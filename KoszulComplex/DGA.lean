import Mathlib

section DGA

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (𝓐 : ℤ → Submodule R A)

class DifferentialGradedAlgebra where
  deriv : Derivation R A A
  deriv_isHomogeneous {n : ℤ} (a : 𝓐 n) : deriv a ∈ 𝓐 (n - 1)

end DGA

section GradedModule

variable {ι A σ : Type*} [DecidableEq ι] [AddMonoid ι] [Semiring A] [SetLike σ A]
  [AddSubmonoidClass σ A] (𝓐 : ι → σ) [GradedRing 𝓐]
  {ιM M σM : Type*} [DecidableEq ιM] [AddAction ι ιM] [AddCommMonoid M] [Module A M]
  [SetLike σM M] [AddSubmonoidClass σM M] (𝓜 : ιM → σM)

class GradedModule extends SetLike.GradedSMul 𝓐 𝓜, DirectSum.Decomposition 𝓜

end GradedModule

section DGM

open DifferentialGradedAlgebra

@[simp]
theorem neg_one_pow_int_add_one (A : Type*) [Ring A] (n : ℤ) :
    (((- 1) ^ (n + 1) : Aˣ) : A) = - ((- 1) ^ n : Aˣ) := by
  norm_cast
  exact (mul_self_zpow (- 1) n).symm.trans (neg_one_mul ((-1) ^ n))

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
  (𝓐 : ℤ → Submodule R A) [GradedAlgebra 𝓐] [DifferentialGradedAlgebra 𝓐]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  (𝓜 : ℤ → Submodule R M)

class DifferentialGradedModule where
  d : M →ₗ[R] M
  d_isHomogeneous {n : ℤ} (m : 𝓜 n) : d m ∈ 𝓜 (n - 1)
  leibniz {n : ℤ} (a : 𝓐 n) (m : M) : d (a • m) = (deriv 𝓐 a) • m + (((- 1) ^ n : Aˣ) * a : A) • d m

end DGM
