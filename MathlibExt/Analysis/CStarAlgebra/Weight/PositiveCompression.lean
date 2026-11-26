/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Weight.FiniteSquareSubmodule
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Finite weight squares and positive compressions

For a nonunital complex C-star algebra and extended positive weight `φ`, each positive `a`
satisfies `a² ≤ ‖a‖ • a`. Thus `φ(a) < ∞` implies `φ(a* a) < ∞`, and the complex span of
finite-weight positive elements lies in `n_φ = {x : φ(x* x) < ∞}`.

For `x ∈ n_φ` and every positive `a`, the compression `x* a x` has finite weight: `x* a x ≤ ‖a‖
• (x* x)`. The algebra may be nonunital and the weight need not be faithful, densely defined or
lower semicontinuous.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarAlgebra.ScalarWeight

universe uA

variable {A : Type uA} [NonUnitalCStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- **Norm bound on a positive square.** In a nonunital complex C-star algebra with its spectral
order, every positive `a` satisfies `a*a ≤ ‖a‖ • a`. -/
theorem positive_mul_self_le_norm_smul (a : PositiveElement A) :
    (a : A) * (a : A) ≤ ‖(a : A)‖ • (a : A) := by
  let r : A := CFC.sqrt (a : A)
  have hstar : star r = r := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a : A))
  have hsquare : r * r = (a : A) := CFC.sqrt_mul_sqrt_self (a : A) a.property
  have hconjugate := CStarAlgebra.star_left_conjugate_le_norm_smul r (a : A)
    (IsSelfAdjoint.of_nonneg a.property)
  have hproduct : star r * (a : A) * r = (a : A) * (a : A) := by
    rw [hstar, ← hsquare]
    simp only [mul_assoc]
  calc
    (a : A) * (a : A) = star r * (a : A) * r := hproduct.symm
    _ ≤ ‖(a : A)‖ • (star r * r) := hconjugate
    _ = ‖(a : A)‖ • (a : A) := by rw [hstar, hsquare]

/-- **Finite positive elements have finite squares.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. if `a ≥ 0` and `φ(a) < ∞`, then
`a ∈ n_φ`; equivalently, `finitePositiveElements φ ⊆ finiteSquareDomain φ`. -/
theorem Weight.finitePositiveElements_subset_finiteSquareDomain (φ : Weight A) :
    φ.finitePositiveElements ⊆ φ.finiteSquareDomain := by
  intro a ha
  obtain ⟨haPositive, haFinite⟩ := ha
  let p : PositiveElement A := ⟨a, haPositive⟩
  have hstar : star a = a := IsSelfAdjoint.of_nonneg haPositive
  have hbound : (leftSquare a : A) ≤
      (positiveSmul (NNReal.mk ‖a‖ (norm_nonneg a)) p : A) := by
    change star a * a ≤ ‖a‖ • a
    rw [hstar]
    exact positive_mul_self_le_norm_smul p
  exact φ.finite_of_le (leftSquare a)
    (positiveSmul (NNReal.mk ‖a‖ (norm_nonneg a)) p) hbound
    (φ.finite_positiveSmul (NNReal.mk ‖a‖ (norm_nonneg a)) p haFinite)

/-- **Finite integration span in the square domain.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. the complex span
`finiteIntegrationDomain φ = span ℂ {a ≥ 0 : φ(a) < ∞}` is contained in the complex submodule
`n_φ`. -/
theorem Weight.finiteIntegrationDomain_le_finiteSquareSubmodule (φ : Weight A) :
    φ.finiteIntegrationDomain ≤ φ.finiteSquareSubmodule := by
  apply Submodule.span_le.mpr
  intro a ha
  exact φ.finitePositiveElements_subset_finiteSquareDomain ha


/-- **Finite weight of a positive compression.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. for `x ∈ n_φ` and any positive `a :
A`, `φ(x* a x) < ∞`, by `x* a x ≤ ‖a‖ • (x* x)`. -/
theorem Weight.value_positiveConjugate_lt_top (φ : Weight A) (x : φ.finiteSquareSubmodule)
    (a : PositiveElement A) :
    φ.value ⟨star (x : A) * (a : A) * (x : A),
      star_left_conjugate_nonneg a.property (x : A)⟩ < ⊤ := by
  let r : NNReal := NNReal.mk ‖(a : A)‖ (norm_nonneg (a : A))
  have hbound : star (x : A) * (a : A) * (x : A) ≤
      (positiveSmul r (leftSquare (x : A)) : A) := by
    change star (x : A) * (a : A) * (x : A) ≤ ‖(a : A)‖ • (star (x : A) * (x : A))
    exact CStarAlgebra.star_left_conjugate_le_norm_smul (x : A) (a : A)
      (IsSelfAdjoint.of_nonneg a.property)
  exact φ.finite_of_le _ (positiveSmul r (leftSquare (x : A))) hbound
    (φ.finite_positiveSmul r (leftSquare (x : A)) x.property)


end CStarAlgebra.ScalarWeight

end
