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
# Finite positive squares and positive compression values for scalar weights

The original global weight on a possibly nonunital C-star algebra gives
finite square values for its finite-positive elements. Their complex span
lies in the exact finite-square module. Every positive compression by a
finite-square element has finite weight, from the canonical conjugation
norm bound and the original weight laws.

These generic APIs use only the original algebra, positive domain and
scalar weight. Concrete von Neumann topology and representation suppliers
consume them through this neutral owner.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarAlgebra.ScalarWeight

universe uA

variable {A : Type uA} [NonUnitalCStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- The original positive square is bounded by the original positive norm multiple. -/
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

/-- Original finite-positive elements belong to the same literal finite-square domain. -/
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

/-- The original finite-positive integration span lies in the actual finite-square module. -/
theorem Weight.finiteIntegrationDomain_le_finiteSquareSubmodule (φ : Weight A) :
    φ.finiteIntegrationDomain ≤ φ.finiteSquareSubmodule := by
  apply Submodule.span_le.mpr
  intro a ha
  exact φ.finitePositiveElements_subset_finiteSquareDomain ha


/-- A literal finite-square element gives finite weight to every original positive compression. -/
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
