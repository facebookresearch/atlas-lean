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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.CoordinateOrthogonality

/-!
# Tensor components at a fixed sum degree

The tensor inclusion is transported to a fixed sum degree, and the
projection specializes `tensorCellProjection`. The selected pair retracts;
a different first degree gives zero composite. Both maps use the tensor
total and its component projections.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v w x y

namespace CochainComplex.ModuleTensor

variable (R : Type u) [CommRing R]
  (P : CochainComplex (ModuleCat.{v} R) ℤ) (Q : CochainComplex (ModuleCat.{w} R) ℤ)

/-- The original native pair with first degree i includes into its actual displayed total degree n. -/
def degreeComponentInclusionAt (n i : ℤ) :
    ModuleCat.tensorObjAt R (P.X i) (Q.X (n - i)) ⟶ (complexAt R P Q).X n :=
  componentInclusionAt R P Q i (n - i) ≫
    ((complexAt R P Q).XIsoOfEq (show i + (n - i) = n by omega)).hom

/-- Compatibility specialization of the canonical arbitrary-degree projection to first degree i. -/
abbrev degreeComponentProjectionAt (n i : ℤ) :
    (complexAt R P Q).X n ⟶ ModuleCat.tensorObjAt R (P.X i) (Q.X (n - i)) :=
  tensorCellProjection R P Q i (n - i) n

/-- Fixed-degree placement is exactly the original native coproduct inclusion. -/
theorem degreeComponentInclusionAt_eq_native (n i : ℤ) :
    degreeComponentInclusionAt R P Q n i =
      HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        i (n - i) n (show i + (n - i) = n by omega) :=
  nativeComponentInclusion_cast R P Q i (n - i) (i + (n - i)) n rfl (by omega)

/-- The original fixed-degree component projection retracts its own native inclusion. -/
theorem degreeComponentInclusionAt_projectionAt (n i : ℤ) :
    degreeComponentInclusionAt R P Q n i ≫ degreeComponentProjectionAt R P Q n i =
      𝟙 (ModuleCat.tensorObjAt R (P.X i) (Q.X (n - i))) := by
  rw [degreeComponentInclusionAt_eq_native]
  exact tensorCellProjection_ι R P Q i (n - i) n (by omega)

/-- A different native first degree is killed by the canonical fixed-degree projection. -/
theorem degreeComponentInclusionAt_other_projectionAt (n p i : ℤ) (hpi : p ≠ i) :
    degreeComponentInclusionAt R P Q n p ≫ degreeComponentProjectionAt R P Q n i = 0 := by
  rw [degreeComponentInclusionAt_eq_native]
  exact tensorCellProjection_ι_eq_zero R P Q i (n - i) n p (n - p) (by omega) (Or.inl hpi)

end CochainComplex.ModuleTensor
