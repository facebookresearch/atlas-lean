/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence

/-!
# Natural isomorphisms retain the original derived replacement maps

The native derived-functor natural-isomorphism construction is reused.
Its maps are identified with the original chosen-Q and chosen-R lifts,
including the complete comparison squares. These characteristic equations
allow source Kan/free isomorphisms to be derived without changing their
maps or supplying a derived comparison as an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uC uD vC vD

open CategoryTheory
open CategoryTheory.Functor

namespace HomotopicalAlgebra.DerivedFunctorCoherence

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L L' : C ⥤ D} {R R' : D ⥤ C}
  (adj : L ⊣ R) [adj.IsQuillenAdjunction]
  (adj' : L' ⊣ R') [adj'.IsQuillenAdjunction]

local instance chosenLeftDerived (q : GeneratedFunctorialReplacements.Data (C := C)) :
    (left adj q).IsLeftDerivedFunctor (leftComparison adj q) (weakEquivalences C) :=
  leftIsDerived adj q

local instance chosenRightDerived (r : GeneratedFunctorialReplacements.Data (C := D)) :
    (right adj r).IsRightDerivedFunctor (rightComparison adj r) (weakEquivalences D) :=
  rightIsDerived adj r

/-- The original Q lift has the full native left-derived comparison square. -/
theorem leftNat_fac (q : GeneratedFunctorialReplacements.Data (C := C)) (τ : L ⟶ L') :
    whiskerLeft (projection C) (leftNat adj adj' q τ) ≫ leftComparison adj' q =
      leftComparison adj q ≫ whiskerRight τ (projection D) := by
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    leftNat_app, leftComparison_app]
  change (projection D).map (τ.app (q.Q.obj X)) ≫
      (projection D).map (L'.map (q.q.app X)) =
    (projection D).map (L.map (q.q.app X)) ≫ (projection D).map (τ.app X)
  simpa only [Functor.map_comp, Functor.id_obj] using
    congrArg (projection D).map (τ.naturality (q.q.app X)).symm

/-- The native left-derived transformation is the same actual Q-map lift. -/
theorem leftNat_eq_native (q : GeneratedFunctorialReplacements.Data (C := C))
    (τ : L ⟶ L') :
    leftNat adj adj' q τ =
      Functor.leftDerivedNatTrans (left adj q) (left adj' q)
        (leftComparison adj q) (leftComparison adj' q) (weakEquivalences C)
        (whiskerRight τ (projection D)) := by
  apply Functor.leftDerived_ext (left adj' q) (leftComparison adj' q)
    (weakEquivalences C)
  exact (leftNat_fac adj adj' q τ).trans
    (Functor.leftDerivedNatTrans_fac (left adj q) (left adj' q)
      (leftComparison adj q) (leftComparison adj' q) (weakEquivalences C)
      (whiskerRight τ (projection D))).symm

/-- Reuse the native derived isomorphism on the complete original left functors. -/
def leftNatIso (q : GeneratedFunctorialReplacements.Data (C := C)) (e : L ≅ L') :
    left adj q ≅ left adj' q := by
  exact Functor.leftDerivedNatIso (left adj q) (left adj' q)
    (leftComparison adj q) (leftComparison adj' q) (weakEquivalences C)
    (isoWhiskerRight e (projection D))

/-- The whole forward isomorphism retains the original Q transformation. -/
theorem leftNatIso_hom (q : GeneratedFunctorialReplacements.Data (C := C)) (e : L ≅ L') :
    (leftNatIso adj adj' q e).hom = leftNat adj adj' q e.hom :=
  (leftNat_eq_native adj adj' q e.hom).symm

/-- The whole inverse retains the same Q and the original inverse transformation. -/
theorem leftNatIso_inv (q : GeneratedFunctorialReplacements.Data (C := C)) (e : L ≅ L') :
    (leftNatIso adj adj' q e).inv = leftNat adj' adj q e.inv :=
  (leftNat_eq_native adj' adj q e.inv).symm

/-- Every projected coefficient of the forward comparison is the actual map on Q. -/
theorem leftNatIso_hom_app (q : GeneratedFunctorialReplacements.Data (C := C))
    (e : L ≅ L') (X : C) :
    (leftNatIso adj adj' q e).hom.app ((projection C).obj X) =
      (projection D).map (e.hom.app (q.Q.obj X)) := by
  rw [leftNatIso_hom, leftNat_app]

/-- Every projected inverse coefficient is the original inverse map on the same Q. -/
theorem leftNatIso_inv_app (q : GeneratedFunctorialReplacements.Data (C := C))
    (e : L ≅ L') (X : C) :
    (leftNatIso adj adj' q e).inv.app ((projection C).obj X) =
      (projection D).map (e.inv.app (q.Q.obj X)) := by
  rw [leftNatIso_inv, leftNat_app]

/-- The original R lift has the full native right-derived comparison square. -/
theorem rightNat_fac (r : GeneratedFunctorialReplacements.Data (C := D)) (τ : R ⟶ R') :
    rightComparison adj r ≫ whiskerLeft (projection D) (rightNat adj adj' r τ) =
      whiskerRight τ (projection C) ≫ rightComparison adj' r := by
  ext Y
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightNat_app, rightComparison_app]
  change (projection C).map (R.map (r.r.app Y)) ≫
      (projection C).map (τ.app (r.R.obj Y)) =
    (projection C).map (τ.app Y) ≫ (projection C).map (R'.map (r.r.app Y))
  simpa only [Functor.map_comp, Functor.id_obj] using
    congrArg (projection C).map (τ.naturality (r.r.app Y))

/-- The native right-derived transformation retains the same actual R-map lift. -/
theorem rightNat_eq_native (r : GeneratedFunctorialReplacements.Data (C := D))
    (τ : R ⟶ R') :
    rightNat adj adj' r τ =
      Functor.rightDerivedNatTrans (right adj r) (right adj' r)
        (rightComparison adj r) (rightComparison adj' r) (weakEquivalences D)
        (whiskerRight τ (projection C)) := by
  apply Functor.rightDerived_ext (right adj r) (rightComparison adj r)
    (weakEquivalences D)
  exact (rightNat_fac adj adj' r τ).trans
    (Functor.rightDerivedNatTrans_fac (right adj r) (right adj' r)
      (rightComparison adj r) (rightComparison adj' r) (weakEquivalences D)
      (whiskerRight τ (projection C))).symm

/-- Reuse the native right-derived isomorphism with its actual chosen R maps. -/
def rightNatIso (r : GeneratedFunctorialReplacements.Data (C := D)) (e : R ≅ R') :
    right adj r ≅ right adj' r := by
  exact Functor.rightDerivedNatIso (right adj r) (right adj' r)
    (rightComparison adj r) (rightComparison adj' r) (weakEquivalences D)
    (isoWhiskerRight e (projection C))

/-- The forward right comparison is the original R-image transformation. -/
theorem rightNatIso_hom (r : GeneratedFunctorialReplacements.Data (C := D)) (e : R ≅ R') :
    (rightNatIso adj adj' r e).hom = rightNat adj adj' r e.hom :=
  (rightNat_eq_native adj adj' r e.hom).symm

/-- The inverse right comparison retains the actual inverse map on the same R. -/
theorem rightNatIso_inv (r : GeneratedFunctorialReplacements.Data (C := D)) (e : R ≅ R') :
    (rightNatIso adj adj' r e).inv = rightNat adj' adj r e.inv :=
  (rightNat_eq_native adj' adj r e.inv).symm

/-- All original projected forward coefficients use the same fibrant replacement. -/
theorem rightNatIso_hom_app (r : GeneratedFunctorialReplacements.Data (C := D))
    (e : R ≅ R') (Y : D) :
    (rightNatIso adj adj' r e).hom.app ((projection D).obj Y) =
      (projection C).map (e.hom.app (r.R.obj Y)) := by
  rw [rightNatIso_hom, rightNat_app]

/-- All original projected inverse coefficients keep the same replacement and inverse. -/
theorem rightNatIso_inv_app (r : GeneratedFunctorialReplacements.Data (C := D))
    (e : R ≅ R') (Y : D) :
    (rightNatIso adj adj' r e).inv.app ((projection D).obj Y) =
      (projection C).map (e.inv.app (r.R.obj Y)) := by
  rw [rightNatIso_inv, rightNat_app]

end HomotopicalAlgebra.DerivedFunctorCoherence
