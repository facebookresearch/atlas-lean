/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.TotalComparisonBoxDivision
import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyAdjunction

/-!
# The actual first–total composite

The two named adjunctions compose on the original Joyal carrier. Their left
composite is naturally the identity by the original box-zero comparison and
the actual k-zero comparison. The right comparison is its forced inverse-left
mate, retaining the original units, counits and Hom equivalences.

This is the raw composite argument in the proof of Joyal–Tierney Theorem 4.12.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SimplicialSpace.TotalSpace

/-- The actual named first left adjoint followed by the actual named total left adjoint. -/
abbrev firstTotalLeft : JoyalSSet.{u} ⥤ JoyalSSet.{u} := comparisonLeft.{u} ⋙ left.{u}

/-- The actual named total right adjoint followed by the original named zeroth row. -/
abbrev totalFirstRight : JoyalSSet.{u} ⥤ JoyalSSet.{u} := right.{u} ⋙ comparisonRight.{u}

/-- The original two adjunctions compose on the same designated Joyal carrier. -/
def firstTotalCompositeAdjunction : firstTotalLeft.{u} ⊣ totalFirstRight.{u} :=
  comparisonAdjunction.{u}.comp adjunction.{u}

private def deltaZeroUnitIso : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
  SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit

private def innerTensorUnitIso : innerTensor (𝟙_ SSet.{u}) ≅ 𝟭 SimplicialSpace.{u} := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · apply InducedCategory.isoMk
    refine NatIso.ofComponents (fun d => ρ_ (X.diagram.obj d)) ?_
    intro d e f
    exact (rightUnitorNatIso SSet.{u}).hom.naturality ((X.diagram.map f))
  · intro X Y f
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext d
    change (f.hom.app d ▷ 𝟙_ SSet.{u}) ≫ (ρ_ (Y.diagram.obj d)).hom =
      (ρ_ (X.diagram.obj d)).hom ≫ f.hom.app d
    exact (rightUnitorNatIso SSet.{u}).hom.naturality (f.hom.app d)

private def boxZeroDiscreteIso : boxProduct.{u}.flip.obj (Δ[0] : SSet.{u}) ≅
    discreteInnerFunctor.{u} :=
  boxProduct.flip.mapIso deltaZeroUnitIso.{u} ≪≫
    Functor.isoWhiskerLeft discreteInnerFunctor.{u} innerTensorUnitIso.{u} ≪≫
      Functor.rightUnitor discreteInnerFunctor.{u}

/-- The original first-projection functor is the box with the original zero simplex. -/
def comparisonLeftBoxZeroIso : comparisonLeft.{u} ≅
    JoyalSSet.forget.{u} ⋙ boxProduct.{u}.flip.obj (Δ[0] : SSet.{u}) :=
  Functor.associator JoyalSSet.forget SSet.simplicialSpaceDiscrete ofSimplicialObject ≪≫
    Functor.isoWhiskerLeft JoyalSSet.forget boxZeroDiscreteIso.symm

private def productKZeroIso : tensorRight (SSet.FreeGroupoidSimplex.kFunctor.obj
    (Δ[0] : SSet.{u})) ≅ 𝟭 SSet.{u} :=
  (curriedTensor SSet.{u}).flip.mapIso
    (SSet.FreeGroupoidSimplex.kZeroIso.{u} ≪≫ deltaZeroUnitIso.{u}) ≪≫
      rightUnitorNatIso SSet.{u}

/-- The original total image of the original first projection is the same Joyal object. -/
def firstTotalLeftIso : firstTotalLeft.{u} ≅ 𝟭 JoyalSSet.{u} :=
  Functor.isoWhiskerRight comparisonLeftBoxZeroIso.{u} left.{u} ≪≫
    Functor.associator JoyalSSet.forget
      (boxProduct.{u}.flip.obj (Δ[0] : SSet.{u})) left.{u} ≪≫
    Functor.isoWhiskerLeft JoyalSSet.forget
      (((Functor.flipping (C := SSet.{u}) (D := SSet.{u}) (E := JoyalSSet.{u})).functor.mapIso
        boxProductIso.{u}).app (Δ[0] : SSet.{u})) ≪≫
    Functor.isoWhiskerLeft JoyalSSet.forget
      (Functor.isoWhiskerRight productKZeroIso.{u} JoyalSSet.ofSSet.{u} ≪≫
        Functor.leftUnitor JoyalSSet.ofSSet.{u}) ≪≫
    JoyalSSet.equivalenceSSet.{u}.unitIso.symm

/-- The matching original right composite is the forced mate of the same inverse left iso. -/
def totalFirstRightIso : totalFirstRight.{u} ≅ 𝟭 JoyalSSet.{u} :=
  conjugateIsoEquiv firstTotalCompositeAdjunction.{u} Adjunction.id firstTotalLeftIso.{u}.symm

/-- The left comparison preserves every original Joyal map. -/
theorem firstTotalLeftIso_naturality {A B : JoyalSSet.{u}} (f : A ⟶ B) :
    left.map (comparisonLeft.map f) ≫ firstTotalLeftIso.hom.app B =
      firstTotalLeftIso.hom.app A ≫ f := firstTotalLeftIso.hom.naturality f

/-- The inverse left comparison preserves every original Joyal map. -/
theorem firstTotalLeftIso_inv_naturality {A B : JoyalSSet.{u}} (f : A ⟶ B) :
    f ≫ firstTotalLeftIso.inv.app B =
      firstTotalLeftIso.inv.app A ≫ left.map (comparisonLeft.map f) :=
  firstTotalLeftIso.inv.naturality f

/-- The right mate preserves every original Joyal map. -/
theorem totalFirstRightIso_naturality {Q Q' : JoyalSSet.{u}} (q : Q ⟶ Q') :
    comparisonRight.map (right.map q) ≫ totalFirstRightIso.hom.app Q' =
      totalFirstRightIso.hom.app Q ≫ q := totalFirstRightIso.hom.naturality q

/-- The inverse right mate preserves every original Joyal map. -/
theorem totalFirstRightIso_inv_naturality {Q Q' : JoyalSSet.{u}} (q : Q ⟶ Q') :
    q ≫ totalFirstRightIso.inv.app Q' =
      totalFirstRightIso.inv.app Q ≫ comparisonRight.map (right.map q) :=
  totalFirstRightIso.inv.naturality q

/-- The composite unit retains the literal original first and total units. -/
theorem firstTotalCompositeAdjunction_unit (A : JoyalSSet.{u}) :
    firstTotalCompositeAdjunction.unit.app A = comparisonAdjunction.unit.app A ≫
      comparisonRight.map (adjunction.unit.app (comparisonLeft.obj A)) :=
  Adjunction.comp_unit_app comparisonAdjunction adjunction A

/-- The composite counit retains the literal original first and total counits. -/
theorem firstTotalCompositeAdjunction_counit (Q : JoyalSSet.{u}) :
    firstTotalCompositeAdjunction.counit.app Q =
      left.map (comparisonAdjunction.counit.app (right.obj Q)) ≫ adjunction.counit.app Q :=
  Adjunction.comp_counit_app comparisonAdjunction adjunction Q

/-- The same inverse-left mate identifies the actual composite unit. -/
theorem firstTotalComposite_unit_mate (A : JoyalSSet.{u}) :
    firstTotalCompositeAdjunction.unit.app A ≫ totalFirstRightIso.hom.app (firstTotalLeft.obj A) =
      firstTotalLeftIso.inv.app A := by
  have h := unit_conjugateEquiv firstTotalCompositeAdjunction.{u} Adjunction.id
    firstTotalLeftIso.inv A
  simpa only [totalFirstRightIso, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    Adjunction.id_unit, NatTrans.id_app, CategoryTheory.Functor.id_map,
    Category.id_comp] using h

/-- The same inverse-left mate identifies the actual composite counit. -/
theorem firstTotalComposite_counit_mate (Q : JoyalSSet.{u}) :
    firstTotalLeftIso.inv.app (totalFirstRight.obj Q) ≫ firstTotalCompositeAdjunction.counit.app Q =
      totalFirstRightIso.hom.app Q := by
  have h := conjugateEquiv_counit firstTotalCompositeAdjunction.{u} Adjunction.id
    firstTotalLeftIso.inv Q
  simpa only [totalFirstRightIso, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    Adjunction.id_counit, NatTrans.id_app, CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj,
    Category.comp_id] using h.symm

/-- The inverse right mate keeps the original composite unit and original left map. -/
theorem firstTotalComposite_inv_unit_mate (A : JoyalSSet.{u}) :
    totalFirstRightIso.inv.app A = firstTotalCompositeAdjunction.unit.app A ≫
      totalFirstRight.map (firstTotalLeftIso.hom.app A) := by
  have h := unit_conjugateEquiv Adjunction.id firstTotalCompositeAdjunction.{u}
    firstTotalLeftIso.hom A
  simpa only [totalFirstRightIso, conjugateIsoEquiv_apply_inv, Iso.symm_inv,
    Adjunction.id_unit, NatTrans.id_app, CategoryTheory.Functor.id_obj, Category.id_comp] using h

/-- The inverse right mate keeps the original composite counit and original left map. -/
theorem firstTotalComposite_inv_counit_mate (Q : JoyalSSet.{u}) :
    firstTotalLeft.map (totalFirstRightIso.inv.app Q) ≫ firstTotalCompositeAdjunction.counit.app Q =
      firstTotalLeftIso.hom.app Q := by
  have h := conjugateEquiv_counit Adjunction.id firstTotalCompositeAdjunction.{u}
    firstTotalLeftIso.hom Q
  simpa only [totalFirstRightIso, conjugateIsoEquiv_apply_inv, Iso.symm_inv,
    Adjunction.id_counit, NatTrans.id_app, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj, Category.comp_id] using h

/-- Transposition commutes with both original comparisons for every original map. -/
theorem firstTotalComposite_homEquiv (A Q : JoyalSSet.{u}) (f : firstTotalLeft.obj A ⟶ Q) :
    firstTotalCompositeAdjunction.homEquiv A Q f ≫ totalFirstRightIso.hom.app Q =
      firstTotalLeftIso.inv.app A ≫ f := by
  rw [firstTotalCompositeAdjunction.homEquiv_unit, Category.assoc,
    totalFirstRightIso.hom.naturality, ← Category.assoc, firstTotalComposite_unit_mate]
  rfl

/-- Inverse transposition commutes with the same original comparisons. -/
theorem firstTotalComposite_homEquiv_symm (A Q : JoyalSSet.{u}) (g : A ⟶ totalFirstRight.obj Q) :
    (firstTotalCompositeAdjunction.homEquiv A Q).symm g =
      firstTotalLeftIso.hom.app A ≫ g ≫ totalFirstRightIso.hom.app Q := by
  have h := firstTotalComposite_homEquiv A Q
    ((firstTotalCompositeAdjunction.homEquiv A Q).symm g)
  rw [Equiv.apply_symm_apply] at h
  exact (Iso.inv_comp_eq (firstTotalLeftIso.app A)).1 h.symm

/-- The forward adjunct is literally the original total adjunct followed by the first adjunct. -/
theorem firstTotalComposite_homEquiv_two_stage (A Q : JoyalSSet.{u})
    (f : left.obj (comparisonLeft.obj A) ⟶ Q) :
    comparisonAdjunction.homEquiv A (right.obj Q)
        (adjunction.homEquiv (comparisonLeft.obj A) Q f) ≫ totalFirstRightIso.hom.app Q =
      firstTotalLeftIso.inv.app A ≫ f :=
  firstTotalComposite_homEquiv A Q f

/-- The inverse adjunct retains both actual named inverse Hom equivalences. -/
theorem firstTotalComposite_homEquiv_two_stage_symm (A Q : JoyalSSet.{u})
    (g : A ⟶ comparisonRight.obj (right.obj Q)) :
    (adjunction.homEquiv (comparisonLeft.obj A) Q).symm
        ((comparisonAdjunction.homEquiv A (right.obj Q)).symm g) =
      firstTotalLeftIso.hom.app A ≫ g ≫ totalFirstRightIso.hom.app Q := by
  simpa only [firstTotalCompositeAdjunction, Adjunction.comp_homEquiv,
    Equiv.symm_trans_apply] using firstTotalComposite_homEquiv_symm A Q g

end SimplicialSpace.TotalSpace
