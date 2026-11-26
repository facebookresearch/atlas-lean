/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Waldhausen.ZeroObjectReplacement
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneWeakFunctorNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The original S1 interval square for arbitrary exact functors

The canonical zero-object representative of an arbitrary exact functor makes
the original S1 postcomposition comparison a literal functor equality. Its
original diagonal comparison components are the unique zero maps and its
off-diagonal component is the existing coefficient identity.

Every original interval pullback retains that entire equality. Restriction
uses the same original weak-category comparison, and the whole chain equation
retains every original object and arrow, with independent source and target
object and morphism universes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Simplicial

universe uC vC uD vD

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D}

omit [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D] in
private theorem stageOneDiagramObj_postcomp_zero_eq
    (h0 : F.obj (0 : C) = (0 : D)) (X : C) (A : Ar 1) :
    F.obj (stageOneDiagramObj C X A) = stageOneDiagramObj D (F.obj X) A := by
  by_cases hA : A.left = A.right
  · rw [stageOneDiagramObj_of_eq C X hA, stageOneDiagramObj_of_eq D (F.obj X) hA]
    exact h0
  · rw [stageOneDiagramObj_of_ne C X hA, stageOneDiagramObj_of_ne D (F.obj X) hA]

set_option backward.isDefEq.respectTransparency false in
private theorem stageOneDiagramPostcompIsoComponent_zero_eq
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D)) (X : C) (A : Ar 1) :
    stageOneDiagramPostcompIsoComponent hF X A =
      eqToIso (stageOneDiagramObj_postcomp_zero_eq h0 X A) := by
  apply Iso.ext
  rw [eqToIso.hom]
  by_cases hA : A.left = A.right
  · have hZ : IsZero ((stageOneDiagram C X ⋙ F).obj A) := by
      change IsZero (F.obj (stageOneDiagramObj C X A))
      rw [stageOneDiagramObj_of_eq C X hA]
      exact hF.map_isZero (isZero_zero C)
    exact hZ.eq_of_src _ _
  · have hInterval := ar1_eq_interval01_of_ne hA
    subst A
    change (stageOneDiagramPostcompIso hF X).hom.app
        (interval (0 : Fin 2) 1 (by decide)) = _
    rw [stageOneDiagramPostcompIso_hom_interval hF X]
    exact (eqToHom_refl _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem stageOneDiagram_postcomp_zero_eq
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D)) (X : C) :
    stageOneDiagram C X ⋙ F = stageOneDiagram D (F.obj X) := by
  apply Functor.ext_of_iso (stageOneDiagramPostcompIso hF X)
    (fun A => stageOneDiagramObj_postcomp_zero_eq h0 X A) ?_
  intro A
  change (stageOneDiagramPostcompIsoComponent hF X A).hom = _
  rw [stageOneDiagramPostcompIsoComponent_zero_eq hF h0 X A, eqToIso.hom]

private theorem stageOneObject_postcomp_zero_eq
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D)) (X : C) :
    (hF.mapStage 1).obj ((stageOne C).obj X) = (stageOne D).obj (F.obj X) := by
  apply ObjectProperty.FullSubcategory.ext
  exact stageOneDiagram_postcomp_zero_eq hF h0 X

set_option backward.isDefEq.respectTransparency false in
private theorem stageOnePostcompStageIso_hom_zero_eq
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D)) (X : C) :
    (stageOnePostcompStageIso hF X).hom =
      eqToHom (stageOneObject_postcomp_zero_eq hF h0 X) := by
  apply (forget D 1).map_injective
  change (stageOneDiagramPostcompIso hF X).hom =
    (forget D 1).map (eqToHom (stageOneObject_postcomp_zero_eq hF h0 X))
  rw [eqToHom_map]
  apply NatTrans.ext
  funext A
  rw [eqToHom_app]
  change (stageOneDiagramPostcompIsoComponent hF X A).hom = _
  rw [stageOneDiagramPostcompIsoComponent_zero_eq hF h0 X A, eqToIso.hom]

/-- The original complete S1 comparison is a functor equality whenever the
given functor has its actual selected-zero equation. -/
theorem stageOnePostcomp_eq_of_obj_zero
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D)) :
    stageOne C ⋙ hF.mapStage 1 = F ⋙ stageOne D := by
  apply Functor.ext_of_iso (stageOnePostcompNatIso hF)
    (fun X => stageOneObject_postcomp_zero_eq hF h0 X) ?_
  intro X
  exact stageOnePostcompStageIso_hom_zero_eq hF h0 X

/-- Every original interval pullback retains the entire original S1 square. -/
theorem stageOneIntervalPostcomp_eq_of_obj_zero
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D))
    {a : SimplexCategory} (t : a ⟶ ⦋1⦌) :
    stageOne C ⋙ reindexStage (C := C) t ⋙ hF.mapStage a.len =
      F ⋙ stageOne D ⋙ reindexStage (C := D) t := by
  rw [hF.mapStage_reindex t]
  change (stageOne C ⋙ hF.mapStage 1) ⋙ reindexStage (C := D) t = _
  rw [stageOnePostcomp_eq_of_obj_zero hF h0]
  rfl

private theorem stageOneWeakObject_postcomp_zero_eq
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D))
    (X : CategoryTheory.Waldhausen.WeakCategory C) :
    (stageOneGeneralWeak C ⋙ hF.mapStageWeak 1).obj X =
      (hF.mapWeakCategory ⋙ stageOneGeneralWeak D).obj X := by
  apply WideSubcategory.ext
  change (hF.mapStage 1).obj ((stageOne C).obj X.obj) =
    (stageOne D).obj (F.obj X.obj)
  exact stageOneObject_postcomp_zero_eq hF h0 X.obj

set_option backward.isDefEq.respectTransparency false in
/-- The same original comparison restricts to an equality on every original
weak object and arrow. -/
theorem stageOnePostcompWeak_eq_of_obj_zero
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D)) :
    stageOneGeneralWeak C ⋙ hF.mapStageWeak 1 =
      hF.mapWeakCategory ⋙ stageOneGeneralWeak D := by
  apply Functor.ext_of_iso (stageOnePostcompWeakNatIso hF)
    (fun X => stageOneWeakObject_postcomp_zero_eq hF h0 X) ?_
  intro X
  apply WideSubcategory.hom_ext
  change (stageOnePostcompWeakIso hF X).hom.hom =
    (wideSubcategoryInclusion (stageWeak D 1)).map
      (eqToHom (stageOneWeakObject_postcomp_zero_eq hF h0 X))
  rw [stageOnePostcompWeakIso_hom, eqToHom_map]
  exact stageOnePostcompStageIso_hom_zero_eq hF h0 X.obj

/-- The original weak interval pullback has the same entire strict square. -/
theorem stageOneWeakIntervalPostcomp_eq_of_obj_zero
    (hF : F.IsWaldhausenExact) (h0 : F.obj (0 : C) = (0 : D))
    {a : SimplexCategory} (t : a ⟶ ⦋1⦌) :
    stageOneGeneralWeak C ⋙ reindexStageWeak C t ⋙ hF.mapStageWeak a.len =
      hF.mapWeakCategory ⋙ stageOneGeneralWeak D ⋙ reindexStageWeak D t := by
  rw [hF.mapStageWeak_reindex t]
  change (stageOneGeneralWeak C ⋙ hF.mapStageWeak 1) ⋙ reindexStageWeak D t = _
  rw [stageOnePostcompWeak_eq_of_obj_zero hF h0]
  rfl

/-- Every arbitrary original exact functor has the whole original S1 square
for its earned canonical zero-object representative. -/
theorem stageOneZeroObjectReplacement_naturality (hF : F.IsWaldhausenExact) :
    stageOne C ⋙ hF.zeroObjectReplacement_isWaldhausenExact.mapStage 1 =
      hF.zeroObjectReplacement ⋙ stageOne D :=
  stageOnePostcomp_eq_of_obj_zero hF.zeroObjectReplacement_isWaldhausenExact
    hF.zeroObjectReplacement_obj_zero

/-- An arbitrary exact functor's representative retains every original
interval simplex and the same full pullback square. -/
theorem stageOneIntervalZeroObjectReplacement_naturality
    (hF : F.IsWaldhausenExact) {a : SimplexCategory} (t : a ⟶ ⦋1⦌) :
    stageOne C ⋙ reindexStage (C := C) t ⋙
        hF.zeroObjectReplacement_isWaldhausenExact.mapStage a.len =
      hF.zeroObjectReplacement ⋙ stageOne D ⋙ reindexStage (C := D) t :=
  stageOneIntervalPostcomp_eq_of_obj_zero hF.zeroObjectReplacement_isWaldhausenExact
    hF.zeroObjectReplacement_obj_zero t

/-- The same arbitrary exact functor has its entire original weak S1 square. -/
theorem stageOneWeakZeroObjectReplacement_naturality (hF : F.IsWaldhausenExact) :
    stageOneGeneralWeak C ⋙ hF.zeroObjectReplacement_isWaldhausenExact.mapStageWeak 1 =
      hF.zeroObjectReplacement_isWaldhausenExact.mapWeakCategory ⋙ stageOneGeneralWeak D :=
  stageOnePostcompWeak_eq_of_obj_zero hF.zeroObjectReplacement_isWaldhausenExact
    hF.zeroObjectReplacement_obj_zero

/-- Every original weak interval pullback retains the arbitrary exact
functor's same canonical representative square. -/
theorem stageOneWeakIntervalZeroObjectReplacement_naturality
    (hF : F.IsWaldhausenExact) {a : SimplexCategory} (t : a ⟶ ⦋1⦌) :
    stageOneGeneralWeak C ⋙ reindexStageWeak C t ⋙
        hF.zeroObjectReplacement_isWaldhausenExact.mapStageWeak a.len =
      hF.zeroObjectReplacement_isWaldhausenExact.mapWeakCategory ⋙
        stageOneGeneralWeak D ⋙ reindexStageWeak D t :=
  stageOneWeakIntervalPostcomp_eq_of_obj_zero hF.zeroObjectReplacement_isWaldhausenExact
    hF.zeroObjectReplacement_obj_zero t

/-- Every complete original weak chain retains all its objects and arrows
under the same source-first representative and original interval pullback. -/
theorem stageOneWeakIntervalZeroObjectReplacement_chain
    (hF : F.IsWaldhausenExact) {a : SimplexCategory} (t : a ⟶ ⦋1⦌)
    {n : ℕ} (q : ComposableArrows (CategoryTheory.Waldhausen.WeakCategory C) n) :
    q ⋙ stageOneGeneralWeak C ⋙ reindexStageWeak C t ⋙
        hF.zeroObjectReplacement_isWaldhausenExact.mapStageWeak a.len =
      (q ⋙ hF.zeroObjectReplacement_isWaldhausenExact.mapWeakCategory) ⋙
        stageOneGeneralWeak D ⋙ reindexStageWeak D t :=
  congrArg (fun H => q ⋙ H) (stageOneWeakIntervalZeroObjectReplacement_naturality hF t)

end CategoryTheory.Waldhausen.SConstruction

end
