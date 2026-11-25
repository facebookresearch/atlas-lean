/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Successors
public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Limits
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Same-order coherent Arrow retract absorption

The original successor and limit constructors produce complete compatible
prefixes by well-order induction from the identity seed. Their common glue
and the actual endpoint colimits construct a transfinite presentation on the
same original order and an Arrow retract with both source maps equal to the
identity.

This is the coherent assembly used in Hovey, Model Categories, Proposition
2.1.16, printed pp.33–34, from given original source-stage Arrow retracts.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.SmallObject.CoherentRetracts

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C) [HasPushouts C]
  (hF : ∀ (j : J) (_hj : ¬IsMax j), P.retracts (F.map (homOfLE (Order.le_succ j))))

variable [HasColimitsOfSize.{w, w} C] [F.IsWellOrderContinuous]

/-- Both actual original lift operations construct the well-order induction data. -/
def prefixInductionData : (prefixSplitFunctor P F).WellOrderInductionData :=
  Functor.WellOrderInductionData.ofExists
    (fun j hj S => by
      obtain ⟨A, B, k, R0, hk⟩ := hF j hj
      exact ⟨PrefixSplitSuccessor.originalSuccessorState P F j S hj k R0 hk,
        PrefixSplitSuccessor.originalSuccessorState_restrict P F j S hj k R0 hk⟩)
    (fun j hj x => ⟨PrefixSplitLimit.limitState P F j x
      (F.isColimitOfIsWellOrderContinuous j hj) hj,
      fun i hi => PrefixSplitLimit.limitState_map P F j x
        (F.isColimitOfIsWellOrderContinuous j hj) hj i hi⟩)

variable [WellFoundedLT J]

/-- The whole compatible family is produced from the actual seed; no complete family is input. -/
def coherentPrefixSection : (prefixSplitFunctor P F).sections :=
  (prefixInductionData P F hF).sectionsMk (PrefixSplit.seed (P := P) (F := F))

/-- The actual constructed family starts at the same original identity seed. -/
theorem coherentPrefixSection_bottom :
    (coherentPrefixSection P F hF).val (Opposite.op (⊥ : J)) =
      PrefixSplit.seed (P := P) (F := F) :=
  (prefixInductionData P F hF).sectionsMk_val_op_bot (PrefixSplit.seed (P := P) (F := F))

end CategoryTheory.SmallObject.CoherentRetracts

namespace CategoryTheory.SmallObject.CoherentRetracts

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (P : MorphismProperty C) {X Y : C} {f : X ⟶ Y}

/-- Every original transfinite composite of stage retracts is a source-fixed
retract of an actual same-index transfinite composite of cobase changes of P.
The complete coherent target diagram is constructed, not supplied. -/
theorem existsCoherentRetractAbsorption (c : P.retracts.TransfiniteCompositionOfShape J f) :
    ∃ (Z : C) (g : X ⟶ Z) (_d : P.pushouts.TransfiniteCompositionOfShape J g)
      (h : RetractArrow f g), h.i.left = 𝟙 X ∧ h.r.left = 𝟙 X := by
  let _ : c.F.IsWellOrderContinuous := c.toTransfiniteCompositionOfShape.isWellOrderContinuous
  let x := coherentPrefixSection P c.F (fun j hj => c.map_mem j hj)
  let D := PrefixSplitGlue.wholeDiagram P c.F x
  let G := D ⋙ SplitObject.targetFunctor
  have hSource : D ⋙ SplitObject.sourceFunctor = c.F := PrefixSplitGlue.wholeDiagram_source P c.F x
  let cF : Cocone (D ⋙ SplitObject.sourceFunctor) :=
    (Cocone.precompose (eqToHom hSource)).obj (Cocone.mk Y c.incl)
  let hF : IsColimit cF :=
    (IsColimit.precomposeHomEquiv (eqToIso hSource) (Cocone.mk Y c.incl)).symm c.isColimit
  let cG : Cocone G := colimit.cocone G
  let hG : IsColimit cG := colimit.isColimit G
  let i := SplitObject.inclusionNatTrans D
  let r := SplitObject.retractionNatTrans D
  let sF : X ⟶ (D ⋙ SplitObject.sourceFunctor).obj ⊥ :=
    c.isoBot.inv ≫ eqToHom (Functor.congr_obj hSource (⊥ : J)).symm
  let sG : X ⟶ G.obj ⊥ := sF ≫ i.app ⊥
  let _ : IsIso (i.app ⊥) := by
    change IsIso (D.obj ⊥).inclusion
    dsimp only [D]
    rw [PrefixSplitGlue.wholeDiagram_bottom]
    change IsIso (𝟙 (c.F.obj ⊥))
    infer_instance
  let _ : IsIso sF := by dsimp only [sF]; infer_instance
  let _ : IsIso sG := by dsimp only [sG]; infer_instance
  have hsR : sG ≫ r.app ⊥ = sF := by
    have hsplit : i.app ⊥ ≫ r.app ⊥ = 𝟙 ((D ⋙ SplitObject.sourceFunctor).obj ⊥) := by
      have h := congrArg (fun t => t.app (⊥ : J)) (SplitObject.inclusion_retraction D)
      exact h
    change (sF ≫ i.app ⊥) ≫ r.app ⊥ = sF
    exact (Category.assoc sF (i.app ⊥) (r.app ⊥)).trans
      ((congrArg (fun t => sF ≫ t) hsplit).trans (Category.comp_id sF))
  let g : X ⟶ cG.pt := sG ≫ cG.ι.app ⊥
  let d : P.pushouts.TransfiniteCompositionOfShape J g :=
    { F := G
      isoBot := (asIso sG).symm
      isWellOrderContinuous := (show G.IsWellOrderContinuous from {
        nonempty_isColimit := PrefixSplitGlue.wholeDiagram_continuous P c.F x })
      incl := cG.ι
      isColimit := hG
      fac := rfl
      map_mem j hj := PrefixSplitGlue.wholeDiagram_map_mem P c.F x j hj }
  let hRaw : RetractArrow (sF ≫ cF.ι.app ⊥) g :=
    retractArrowOfColimitCocones cF cG hF hG i r (SplitObject.inclusion_retraction D)
      (⊥ : J) sF sG rfl hsR
  have hleg : cF.ι.app ⊥ =
      eqToHom (Functor.congr_obj hSource (⊥ : J)) ≫ c.incl.app ⊥ := by
    change (eqToHom hSource).app ⊥ ≫ c.incl.app ⊥ = _
    rw [eqToHom_app]
  have hOriginal : sF ≫ cF.ι.app ⊥ = f := by
    rw [hleg]
    change (c.isoBot.inv ≫ eqToHom (Functor.congr_obj hSource (⊥ : J)).symm) ≫
      (eqToHom (Functor.congr_obj hSource (⊥ : J)) ≫ c.incl.app ⊥) = f
    rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact c.fac
  let h : RetractArrow f g :=
    { i := Arrow.homMk (𝟙 X) hRaw.i.right (by
        change 𝟙 X ≫ g = f ≫ hRaw.i.right
        rw [← hOriginal]
        exact hRaw.i_w)
      r := Arrow.homMk (𝟙 X) hRaw.r.right (by
        change 𝟙 X ≫ f = g ≫ hRaw.r.right
        rw [← hOriginal]
        exact hRaw.r_w)
      retract := by
        ext
        · exact Category.id_comp _
        · exact hRaw.retract_right }
  exact ⟨cG.pt, g, d, h, rfl, rfl⟩


end CategoryTheory.SmallObject.CoherentRetracts
