/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Basic

/-!
# Actual small object factor values, attachments, and mapped cofans

These are the original source small object constructions at the supplied
genuine eligible cardinal. Both level model branches instantiate them at
their earned common generator rank. Every cell label, attaching map, cofan,
pushout, stage, endpoint and Arrow square is retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u vD uD

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.PositiveLevelModel.ActualSourceCells

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [P.IsCardinalForSmallObjectArgument κ]

/-- The actual full relative cell history of the original small object left map. -/
abbrev history (f : Arrow C) := SmallObject.relativeCellComplexιObj P κ f.hom

/-- The actual intermediate object is the original small object output. -/
theorem factor_obj (f : Arrow C) :
    (SmallObject.functorialFactorizationData P κ).Z.obj f = SmallObject.obj P κ f.hom := rfl

/-- Every original Arrow square induces the same original small object map. -/
theorem factor_map {f g : Arrow C} (s : f ⟶ g) :
    (SmallObject.functorialFactorizationData P κ).Z.map s = SmallObject.objMap P κ s := rfl

/-- The actual left factor retains its original small object map. -/
theorem factor_i (f : Arrow C) :
    (SmallObject.functorialFactorizationData P κ).i.app f = SmallObject.ιObj P κ f.hom := rfl

/-- The actual right factor retains its original small object map. -/
theorem factor_p (f : Arrow C) :
    (SmallObject.functorialFactorizationData P κ).p.app f = SmallObject.πObj P κ f.hom := rfl

/-- The bottom isomorphism and actual colimit inclusion recover the same original left factor. -/
theorem history_bottom (f : Arrow C) :
    (history P κ f).isoBot.inv ≫ (history P κ f).incl.app ⊥ =
      (SmallObject.functorialFactorizationData P κ).i.app f :=
  (history P κ f).fac

/-- The whole actual stage diagram has the original factor object as its colimit. -/
abbrev historyColimit (f : Arrow C) := (history P κ f).isColimit

/-- Every original successor stage retains its full actual source cell attachment. -/
abbrev attachment (f : Arrow C) (j : κ.ord.ToType) (hj : ¬ IsMax j) :=
  (history P κ f).attachCells j hj

/-- The complete source cofan identifies the original generator map and target injection. -/
theorem attachment_cofan_word (f : Arrow C) (j : κ.ord.ToType) (hj : ¬ IsMax j)
    (a : (attachment P κ f j hj).ι) :
    (attachment P κ f j hj).cofan₁.inj a ≫ (attachment P κ f j hj).m =
      P.homFamily ((attachment P κ f j hj).π a) ≫
        (attachment P κ f j hj).cofan₂.inj a :=
  (attachment P κ f j hj).hm a

/-- The actual attaching square retains both whole coproduct maps and the original stage transition.
-/
abbrev attachmentPushout (f : Arrow C) (j : κ.ord.ToType) (hj : ¬ IsMax j) :=
  (attachment P κ f j hj).isPushout

variable {D : Type uD} [Category.{vD} D] (E : C ⥤ D)
  [PreservesColimitsOfSize.{w, w} E]

/-- The actual mapped source cofan retains every original source injection. -/
abbrev mappedSourceCofan (f : Arrow C) (j : κ.ord.ToType) (hj : ¬ IsMax j) :=
  E.mapCocone (attachment P κ f j hj).cofan₁

/-- The actual mapped target cofan retains every original target injection. -/
abbrev mappedTargetCofan (f : Arrow C) (j : κ.ord.ToType) (hj : ¬ IsMax j) :=
  E.mapCocone (attachment P κ f j hj).cofan₂

/-- The mapped original source cofan is an actual colimit of that unchanged mapped diagram. -/
def mappedSourceCofanIsColimit (f : Arrow C) (j : κ.ord.ToType) (hj : ¬ IsMax j) :
    IsColimit (mappedSourceCofan P κ E f j hj) :=
  isColimitOfPreserves E (attachment P κ f j hj).isColimit₁

/-- The mapped original target cofan is likewise the actual colimit. -/
def mappedTargetCofanIsColimit (f : Arrow C) (j : κ.ord.ToType) (hj : ¬ IsMax j) :
    IsColimit (mappedTargetCofan P κ E f j hj) :=
  isColimitOfPreserves E (attachment P κ f j hj).isColimit₂

omit [PreservesColimitsOfSize.{w, w} E] in
/-- Every original mapped cofan equation retains the full original generator and coproduct map. -/
theorem mapped_attachment_cofan_word (f : Arrow C) (j : κ.ord.ToType) (hj : ¬ IsMax j)
    (a : (attachment P κ f j hj).ι) :
    E.map ((attachment P κ f j hj).cofan₁.inj a) ≫ E.map (attachment P κ f j hj).m =
      E.map (P.homFamily ((attachment P κ f j hj).π a)) ≫
        E.map ((attachment P κ f j hj).cofan₂.inj a) := by
  simpa only [Functor.map_comp] using congrArg E.map (attachment_cofan_word P κ f j hj a)

variable [PreservesColimitsOfShape κ.ord.ToType E]
  [PreservesWellOrderContinuousOfShape κ.ord.ToType E]

/-- The entire original mapped history, including its bottom, colimit, and inclusion maps. -/
abbrev mappedHistory (f : Arrow C) := (history P κ f).toTransfiniteCompositionOfShape.map E

/-- Every actual mapped stage transition is an isomorphism when every original generator maps to
one. -/
theorem mapped_transition_isIso (hP : P ≤ (isomorphisms D).inverseImage E)
    (f : Arrow C) {a b : κ.ord.ToType} (s : a ⟶ b) :
    IsIso (E.map ((history P κ f).F.map s)) := by
  let _ : (isomorphisms D).IsStableUnderCoproducts.{w} := {}
  exact (history P κ f).map_map_mem_of_le E P (isomorphisms D) hP s

omit [PreservesColimitsOfSize.{w, w} E] in
/-- The mapped bottom and colimit inclusion recover the actual original evaluated left factor. -/
theorem mapped_history_bottom (f : Arrow C) :
    (mappedHistory P κ E f).isoBot.inv ≫ (mappedHistory P κ E f).incl.app ⊥ =
      E.map ((SmallObject.functorialFactorizationData P κ).i.app f) :=
  (mappedHistory P κ E f).fac

end HomotopicalAlgebra.PositiveLevelModel.ActualSourceCells
