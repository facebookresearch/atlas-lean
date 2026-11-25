/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.SmallObject.Image

/-!
# Restricting actual free generators while preserving an evaluated isomorphism

An omitted degree is characterized by isomorphisms of its original evaluation.
The actual restricted small-object left factor has that property, and a retract
of that same factor gives the exact ordinary-left-class intersection.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w vC uC vD uD

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.PositiveLevelModel

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (P Q : MorphismProperty D) (E : D ⥤ C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] [P.IsCardinalForSmallObjectArgument κ]
  [PreservesColimitsOfSize.{w, w} E] [PreservesColimitsOfShape κ.ord.ToType E]
  [PreservesWellOrderContinuousOfShape κ.ord.ToType E]

include κ in
/-- The actual free-cell/retract history preserves the original evaluated isomorphisms. -/
theorem restrictedGeneratedLeft_le_isomorphisms
    (hZero : P ≤ (isomorphisms C).inverseImage E) :
    P.rlp.llp ≤ (isomorphisms C).inverseImage E := by
  let _ : (isomorphisms C).IsStableUnderCoproducts.{w} := {}
  exact rlp_llp_le_inverseImage_of_cardinal_closure P (isomorphisms C) E κ hZero

include κ in
/-- The complete restricted left class is precisely the original ordinary left class and evaluated
isomorphisms. -/
theorem restrictedGeneratedLeft_eq
    (hPQ : P ≤ Q) (hZero : P ≤ (isomorphisms C).inverseImage E)
    (hRight : P.rlp ⊓ (isomorphisms C).inverseImage E ≤ Q.rlp) :
    P.rlp.llp = Q.rlp.llp ⊓ (isomorphisms C).inverseImage E := by
  apply le_antisymm
  · exact le_inf (antitone_llp (antitone_rlp hPQ))
      (restrictedGeneratedLeft_le_isomorphisms P E κ hZero)
  · intro X Y f hf
    let i := SmallObject.ιObj P κ f
    let p := SmallObject.πObj P κ f
    let _ : IsIso (E.map i) :=
      restrictedGeneratedLeft_le_isomorphisms P E κ hZero i (SmallObject.llp_rlp_ιObj P κ f)
    let _ : IsIso (E.map f) := hf.2
    have hFac : E.map i ≫ E.map p = E.map f := by
      rw [← Functor.map_comp, SmallObject.ιObj_πObj]
    let _ : IsIso (E.map p) := IsIso.of_isIso_fac_left hFac
    have hp : Q.rlp p := hRight p
        ⟨SmallObject.rlp_πObj P κ f, (show IsIso (E.map p) from inferInstance)⟩
    let _ : HasLiftingProperty f p := hf.1 p hp
    exact P.rlp.llp.of_retract (RetractArrow.ofLeftLiftingProperty (SmallObject.ιObj_πObj P κ f))
      (SmallObject.llp_rlp_ιObj P κ f)

end HomotopicalAlgebra.PositiveLevelModel
