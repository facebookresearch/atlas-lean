/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Codex
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeIncrement
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.BoundedCellTreeCompactRetract
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.IdempotentCoequalizerSplit
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalIdempotentLowerSupport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeWeakSaturation

/-!
# Compact charts for actual split images of bounded cell differences

The step is the actual map of the original chosen lower-support coequalizers.
Its Arrow retract is constructed from the original inclusions and projections.
The literal difference cell tree and the existing compact Arrow producer give
the scalar chart over the same split-image objects, with no completed history,
compact chart, target replacement or scalar-class outcome as input.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.BoundedDifferenceSplitChart

open Limits

variable {C : Type u} [Category.{v} C]
  {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (B D : LowerSet P) (hBD : B ≤ D)
  (eB : L.obj B ⟶ L.obj B) (eD : L.obj D ⟶ L.obj D)
  (heB : eB ≫ eB = eB) (heD : eD ≫ eD = eD)
  (hcomm : eB ≫ L.map hBD = L.map hBD ≫ eD)
  [HasCoequalizer eB (𝟙 (L.obj B))] [HasCoequalizer eD (𝟙 (L.obj D))]

/-- The same actual coequalizer map used by the original support splitting. -/
abbrev step : IdempotentCoequalizerSplit.obj eB ⟶ IdempotentCoequalizerSplit.obj eD :=
  IdempotentCoequalizerSplit.map eB eD (L.map hBD) hcomm

/-- Both original lower-support splitting squares give the actual whole Arrow retract. -/
def stepArrowRetract : RetractArrow (step T L B D hBD eB eD hcomm).right
    (L.map hBD).right where
  i := Arrow.homMk (IdempotentCoequalizerSplit.inclusion eB heB).right
    (IdempotentCoequalizerSplit.inclusion eD heD).right (by
      change (IdempotentCoequalizerSplit.inclusion eB heB).right ≫ (L.map hBD).right =
        (step T L B D hBD eB eD hcomm).right ≫
          (IdempotentCoequalizerSplit.inclusion eD heD).right
      exact (congrArg Under.Hom.right
        (IdempotentCoequalizerSplit.map_inclusion eB heB eD heD (L.map hBD) hcomm)).symm)
  r := Arrow.homMk (IdempotentCoequalizerSplit.projection eB).right
    (IdempotentCoequalizerSplit.projection eD).right (by
      change (IdempotentCoequalizerSplit.projection eB).right ≫
          (step T L B D hBD eB eD hcomm).right =
        (L.map hBD).right ≫ (IdempotentCoequalizerSplit.projection eD).right
      exact congrArg Under.Hom.right
        (IdempotentCoequalizerSplit.projection_map eB eD (L.map hBD) hcomm))
  retract := by
    ext
    · exact congrArg Under.Hom.right (IdempotentCoequalizerSplit.inclusion_projection eB heB)
    · exact congrArg Under.Hom.right (IdempotentCoequalizerSplit.inclusion_projection eD heD)

/-- The source inclusion component is the actual original BEFORE split inclusion. -/
@[simp]
theorem stepArrowRetract_i_left :
    (stepArrowRetract T L B D hBD eB eD heB heD hcomm).i.left =
      (IdempotentCoequalizerSplit.inclusion eB heB).right := rfl

/-- The target inclusion component is the actual original AFTER split inclusion. -/
@[simp]
theorem stepArrowRetract_i_right :
    (stepArrowRetract T L B D hBD eB eD heB heD hcomm).i.right =
      (IdempotentCoequalizerSplit.inclusion eD heD).right := rfl

/-- The source projection component is the actual original BEFORE projection. -/
@[simp]
theorem stepArrowRetract_r_left :
    (stepArrowRetract T L B D hBD eB eD heB heD hcomm).r.left =
      (IdempotentCoequalizerSplit.projection eB).right := rfl

/-- The target projection component is the actual original AFTER projection. -/
@[simp]
theorem stepArrowRetract_r_right :
    (stepArrowRetract T L B D hBD eB eD heB heD hcomm).r.right =
      (IdempotentCoequalizerSplit.projection eD).right := rfl

section Compact

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalAccessibleCategory C chi]
  (good : T.IsGood chi) (hSmall : HasCardinalLT (CellTreeIncrement.Label B D) chi)

/-- The constructed compact-root data belongs to the literal original difference tree. -/
abbrev compactDifference :=
  BoundedCellTreeCompactRetract.compactData chi (CellTreeIncrement.tree T L B D hBD) hSmall
    (fun a => good.presentable_source a.1) (fun a => good.presentable_target a.1)

include heB heD in
/-- Derive the compact scalar geometry over the SAME actual split-image source and target. -/
theorem existsCompactPushout :
    ∃ (A Y : C) (_ : IsCardinalPresentable A chi) (_ : IsCardinalPresentable Y chi)
      (beta : (compactDifference T L B D hBD chi good hSmall).root ⟶ A)
      (a : A ⟶ (IdempotentCoequalizerSplit.obj eB).right)
      (_ : beta ≫ a = (compactDifference T L B D hBD chi good hSmall).rootMap ≫
        (IdempotentCoequalizerSplit.projection eB).right)
      (f : A ⟶ Y) (b : Y ⟶ (IdempotentCoequalizerSplit.obj eD).right)
      (_ : RetractArrow f
        (pushout.inl beta (compactDifference T L B D hBD chi good hSmall).tree.hom)),
      IsPushout a f (step T L B D hBD eB eD hcomm).right b ∧
        IsCardinalPresentable (Arrow.mk f) chi := by
  let R := stepArrowRetract T L B D hBD eB eD heB heD hcomm
  let hR : RetractArrow (step T L B D hBD eB eD hcomm).right
      (CellTreeIncrement.tree T L B D hBD).hom := R
  exact BoundedCellTreeCompactRetract.existsCompactPushout chi
    (CellTreeIncrement.tree T L B D hBD) hSmall
    (fun a => good.presentable_source a.1) (fun a => good.presentable_target a.1) hR

end Compact

section OriginalSupport

open OriginalIdempotentLowerSupport

variable {q : T.endpointObj ⟶ T.endpointObj}
  (S R : State T L q) (h : State.Inclusion S R)
  [HasCoequalizer S.e (𝟙 (L.obj S.support))]
  [HasCoequalizer R.e (𝟙 (L.obj R.support))]

/-- The same original support inclusion gives the whole Arrow retract of its split step. -/
abbrev supportStepArrowRetract :
    RetractArrow (State.splitMap h).right (L.map h.le).right :=
  stepArrowRetract T L S.support R.support h.le S.e R.e
    S.idempotent R.idempotent h.commutes

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalAccessibleCategory C chi]
  (good : T.IsGood chi)
  (hSmall : HasCardinalLT (CellTreeIncrement.Label S.support R.support) chi)

/-- Compact-root data for the literal difference of the original stable supports. -/
abbrev compactDifferenceForInclusion :=
  compactDifference T L S.support R.support h.le chi good hSmall

/-- The compact chart targets the original chosen split objects and their actual split map. -/
theorem existsCompactPushoutForInclusion :
    ∃ (A Y : C) (_ : IsCardinalPresentable A chi) (_ : IsCardinalPresentable Y chi)
      (beta : (compactDifferenceForInclusion T L S R h chi good hSmall).root ⟶ A)
      (a : A ⟶ (State.splitObj S).right)
      (_ : beta ≫ a =
        (compactDifferenceForInclusion T L S R h chi good hSmall).rootMap ≫
          (State.projection S).right)
      (f : A ⟶ Y) (b : Y ⟶ (State.splitObj R).right)
      (_ : RetractArrow f
        (pushout.inl beta
          (compactDifferenceForInclusion T L S R h chi good hSmall).tree.hom)),
      IsPushout a f (State.splitMap h).right b ∧
        IsCardinalPresentable (Arrow.mk f) chi :=
  existsCompactPushout T L S.support R.support h.le S.e R.e
    S.idempotent R.idempotent h.commutes chi good hSmall

omit [HasCoequalizer S.e (𝟙 (L.obj S.support))]
  [HasCoequalizer R.e (𝟙 (L.obj R.support))] in
/-- Unchanged original labels derive membership of the internally constructed compact tree. -/
theorem compactDifferenceForInclusion_hom_mem
    (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W]
    (hs : ∀ a : P, W (s (T.label a)).hom) :
    W (compactDifferenceForInclusion T L S R h chi good hSmall).tree.hom := by
  let H := compactDifferenceForInclusion T L S R h chi good hSmall
  have hsH : ∀ a, W (s (H.tree.label a)).hom := by
    intro a
    rw [H.label_eq]
    exact hs a.1
  exact CellTreeWeakSaturation.hom_mem W H.tree H.lower hsH

omit [HasCoequalizer S.e (𝟙 (L.obj S.support))]
  [HasCoequalizer R.e (𝟙 (L.obj R.support))] in
/-- Every actual scalar retract of this original compact-tree pushout belongs to the class. -/
theorem scalar_memForInclusion
    (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W] [W.IsStableUnderRetracts]
    (hs : ∀ a : P, W (s (T.label a)).hom)
    {A Y : C}
    (beta : (compactDifferenceForInclusion T L S R h chi good hSmall).root ⟶ A)
    (f : A ⟶ Y)
    (Rf : RetractArrow f (pushout.inl beta
      (compactDifferenceForInclusion T L S R h chi good hSmall).tree.hom)) : W f :=
  MorphismProperty.of_retract Rf (W.pushout_inl beta _
    (compactDifferenceForInclusion_hom_mem T L S R h chi good hSmall W hs))

/-- Original cells and the actual closure operations produce a compact scalar in the class. -/
theorem existsCompactPushoutInClassForInclusion
    (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W] [W.IsStableUnderRetracts]
    (hs : ∀ a : P, W (s (T.label a)).hom) :
    ∃ (A Y : C) (_ : IsCardinalPresentable A chi) (_ : IsCardinalPresentable Y chi)
      (beta : (compactDifferenceForInclusion T L S R h chi good hSmall).root ⟶ A)
      (a : A ⟶ (State.splitObj S).right)
      (_ : beta ≫ a =
        (compactDifferenceForInclusion T L S R h chi good hSmall).rootMap ≫
          (State.projection S).right)
      (f : A ⟶ Y) (b : Y ⟶ (State.splitObj R).right)
      (_ : RetractArrow f
        (pushout.inl beta
          (compactDifferenceForInclusion T L S R h chi good hSmall).tree.hom)),
      IsPushout a f (State.splitMap h).right b ∧
        IsCardinalPresentable (Arrow.mk f) chi ∧ W f := by
  obtain ⟨A, Y, hA, hY, beta, a, hroot, f, b, Rf, hPush, hArrow⟩ :=
    existsCompactPushoutForInclusion T L S R h chi good hSmall
  exact ⟨A, Y, hA, hY, beta, a, hroot, f, b, Rf, hPush, hArrow,
    scalar_memForInclusion T L S R h chi good hSmall W hs beta f Rf⟩

end OriginalSupport

end CategoryTheory.SmallObject.BoundedDifferenceSplitChart
