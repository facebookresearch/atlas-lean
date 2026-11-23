/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparison
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange

/-!
# The stock comparison of a strict pullback along an actual fibration

The original pullback and the actual left projection fibration give a weak
constant-path comparison. Its entire old path-ending pullback construction,
constant family and right-properness proof are moved unchanged from
`HomotopyCartesianOpenCoverDescent`. The names, hypotheses and maps remain
unchanged. No second path or fiber construction is introduced.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat

private theorem allSpaces_fibrant (B : TopCat.{u}) : IsFibrant B := by
  let _ : CategoryWithFibrations SSet.{u} :=
    SSet.modelCategoryQuillen.instCategoryWithFibrations
  rw [isFibrant_iff, fibration_iff]
  change TopCat.realizedHornInclusions.{u}.rlp (terminal.from B)
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  rw [← SSet.modelCategoryQuillen.fibration_iff]
  rw [← isFibrant_iff_of_isTerminal _
    (IsTerminal.isTerminalObj TopCat.toSSet _ terminalIsTerminal)]
  exact TopCat.toSSet_obj_kanComplex B

private theorem pathEvalOne_trivialFibration (B : TopCat.{u}) :
    trivialFibrations TopCat.{u} (pathEvalOne B) := by
  let _ : IsFibrant B := allSpaces_fibrant B
  let _ : Fibration (pathEndpoints B) := modelCategory.pathEndpoints_fibration B
  have hf : Fibration (pathEndpoints B ≫ (prod.snd : B ⨯ B ⟶ B)) := inferInstance
  let _ : Fibration (pathEvalOne B) := by
    simpa only [pathEndpoints, prod.lift_snd] using hf
  have hc : weakHomotopyEquivalences (pathConstant B) := by
    apply weakHomotopyEquivalences.of_postcomp _ _
      (pathEvalZero_mem_weakHomotopyEquivalences B)
    rw [pathConstant_evalZero]
    exact weakHomotopyEquivalences.of_isIso _
  have h₁ : weakHomotopyEquivalences (pathEvalOne B) := by
    apply weakHomotopyEquivalences.of_precomp _ _ hc
    rw [pathConstant_evalOne]
    exact weakHomotopyEquivalences.of_isIso _
  exact (mem_trivialFibrations_iff _).mpr
    ⟨inferInstance, (weakEquivalence_iff _).mpr h₁⟩

private abbrev pathsEndingOver {W B : TopCat.{u}} (h : W ⟶ B) : TopCat.{u} :=
  pullback (pathEvalOne B) h

private abbrev pathsEndingOverPath {W B : TopCat.{u}} (h : W ⟶ B) :
    pathsEndingOver h ⟶ pathObject B :=
  pullback.fst (pathEvalOne B) h

private abbrev pathsEndingOverRight {W B : TopCat.{u}} (h : W ⟶ B) :
    pathsEndingOver h ⟶ W :=
  pullback.snd (pathEvalOne B) h

private abbrev pathsEndingOverStart {W B : TopCat.{u}} (h : W ⟶ B) :
    pathsEndingOver h ⟶ B :=
  pathsEndingOverPath h ≫ pathEvalZero B

private def pathsEndingOverConstant {W B : TopCat.{u}} (h : W ⟶ B) :
    W ⟶ pathsEndingOver h :=
  pullback.lift (h ≫ pathConstant B) (𝟙 W) (by simp)

@[reassoc (attr := simp)]
private theorem pathsEndingOverConstant_path {W B : TopCat.{u}} (h : W ⟶ B) :
    pathsEndingOverConstant h ≫ pathsEndingOverPath h = h ≫ pathConstant B := by
  rw [pathsEndingOverConstant, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem pathsEndingOverConstant_right {W B : TopCat.{u}} (h : W ⟶ B) :
    pathsEndingOverConstant h ≫ pathsEndingOverRight h = 𝟙 W := by
  rw [pathsEndingOverConstant, pullback.lift_snd]

@[reassoc]
private theorem pathsEndingOverConstant_start {W B : TopCat.{u}} (h : W ⟶ B) :
    pathsEndingOverConstant h ≫ pathsEndingOverStart h = h := by
  simp [pathsEndingOverStart]

private theorem pathsEndingOverConstant_weak {W B : TopCat.{u}} (h : W ⟶ B) :
    weakHomotopyEquivalences (pathsEndingOverConstant h) := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp (pathEvalOne_trivialFibration B)
  let _ : Fibration (pathEvalOne B) := hf
  let _ : WeakEquivalence (pathEvalOne B) := hw
  have hr : weakHomotopyEquivalences (pathsEndingOverRight h) := by
    change weakEquivalences TopCat.{u} (pathsEndingOverRight h)
    exact (weakEquivalence_iff _).mp inferInstance
  apply weakHomotopyEquivalences.of_postcomp _ _ hr
  rw [pathsEndingOverConstant_right]
  exact weakHomotopyEquivalences.of_isIso _

private def homotopyPullbackToPathsEndingOver
    {E W B : TopCat.{u}} (p : E ⟶ B) (h : W ⟶ B) :
    homotopyPullback p h ⟶ pathsEndingOver h :=
  pullback.lift (homotopyPullbackPath p h) (homotopyPullbackRight p h)
    (homotopyPullbackPath_evalOne p h)

@[reassoc (attr := simp)]
private theorem homotopyPullbackToPathsEndingOver_path
    {E W B : TopCat.{u}} (p : E ⟶ B) (h : W ⟶ B) :
    homotopyPullbackToPathsEndingOver p h ≫ pathsEndingOverPath h =
      homotopyPullbackPath p h := by
  rw [homotopyPullbackToPathsEndingOver, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem homotopyPullbackToPathsEndingOver_right
    {E W B : TopCat.{u}} (p : E ⟶ B) (h : W ⟶ B) :
    homotopyPullbackToPathsEndingOver p h ≫ pathsEndingOverRight h =
      homotopyPullbackRight p h := by
  rw [homotopyPullbackToPathsEndingOver, pullback.lift_snd]

private theorem homotopyPullback_pathsEndingOver_isPullback
    {E W B : TopCat.{u}} (p : E ⟶ B) (h : W ⟶ B) :
    IsPullback (homotopyPullbackLeft p h)
      (homotopyPullbackToPathsEndingOver p h) p (pathsEndingOverStart h) := by
  have hw : homotopyPullbackLeft p h ≫ p =
      homotopyPullbackToPathsEndingOver p h ≫ pathsEndingOverStart h := by
    simp [pathsEndingOverStart, homotopyPullbackPath_evalZero]
  apply IsPullback.of_isLimit'
    (CommSq.mk hw)
  apply PullbackCone.IsLimit.mk hw
    (fun c => pullback.lift (prod.lift c.fst (c.snd ≫ pathsEndingOverRight h))
      (c.snd ≫ pathsEndingOverPath h) (by
        apply prod.hom_ext
        · simpa [pathEndpoints, pathsEndingOverStart] using c.condition
        · simpa [pathEndpoints] using
            (congrArg (fun f => c.snd ≫ f)
              (pullback.condition (f := pathEvalOne B) (g := h))).symm))
  · intro c
    rw [← Category.assoc, pullback.lift_fst]
    simp
  · intro c
    apply pullback.hom_ext
    · rw [Category.assoc, homotopyPullbackToPathsEndingOver_path, pullback.lift_snd]
    · rw [Category.assoc, homotopyPullbackToPathsEndingOver_right,
        ← Category.assoc, pullback.lift_fst]
      simp
  · intro c m hm₁ hm₂
    apply homotopyPullback_hom_ext
    · rw [hm₁]
      symm
      rw [← Category.assoc, pullback.lift_fst]
      simp
    · have hm := hm₂ =≫ pathsEndingOverRight h
      rw [Category.assoc, homotopyPullbackToPathsEndingOver_right] at hm
      rw [hm]
      symm
      rw [← Category.assoc, pullback.lift_fst]
      simp
    · have hm := hm₂ =≫ pathsEndingOverPath h
      simpa only [Category.assoc, homotopyPullbackToPathsEndingOver_path,
        pullback.lift_snd] using hm

/-- A strict pullback along an actual fibration has a weak constant-path comparison. -/
theorem homotopyPullbackComparison_mem_of_isPullback
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} (sq : IsPullback s q p h) [Fibration p] :
    weakHomotopyEquivalences (homotopyPullbackComparison sq.toCommSq) := by
  let c := homotopyPullbackComparison sq.toCommSq
  have hc : c ≫ homotopyPullbackToPathsEndingOver p h = q ≫ pathsEndingOverConstant h := by
    apply pullback.hom_ext
    · simp only [Category.assoc, homotopyPullbackToPathsEndingOver_path,
        c, homotopyPullbackComparison_path, pathsEndingOverConstant_path]
      exact (reassoc_of% sq.w) (pathConstant B)
    · simp [c]
  have houter : IsPullback (c ≫ homotopyPullbackLeft p h) q p
      (pathsEndingOverConstant h ≫ pathsEndingOverStart h) := by
    simpa only [c, homotopyPullbackComparison_left, pathsEndingOverConstant_start] using sq
  have hpb := houter.of_right hc (homotopyPullback_pathsEndingOver_isPullback p h)
  let _ : Fibration (homotopyPullbackToPathsEndingOver p h) := by
    rw [fibration_iff]
    exact MorphismProperty.of_isPullback
      (homotopyPullback_pathsEndingOver_isPullback p h) (mem_fibrations p)
  let _ : WeakEquivalence (pathsEndingOverConstant h) :=
    (weakEquivalence_iff _).mpr (pathsEndingOverConstant_weak h)
  let _ : IsRightProper TopCat.{u} := modelCategory.rightProper
  exact (weakEquivalence_iff c).mp
    (IsRightProper.weakEquivalence_of_isPullback hpb.flip)

end TopCat

end
