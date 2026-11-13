/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FinCases
import MathlibExt.NumberTheory.MultipleZeta.Series

namespace MetaMathlibExt.MultipleZeta

private def admissibleIndex : Index :=
  ⟨2, ⟨[2], by simp, by simp⟩⟩

private def nonadmissibleIndex : Index :=
  ⟨1, ⟨[1], by simp, by simp⟩⟩

private def depthTwoIndex : Index :=
  ⟨3, ⟨[2, 1], by simp, by decide⟩⟩

private def mOne : StrictDecreasingTuple 1 :=
  ⟨fun _ => ⟨1, by decide⟩, by
    intro i j hij
    fin_cases i
    fin_cases j
    exact (lt_irrefl 0 hij).elim⟩

private def mTwo : StrictDecreasingTuple 2 :=
  ⟨![⟨2, by decide⟩, ⟨1, by decide⟩], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

example : Index.empty.entries = [] := by simp

example : Index.empty.weight = 0 := by simp

example : Index.empty.depth = 0 := by simp

example : admissibleIndex.IsAdmissibleOrEmpty := by
  left
  simp [admissibleIndex, Index.IsAdmissible]

example : ¬nonadmissibleIndex.IsAdmissibleOrEmpty := by
  simp [nonadmissibleIndex, Index.IsAdmissibleOrEmpty, Index.IsAdmissible, Index.depth]

example : (admissibleIndex.entry ⟨0, by decide⟩ : ℕ) = 2 :=
  rfl

example : (depthTwoIndex.entry ⟨0, by decide⟩ : ℕ) = 2 :=
  rfl

example : (depthTwoIndex.entry ⟨1, by decide⟩ : ℕ) = 1 :=
  rfl

example : (mOne.1 ⟨0, by decide⟩ : ℕ) = 1 :=
  rfl

example : (mTwo.1 ⟨0, by decide⟩ : ℕ) = 2 :=
  rfl

example : (mTwo.1 ⟨1, by decide⟩ : ℕ) = 1 :=
  rfl

example (m : StrictDecreasingTuple 2) :
    (m.1 ⟨1, by decide⟩ : ℕ) < (m.1 ⟨0, by decide⟩ : ℕ) := by
  have h01 : (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ := by decide
  exact m.2 h01

example (index : Index) (m : StrictDecreasingTuple index.depth) :
    strictSummand index m =
      (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹ :=
  rfl

example : strictValue Index.empty (.inr Index.empty_depth) = 1 := by
  apply strictValue_empty

private def mWeakTwo : WeaklyDecreasingTuple 2 :=
  ⟨fun _ => ⟨1, by decide⟩, fun _ _ _ => le_rfl⟩

example : (mWeakTwo.1 ⟨0, by decide⟩ : ℕ) = 1 := rfl

example : (mWeakTwo.1 ⟨1, by decide⟩ : ℕ) = 1 := rfl

example (m : WeaklyDecreasingTuple 2) :
    (m.1 ⟨1, by decide⟩ : ℕ) ≤ (m.1 ⟨0, by decide⟩ : ℕ) :=
  m.2 (by decide)

example :
    starSummand depthTwoIndex mTwo.toWeaklyDecreasing = strictSummand depthTwoIndex mTwo :=
  starSummand_toWeaklyDecreasing depthTwoIndex mTwo

example (index : Index) (h : index.IsAdmissibleOrEmpty) :
    starValue index h =
      ∑' m : WeaklyDecreasingTuple index.depth, starSummand index m :=
  rfl

example : starSummand Index.empty WeaklyDecreasingTuple.empty = 1 :=
  starSummand_empty WeaklyDecreasingTuple.empty

example : starValue Index.empty (.inr Index.empty_depth) = 1 := by
  apply starValue_empty

example : (Index.replicate 3 2).entries = [2, 2, 2] := by simp

example : (Index.replicate 3 2).depth = 3 := by simp

example : (Index.replicate 3 2).weight = 6 := by simp

example : Index.replicate 0 2 = Index.empty := rfl

example : (Index.replicate 2 3).entry ⟨1, by simp⟩ = 3 := by simp

example : (Index.replicate 2 2).IsAdmissibleOrEmpty :=
  Index.replicate_isAdmissibleOrEmpty 2 le_rfl

example : ¬(Index.replicate 1 1).IsAdmissibleOrEmpty := by
  simp [Index.replicate, Index.IsAdmissibleOrEmpty, Index.IsAdmissible, Index.depth]

end MetaMathlibExt.MultipleZeta
