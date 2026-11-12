/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCausalCrossBridge

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma mem_take_realizedEquiv_iff
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (i : Fin (Fintype.card E)) (t : ℕ) :
    realizedEquiv S base i ∈ (realizedList S base).take t ↔ (i : ℕ) < t := by
  have hefull : realizedEquiv S base i ∈ realizedList S base := by
    rw [← List.mem_toFinset, realizedList_toFinset]
    simp
  rw [List.mem_take_iff_idxOf_lt hefull]
  simpa only [← realizedEquiv_symm_val, Equiv.symm_apply_apply]




theorem causalMixLabels_extendDecisionTreeAt_eq_adaptWt
    (t : ℕ) (T : DecisionTree E) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) :
    causalMixLabels
        (extendDecisionTreeAt t T base (Finset.univ : Finset E)) base U V =
      AdaptMConditional.adaptWt U V (T.queried base).card t := by
  let St := extendDecisionTreeAt t T base (Finset.univ : Finset E)
  let S0 := extendDecisionTree T base (Finset.univ : Finset E)
  have hlists : realizedList St base = realizedList S0 base := by
    exact realizedList_extendDecisionTreeAt t T base base Finset.univ
  have hshared : sharedEdges St base =
      T.queried base \
        ((realizedList S0 base).take t).toFinset := by
    simpa [St, S0] using
      sharedEdges_extendDecisionTreeAt_eq_sdiff_take
        t T base base (Finset.univ : Finset E) (by simp)
  funext i
  let e := realizedEquiv St base i
  have hequery : e ∈ T.queried base ↔ (i : ℕ) < (T.queried base).card := by
    have htakeq :
        ((realizedList S0 base).take (T.queried base).card).toFinset =
          T.queried base := by
      simpa [S0] using realizedList_take_queried_extendDecisionTree
        T base base (Finset.univ : Finset E) (by simp)
    have hmemEq : e ∈ T.queried base ↔
        e ∈ ((realizedList S0 base).take (T.queried base).card).toFinset := by
      rw [htakeq]
    rw [hmemEq, List.mem_toFinset, ← hlists]
    exact mem_take_realizedEquiv_iff St base i (T.queried base).card
  have hetake : e ∈ (realizedList S0 base).take t ↔ (i : ℕ) < t := by
    rw [← hlists]
    exact mem_take_realizedEquiv_iff St base i t
  have hmem : e ∈ sharedEdges St base ↔
      (i : ℕ) < (T.queried base).card ∧ ¬ (i : ℕ) < t := by
    rw [hshared]
    simp only [Finset.mem_sdiff, List.mem_toFinset, hequery, hetake]
  unfold causalMixLabels AdaptMConditional.adaptWt
  change (if independentAt St base e then V i else U i) = _
  by_cases hit : (i : ℕ) < t
  · have hnot : e ∉ sharedEdges St base := by
      intro he
      exact (hmem.mp he).2 hit
    have hind : independentAt St base e = true := by
      apply Bool.eq_true_of_not_eq_false
      intro hfalse
      apply hnot
      exact (mem_sharedEdges_iff_independentAt_false St base e (by simp)).mpr hfalse
    simp [hit, hind]
  · by_cases him : (i : ℕ) < (T.queried base).card
    · have hmem' : e ∈ sharedEdges St base := hmem.mpr ⟨him, hit⟩
      have hind : independentAt St base e = false :=
        (mem_sharedEdges_iff_independentAt_false St base e (by simp)).mp hmem'
      simp [hit, him, hind]
    · have hnot : e ∉ sharedEdges St base := by
        intro he
        exact him (hmem.mp he).1
      have hind : independentAt St base e = true := by
        apply Bool.eq_true_of_not_eq_false
        intro hfalse
        apply hnot
        exact (mem_sharedEdges_iff_independentAt_false St base e (by simp)).mpr hfalse
      simp [hit, him, hind]



theorem causalMixLabels_extendDecisionTreeTriple_left_eq_adaptWt
    (t : ℕ) (T : DecisionTree E) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) :
    let S := extendDecisionTreeTriple (some t) T base
      (Finset.univ : Finset E)
    causalMixLabels S.leftOrder base U V =
      AdaptMConditional.adaptWt U V (T.queried base).card t := by
  dsimp only
  rw [extendDecisionTreeTriple_leftOrder]
  exact causalMixLabels_extendDecisionTreeAt_eq_adaptWt t T base U V



theorem causalMixLabels_extendDecisionTreeTriple_right_eq_adaptWt
    (t : ℕ) (T : DecisionTree E) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) :
    let S := extendDecisionTreeTriple (some t) T base
      (Finset.univ : Finset E)
    causalMixLabels S.rightOrder base U V =
      AdaptMConditional.adaptWt U V (T.queried base).card (t + 1) := by
  dsimp only
  rw [extendDecisionTreeTriple_rightOrder]
  exact causalMixLabels_extendDecisionTreeAt_eq_adaptWt (t + 1) T base U V

end AdaptiveCausalKernel
end OSSS
end StatMech
