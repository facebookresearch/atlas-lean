/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase

open Finset

namespace StatMech.Ising.LPRankFiveAggregateCounterexample

open LPRankFiveCounterexample


def AggregateSource :=
  Sigma fun i : Seam => Sigma fun j : Seam =>
    Fin (if i = j then 0 else 1) × ↑(sourceSectorStates i j)

noncomputable instance : Fintype AggregateSource := by
  unfold AggregateSource
  infer_instance


def AggregateTarget :=
  Fin 2 × Sigma fun i : Seam => Sigma fun j : Seam =>
    ↑(targetSectorStates i j)

noncomputable instance : Fintype AggregateTarget := by
  unfold AggregateTarget
  infer_instance


def SelectedCrossingTarget :=
  Fin 2 × Sigma fun j : Seam => ↑(targetSectorStates 2 j)

noncomputable instance : Fintype SelectedCrossingTarget := by
  unfold SelectedCrossingTarget
  infer_instance



theorem sourceSectorStates_unmarked_seam_connected
    (i j : Seam) (_hij : i ≠ j)
    (z : LPRankFiveCounterOrientation × LPRankFiveCounterColoring)
    (_hz : z ∈ sourceSectorStates i j) :
    reachable z.1 Finset.univ 6 7 := by
  let o := z.1
  have hadj : adjacent o Finset.univ 6 7 := by
    refine ⟨4, Finset.mem_univ _, ?_⟩
    simp [LPRankFiveCounterexample.ends]
  have hstep (n : Nat) (v : LPRankFiveCounterVertex)
      (hv : v ∈ component o Finset.univ 6 n) :
      v ∈ component o Finset.univ 6 (n + 1) := by
    change v ∈ componentStep o Finset.univ
      (component o Finset.univ 6 n)
    simp only [componentStep, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl hv
  have h1 : (7 : LPRankFiveCounterVertex) ∈
      component o Finset.univ 6 1 := by
    change (7 : LPRankFiveCounterVertex) ∈
      componentStep o Finset.univ {6}
    simp only [componentStep, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨6, by simp, hadj⟩
  exact hstep 7 7 (hstep 6 7 (hstep 5 7 (hstep 4 7
    (hstep 3 7 (hstep 2 7 (hstep 1 7 h1))))))


theorem card_aggregateSource : Fintype.card AggregateSource = 12 := by
  classical
  unfold AggregateSource
  change Fintype.card (Sigma fun i : Seam => Sigma fun j : Seam =>
    Fin (if i = j then 0 else 1) × ↑(sourceSectorStates i j)) = 12
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe]
  have hterm (i j : Seam) :
      (if i = j then 0 else 1) * (sourceSectorStates i j).card =
        if i = j then 0 else 2 := by
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, sourceSectorStates_card_of_ne i j hij]
  simp_rw [hterm]
  decide


theorem card_aggregateTarget : Fintype.card AggregateTarget = 12 := by
  classical
  unfold AggregateTarget
  change Fintype.card (Fin 2 × Sigma fun i : Seam => Sigma fun j : Seam =>
    ↑(targetSectorStates i j)) = 12
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_coe, targetSectorStates_card]
  decide



theorem card_selectedCrossingTarget :
    Fintype.card SelectedCrossingTarget = 12 := by
  classical
  unfold SelectedCrossingTarget
  change Fintype.card (Fin 2 × Sigma fun j : Seam =>
    ↑(targetSectorStates 2 j)) = 12
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  simp_rw [Fintype.card_coe, targetSectorStates_card]
  decide


theorem aggregateSource_card_le_selectedCrossingTarget :
    Fintype.card AggregateSource ≤
      Fintype.card SelectedCrossingTarget := by
  rw [card_aggregateSource, card_selectedCrossingTarget]



noncomputable def aggregateSourceEmbedding :
    AggregateSource ↪ SelectedCrossingTarget := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  exact aggregateSource_card_le_selectedCrossingTarget

end StatMech.Ising.LPRankFiveAggregateCounterexample
