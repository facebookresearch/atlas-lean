/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.GrahamWeightedComponentPartition

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem gatedSourcePairSum_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (P : Current V -> Prop) [DecidablePred P] :
    0 ≤ gatedSourcePairSum G beta J A B P := by
  unfold gatedSourcePairSum
  apply tsum_nonneg
  rintro ⟨p, q⟩
  by_cases hp : sources G (ofEdgeFun G p) = A <;>
    by_cases hq : sources G (ofEdgeFun G q) = B <;>
    by_cases hP : P (ofEdgeFun G (fun e => p e + q e)) <;>
    simp [hp, hq, hP]
  exact mul_nonneg
    (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G p))
    (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G q))



theorem gatedSourcePairSum_mono_sources
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (P Q : Current V -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ p q : G.edgeFinset -> Nat,
      sources G (ofEdgeFun G p) = A ->
      sources G (ofEdgeFun G q) = B ->
      P (ofEdgeFun G (fun e => p e + q e)) ->
      Q (ofEdgeFun G (fun e => p e + q e))) :
    gatedSourcePairSum G beta J A B P ≤
      gatedSourcePairSum G beta J A B Q := by
  unfold gatedSourcePairSum
  apply (summable_gatedSourcePairSummand G beta J A B P).tsum_le_tsum
  · rintro ⟨p, q⟩
    let n := ofEdgeFun G (fun e => p e + q e)
    change
      ((if sources G (ofEdgeFun G p) = A
          then weight G beta J (ofEdgeFun G p) else 0) *
        (if sources G (ofEdgeFun G q) = B
          then weight G beta J (ofEdgeFun G q) else 0) *
        (if P n then 1 else 0)) ≤
      ((if sources G (ofEdgeFun G p) = A
          then weight G beta J (ofEdgeFun G p) else 0) *
        (if sources G (ofEdgeFun G q) = B
          then weight G beta J (ofEdgeFun G q) else 0) *
        (if Q n then 1 else 0))
    by_cases hp : sources G (ofEdgeFun G p) = A <;>
      by_cases hq : sources G (ofEdgeFun G q) = B
    · by_cases hP : P n
      · have hQ : Q n := hPQ p q hp hq hP
        simp [n, hp, hq, hP, hQ]
      · by_cases hQ : Q n
        · have hw := mul_nonneg
            (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ
              (ofEdgeFun G p))
            (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ
              (ofEdgeFun G q))
          simpa [hp, hq, hP, hQ] using hw
        · simp [n, hp, hq, hP, hQ]
    · simp [hp, hq]
    · simp [hp]
    · simp [hp]
  · exact summable_gatedSourcePairSummand G beta J A B Q



theorem grahamFirstSurvivor_switching_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    {i j k l m : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    gatedSourcePairSum G beta J {i, k} {k, j}
        (fun n => ¬ CurrentConnected G n i m) ≤
      gatedSourcePairSum G beta J {i, j} ∅
        (fun n => ¬ CurrentConnected G n i m ∧
          (CurrentConnected G n i k ∨ CurrentConnected G n i l)) := by
  have hswitch := gatedSourcePairSum_switching G beta J
    ({i, j} : Finset V) (Ne.symm hjk)
    (fun n => ¬ CurrentConnected G n i m)
  have hsd : ({i, j} : Finset V) ∆ {k, j} = {i, k} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      by_cases hxk : x = k <;> simp_all [eq_comm]
  rw [hsd] at hswitch
  rw [hswitch]
  apply gatedSourcePairSum_mono_sources G beta J hbeta hJ
  intro p q hp hq hP
  let n := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G n = {i, j} := by
    dsimp [n]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    ext x
    simp [Finset.mem_symmDiff]
  have hijC : CurrentConnected G n i j :=
    currentConnected_of_sources_pair G (fun e => p e + q e) hij hsrc
  exact ⟨hP.1, Or.inl
    (CurrentConnected.trans G hijC (CurrentConnected.symm G hP.2))⟩



theorem grahamSecondSurvivor_switching_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    {i j k l m : V} (hik : i ≠ k) (hkl : k ≠ l) (hil : i ≠ l) :
    gatedSourcePairSum G beta J {k, i} {i, l}
        (fun n => ¬ CurrentConnected G n k m) ≤
      gatedSourcePairSum G beta J {k, l} ∅
        (fun n => ¬ CurrentConnected G n k m ∧
          (CurrentConnected G n k i ∨ CurrentConnected G n k j)) := by
  have hswitch := gatedSourcePairSum_switching G beta J
    ({k, l} : Finset V) hil
    (fun n => ¬ CurrentConnected G n k m)
  have hsd : ({k, l} : Finset V) ∆ {i, l} = {k, i} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      by_cases hxi : x = i <;> simp_all [eq_comm]
  rw [hsd] at hswitch
  rw [hswitch]
  apply gatedSourcePairSum_mono_sources G beta J hbeta hJ
  intro p q hp hq hP
  let n := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G n = {k, l} := by
    dsimp [n]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    ext x
    simp [Finset.mem_symmDiff]
  have hklC : CurrentConnected G n k l :=
    currentConnected_of_sources_pair G (fun e => p e + q e) hkl hsrc
  exact ⟨hP.1, Or.inl
    (CurrentConnected.trans G hklC (CurrentConnected.symm G hP.2))⟩

end StatMech.FrontierA
