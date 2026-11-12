/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamWeightedLemmaOneFiber
import Code.FrontierA.GrahamWeightedGateShift
import Code.Sharpness.MeanfieldIsingMass











open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem couplingIn_couplingIn_of_subset
    (J : Sym2 V -> Real) {S T : Finset V} (hST : S ⊆ T) :
    couplingIn (couplingIn J T) S = couplingIn J S := by
  funext e
  unfold couplingIn
  by_cases hS : edgeInside S e
  · have hT : edgeInside T e := by
      intro x hx
      exact hST (hS x hx)
    simp [hS, hT]
  · simp [hS]



noncomputable def grahamCutPairCorrelation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (x y : V) (S : Finset V) : Real :=
  if x ∈ S ∧ y ∈ S then expectationJ G beta (couplingIn J S) {x, y} else 0



theorem grahamCutPairCorrelation_monotone
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (x y : V) :
    Monotone (grahamCutPairCorrelation G beta J x y) := by
  intro S T hST
  unfold grahamCutPairCorrelation
  by_cases hxyS : x ∈ S ∧ y ∈ S
  · have hxyT : x ∈ T ∧ y ∈ T := ⟨hST hxyS.1, hST hxyS.2⟩
    rw [if_pos hxyS, if_pos hxyT]
    have hmono := expectationJ_couplingIn_le G beta (couplingIn J T) hbeta
      (fun e => by
        unfold couplingIn
        split <;> simp_all [hJ e]) S {x, y}
    rwa [couplingIn_couplingIn_of_subset J hST] at hmono
  · rw [if_neg hxyS]
    by_cases hxyT : x ∈ T ∧ y ∈ T
    · rw [if_pos hxyT]
      exact Ising.acr_expectationJ_nonneg G beta (couplingIn J T) hbeta
        (fun e => by
          unfold couplingIn
          split <;> simp_all [hJ e]) {x, y}
    · simp [hxyT]




def GrahamCutPositiveAssociation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (m : V) : Prop :=
  ∀ f g : Finset V -> Real, Monotone f -> Monotone g ->
    (∑ S : Finset V, isingCutMass G beta J m S * f S) *
        (∑ S : Finset V, isingCutMass G beta J m S * g S) ≤
      ∑ S : Finset V, isingCutMass G beta J m S * (f S * g S)


theorem sum_isingCutMass_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (m : V) :
    ∑ S : Finset V, isingCutMass G beta J m S = 1 := by
  let Z := currentSum G beta J ∅
  have hZ : Z ≠ 0 := ne_of_gt (Ising.acr_currentSum_empty_pos G beta J)
  have hpart := gatedSourcePairSum_partition G beta J ∅ ∅
    (fun _ => True) (fun n => notConnComp G n m)
  have htrue : gatedSourcePairSum G beta J ∅ ∅ (fun _ => True) = Z ^ 2 := by
    rw [show gatedSourcePairSum G beta J ∅ ∅ (fun _ => True) =
        sourcePairSum G beta J ∅ ∅ by
      unfold gatedSourcePairSum sourcePairSum
      apply tsum_congr
      rintro ⟨p, q⟩
      simp]
    rw [sourcePairSum_eq_mul]
    dsimp only [Z]
    ring
  rw [htrue] at hpart
  simp only [and_true] at hpart
  unfold isingCutMass
  rw [← Finset.mul_sum, ← hpart]
  dsimp only [Z] at hZ ⊢
  field_simp



theorem sum_cutPairCorrelation_eq_sourcePairDisconn_div
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {x y m : V} (hxy : x ≠ y) (hxm : x ≠ m) (hym : y ≠ m) :
    (∑ S : Finset V, isingCutMass G beta J m S *
        grahamCutPairCorrelation G beta J x y S) =
      sourcePairDisconnSum G beta J {x, y} ∅ x m /
        currentSum G beta J ∅ ^ 2 := by
  have hmean := sum_localCorr_mul_isingCutMass_eq_covariance
    G beta J hxy hxm hym
  have hgap := expectationBridgeGap_eq_sourcePairDisconn
    G beta J hxy hxm hym
  have hcmm : expectationJ G beta J {y, m} = expectationJ G beta J {m, y} := by
    congr 1
    ext z
    simp [or_comm]
  rw [hcmm] at hmean
  rw [hgap] at hmean
  rw [← hmean]
  apply Finset.sum_congr rfl
  intro S _
  unfold grahamCutPairCorrelation
  by_cases hxyS : x ∈ S ∧ y ∈ S
  · rw [if_pos hxyS]
    by_cases hmS : m ∈ S
    · rw [isingCutMass_eq_zero_of_mem_root G beta J m S hmS]
      simp
    · simp [hxyS, hmS, mul_comm]
  · rw [if_neg hxyS]
    rw [if_neg (by
      rintro ⟨hx, hy, -⟩
      exact hxyS ⟨hx, hy⟩)]
    simp


private theorem currentConnected_add_left
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : G.edgeFinset -> Nat) {x y : V}
    (h : CurrentConnected G (ofEdgeFun G p) x y) :
    CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) x y := by
  exact SimpleGraph.Reachable.mono (fun a b hab => by
    refine ⟨hab.1, ?_⟩
    have hedge : s(a, b) ∈ G.edgeFinset := by
      simpa [SimpleGraph.mem_edgeFinset] using hab.1
    calc
      1 ≤ ofEdgeFun G p s(a, b) := hab.2
      _ = p ⟨s(a, b), hedge⟩ := by simp [ofEdgeFun, hedge]
      _ ≤ p ⟨s(a, b), hedge⟩ + q ⟨s(a, b), hedge⟩ := Nat.le_add_right _ _
      _ = ofEdgeFun G (fun e => p e + q e) s(a, b) := by simp [ofEdgeFun, hedge]) h



theorem sum_mixedComponentFiber_eq_sourcePairDisconn
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {j k l m : V} (hjk : j ≠ k) (hkl : k ≠ l) :
    (∑ S : Finset V,
      if j ∈ S ∧ k ∈ S ∧ l ∈ S ∧ m ∉ S then
        grahamSourcePairComponentFiber G beta J S m {j, k} {k, l}
      else 0) = sourcePairDisconnSum G beta J {j, k} {k, l} k m := by
  let P : Current V -> Prop := fun n => ¬ CurrentConnected G n k m
  let f : Current V -> Finset V := fun n => notConnComp G n m
  have hterm (S : Finset V) :
      (if j ∈ S ∧ k ∈ S ∧ l ∈ S ∧ m ∉ S then
          grahamSourcePairComponentFiber G beta J S m {j, k} {k, l}
        else 0) =
        gatedSourcePairSum G beta J {j, k} {k, l}
          (fun n => f n = S ∧ P n) := by
    by_cases hgood : j ∈ S ∧ k ∈ S ∧ l ∈ S ∧ m ∉ S
    · rw [if_pos hgood]
      unfold grahamSourcePairComponentFiber
      apply gatedSourcePairSum_congr_sources
      intro p q hp hq
      let n := ofEdgeFun G (fun e => p e + q e)
      constructor
      · intro hn
        refine ⟨hn, ?_⟩
        have hmk : ¬ CurrentConnected G n m k := by
          apply (mem_notConnComp G).mp
          rw [hn]
          exact hgood.2.1
        exact fun hkm => hmk hkm.symm
      · exact fun hn => hn.1
    · rw [if_neg hgood]
      have hzero := gatedSourcePairSum_congr_sources G beta J {j, k} {k, l}
        (fun n => f n = S ∧ P n) (fun _ => False) (fun p q hp hq => by
          let n := ofEdgeFun G (fun e => p e + q e)
          constructor
          · rintro ⟨hn, hP⟩
            have hjk0 := currentConnected_of_sources_pair G p hjk hp
            have hjkN : CurrentConnected G n j k := by
              exact currentConnected_add_left G p q hjk0
            have hkl0 := currentConnected_of_sources_pair G q hkl hq
            have hklN : CurrentConnected G n k l := by
              simpa only [Nat.add_comm] using currentConnected_add_left G q p hkl0
            have hmk : ¬ CurrentConnected G n m k := fun h => hP h.symm
            have hkS : k ∈ S := by
              rw [← hn, mem_notConnComp]
              exact hmk
            have hjS : j ∈ S := by
              rw [← hn, mem_notConnComp]
              intro hmj
              exact hmk (CurrentConnected.trans G hmj hjkN)
            have hlS : l ∈ S := by
              rw [← hn, mem_notConnComp]
              intro hml
              exact hmk (CurrentConnected.trans G hml hklN.symm)
            have hmS : m ∉ S := by
              rw [← hn, mem_notConnComp]
              exact not_not.mpr (CurrentConnected.refl G n m)
            exact (hgood ⟨hjS, hkS, hlS, hmS⟩).elim
          · simp)
      rw [hzero]
      simp [gatedSourcePairSum]
  calc
    (∑ S : Finset V,
        if j ∈ S ∧ k ∈ S ∧ l ∈ S ∧ m ∉ S then
          grahamSourcePairComponentFiber G beta J S m {j, k} {k, l}
        else 0) =
        ∑ S : Finset V, gatedSourcePairSum G beta J {j, k} {k, l}
          (fun n => f n = S ∧ P n) := by
      apply Finset.sum_congr rfl
      intro S _
      exact hterm S
    _ = gatedSourcePairSum G beta J {j, k} {k, l} P :=
      (gatedSourcePairSum_partition G beta J {j, k} {k, l} P f).symm
    _ = sourcePairDisconnSum G beta J {j, k} {k, l} k m := by
      rfl



theorem sum_cutPairCorrelation_mul_eq_mixedDisconn_div
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {j k l m : V} (hjk : j ≠ k) (hkl : k ≠ l) :
    (∑ S : Finset V, isingCutMass G beta J m S *
      (grahamCutPairCorrelation G beta J j k S *
        grahamCutPairCorrelation G beta J k l S)) =
      sourcePairDisconnSum G beta J {j, k} {k, l} k m /
        currentSum G beta J ∅ ^ 2 := by
  let Z := currentSum G beta J ∅
  have hZ : Z ≠ 0 := ne_of_gt (Ising.acr_currentSum_empty_pos G beta J)
  have hsum := sum_mixedComponentFiber_eq_sourcePairDisconn
    G beta J (m := m) hjk hkl
  have hterm (S : Finset V) :
      isingCutMass G beta J m S *
          (grahamCutPairCorrelation G beta J j k S *
            grahamCutPairCorrelation G beta J k l S) =
        Z⁻¹ ^ 2 *
          (if j ∈ S ∧ k ∈ S ∧ l ∈ S ∧ m ∉ S then
            grahamSourcePairComponentFiber G beta J S m {j, k} {k, l}
          else 0) := by
    by_cases hgood : j ∈ S ∧ k ∈ S ∧ l ∈ S ∧ m ∉ S
    · rw [if_pos hgood]
      unfold grahamCutPairCorrelation
      rw [if_pos ⟨hgood.1, hgood.2.1⟩, if_pos ⟨hgood.2.1, hgood.2.2.1⟩]
      unfold isingCutMass
      change Z⁻¹ ^ 2 *
          grahamSourcePairComponentFiber G beta J S m ∅ ∅ *
            (expectationJ G beta (couplingIn J S) {j, k} *
              expectationJ G beta (couplingIn J S) {k, l}) = _
      rw [grahamSourcePairComponentFiber_vacuum_factor G beta J S hgood.2.2.2,
        grahamSourcePairComponentFiber_mixed_factor G beta J S
          hgood.2.2.2 hgood.1 hgood.2.1 hgood.2.2.1]
      rw [Ising.acr_eq15_insertion' G beta (couplingIn J S) {j, k},
        Ising.acr_eq15_insertion' G beta (couplingIn J S) {k, l}]
      ring
    · rw [if_neg hgood]
      by_cases hmS : m ∈ S
      · rw [isingCutMass_eq_zero_of_mem_root G beta J m S hmS]
        simp
      · have hnot : ¬ (j ∈ S ∧ k ∈ S) ∨ ¬ (k ∈ S ∧ l ∈ S) := by
          by_contra h
          push Not at h
          exact hgood ⟨h.1.1, h.1.2, h.2.2, hmS⟩
        rcases hnot with hnot | hnot
        · unfold grahamCutPairCorrelation
          rw [if_neg hnot]
          simp
        · unfold grahamCutPairCorrelation
          rw [if_neg hnot]
          simp
  calc
    (∑ S : Finset V, isingCutMass G beta J m S *
        (grahamCutPairCorrelation G beta J j k S *
          grahamCutPairCorrelation G beta J k l S)) =
        ∑ S : Finset V, Z⁻¹ ^ 2 *
          (if j ∈ S ∧ k ∈ S ∧ l ∈ S ∧ m ∉ S then
            grahamSourcePairComponentFiber G beta J S m {j, k} {k, l}
          else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      exact hterm S
    _ = Z⁻¹ ^ 2 * sourcePairDisconnSum G beta J {j, k} {k, l} k m := by
      rw [← Finset.mul_sum, hsum]
    _ = sourcePairDisconnSum G beta J {j, k} {k, l} k m / Z ^ 2 := by
      field_simp



theorem grahamWeightedLemmaOne_of_cutPositiveAssociation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    {j k l m : V}
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m)
    (hassoc : GrahamCutPositiveAssociation G beta J m) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m ≤
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 := by
  let f := grahamCutPairCorrelation G beta J j k
  let g := grahamCutPairCorrelation G beta J k l
  have hpa := hassoc f g
    (grahamCutPairCorrelation_monotone G beta J hbeta hJ j k)
    (grahamCutPairCorrelation_monotone G beta J hbeta hJ k l)
  have hf := sum_cutPairCorrelation_eq_sourcePairDisconn_div
    G beta J hjk hjm hkm
  have hg := sum_cutPairCorrelation_eq_sourcePairDisconn_div
    G beta J hkl hkm hlm
  have hfg := sum_cutPairCorrelation_mul_eq_mixedDisconn_div
    G beta J (m := m) hjk hkl
  dsimp only [f, g] at hpa
  rw [hf, hg, hfg] at hpa
  rw [sourcePairDisconnSum_gate_shift_left G beta J ∅ hjk] at hpa
  have hZ : 0 < currentSum G beta J ∅ := Ising.acr_currentSum_empty_pos G beta J
  field_simp [hZ.ne'] at hpa
  nlinarith

end StatMech.FrontierA
