/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamWeightedFirstGKSDrop

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamCurrentConnected_add_right
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : G.edgeFinset -> Nat) {u v : V}
    (h : CurrentConnected G (ofEdgeFun G p) u v) :
    CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) u v := by
  exact SimpleGraph.Reachable.mono (fun a b hab => by
    refine ⟨hab.1, ?_⟩
    have hedge : s(a, b) ∈ G.edgeFinset := by
      simpa [SimpleGraph.mem_edgeFinset] using hab.1
    calc
      1 ≤ ofEdgeFun G p s(a, b) := hab.2
      _ = p ⟨s(a, b), hedge⟩ := by simp [ofEdgeFun, hedge]
      _ ≤ p ⟨s(a, b), hedge⟩ + q ⟨s(a, b), hedge⟩ :=
        Nat.le_add_right _ _
      _ = ofEdgeFun G (fun e => p e + q e) s(a, b) := by
        simp [ofEdgeFun, hedge]) h



def grahamFirstAdmissibleComponentComplements
    (i j k l m : V) : Finset (Finset V) :=
  Finset.univ.filter (fun S =>
    i ∉ S ∧ j ∉ S ∧ k ∈ S ∧ l ∈ S ∧ m ∈ S)


noncomputable def grahamFirstRemainderMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) : Real :=
  gatedSourcePairSum G beta J {i, j} ∅
    (fun n => ¬ CurrentConnected G n i m ∧
      ¬ CurrentConnected G n i k ∧ ¬ CurrentConnected G n i l)


noncomputable def grahamFirstMixedRemainderMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) : Real :=
  gatedSourcePairSum G beta J {i, j} {k, l}
    (fun n => ¬ CurrentConnected G n i m ∧
      ¬ CurrentConnected G n i k)



theorem grahamFirstRemainder_admissible_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : G.edgeFinset -> Nat) {i j k l m : V} (hij : i ≠ j)
    (hp : sources G (ofEdgeFun G p) = {i, j})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    notConnComp G (ofEdgeFun G (fun e => p e + q e)) i ∈
        grahamFirstAdmissibleComponentComplements i j k l m ↔
      ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i m ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i l := by
  let n := ofEdgeFun G (fun e => p e + q e)
  have hijP : CurrentConnected G (ofEdgeFun G p) i j :=
    currentConnected_of_sources_pair G p hij hp
  have hijN : CurrentConnected G n i j :=
    grahamCurrentConnected_add_right G p q hijP
  rw [grahamFirstAdmissibleComponentComplements, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, _, hk, hl, hm⟩
    rw [mem_notConnComp] at hk hl hm
    exact ⟨hm, hk, hl⟩
  · rintro ⟨hm, hk, hl⟩
    have hi : i ∉ notConnComp G n i := by
      rw [mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G n i)
    have hj : j ∉ notConnComp G n i := by
      rw [mem_notConnComp]
      exact not_not.mpr hijN
    have hk' : k ∈ notConnComp G n i := by
      rw [mem_notConnComp]
      exact hk
    have hl' : l ∈ notConnComp G n i := by
      rw [mem_notConnComp]
      exact hl
    have hm' : m ∈ notConnComp G n i := by
      rw [mem_notConnComp]
      exact hm
    exact ⟨hi, hj, hk', hl', hm'⟩




theorem grahamFirstMixedRemainder_admissible_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : G.edgeFinset -> Nat) {i j k l m : V}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hp : sources G (ofEdgeFun G p) = {i, j})
    (hq : sources G (ofEdgeFun G q) = {k, l}) :
    notConnComp G (ofEdgeFun G (fun e => p e + q e)) i ∈
        grahamFirstAdmissibleComponentComplements i j k l m ↔
      ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i m ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k := by
  let n := ofEdgeFun G (fun e => p e + q e)
  have hijP : CurrentConnected G (ofEdgeFun G p) i j :=
    currentConnected_of_sources_pair G p hij hp
  have hijN : CurrentConnected G n i j :=
    grahamCurrentConnected_add_right G p q hijP
  have hklQ : CurrentConnected G (ofEdgeFun G q) k l :=
    currentConnected_of_sources_pair G q hkl hq
  have hklN : CurrentConnected G n k l := by
    simpa [n, Nat.add_comm] using grahamCurrentConnected_add_right G q p hklQ
  rw [grahamFirstAdmissibleComponentComplements, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, _, hk, _, hm⟩
    rw [mem_notConnComp] at hk hm
    exact ⟨hm, hk⟩
  · rintro ⟨hm, hk⟩
    have hl : ¬ CurrentConnected G n i l := by
      intro hil
      exact hk (CurrentConnected.trans G hil (CurrentConnected.symm G hklN))
    have hiS : i ∉ notConnComp G n i := by
      rw [mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G n i)
    have hjS : j ∉ notConnComp G n i := by
      rw [mem_notConnComp]
      exact not_not.mpr hijN
    have hkS : k ∈ notConnComp G n i := by
      rw [mem_notConnComp]
      exact hk
    have hlS : l ∈ notConnComp G n i := by
      rw [mem_notConnComp]
      exact hl
    have hmS : m ∈ notConnComp G n i := by
      rw [mem_notConnComp]
      exact hm
    exact ⟨hiS, hjS, hkS, hlS, hmS⟩



theorem grahamFirstRemainderMass_eq_componentSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l m : V} (hij : i ≠ j) :
    grahamFirstRemainderMass G beta J i j k l m =
      ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l m,
        grahamFirstComponentFiber G beta J S i {i, j} ∅ := by
  let P : Current V -> Prop := fun n =>
    ¬ CurrentConnected G n i m ∧ ¬ CurrentConnected G n i k ∧
      ¬ CurrentConnected G n i l
  let f : Current V -> Finset V := fun n => notConnComp G n i
  have hpart := gatedSourcePairSum_partition G beta J {i, j} ∅ P f
  unfold grahamFirstRemainderMass
  change gatedSourcePairSum G beta J {i, j} ∅ P = _
  rw [hpart]
  calc
    (∑ S : Finset V,
        gatedSourcePairSum G beta J {i, j} ∅ (fun n => f n = S ∧ P n)) =
      ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l m,
        gatedSourcePairSum G beta J {i, j} ∅ (fun n => f n = S) := by
          rw [grahamFirstAdmissibleComponentComplements, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro S _
          by_cases hS : i ∉ S ∧ j ∉ S ∧ k ∈ S ∧ l ∈ S ∧ m ∈ S
          · rw [if_pos hS]
            apply gatedSourcePairSum_congr_sources
            intro p q hp hq
            have hadm := grahamFirstRemainder_admissible_iff G p q
              (k := k) (l := l) (m := m) hij hp hq
            constructor
            · exact And.left
            · intro hf
              have : f (ofEdgeFun G (fun e => p e + q e)) ∈
                  grahamFirstAdmissibleComponentComplements i j k l m := by
                rw [grahamFirstAdmissibleComponentComplements,
                  Finset.mem_filter]
                simpa [hf] using hS
              exact ⟨hf, hadm.mp this⟩
          · rw [if_neg hS]
            rw [gatedSourcePairSum_congr_sources G beta J {i, j} ∅
              (fun n => f n = S ∧ P n) (fun _ => False)]
            · unfold gatedSourcePairSum
              simp
            · intro p q hp hq
              constructor
              · rintro ⟨hf, hP⟩
                apply hS
                have hadm := (grahamFirstRemainder_admissible_iff G p q
                  (k := k) (l := l) (m := m) hij hp hq).mpr hP
                rw [grahamFirstAdmissibleComponentComplements,
                  Finset.mem_filter] at hadm
                have hprops := hadm.2
                dsimp [f] at hf
                rw [hf] at hprops
                exact hprops
              · exact False.elim
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      rfl


theorem grahamFirstMixedRemainderMass_eq_componentSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l m : V} (hij : i ≠ j) (hkl : k ≠ l) :
    grahamFirstMixedRemainderMass G beta J i j k l m =
      ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l m,
        grahamFirstComponentFiber G beta J S i {i, j} {k, l} := by
  let P : Current V -> Prop := fun n =>
    ¬ CurrentConnected G n i m ∧ ¬ CurrentConnected G n i k
  let f : Current V -> Finset V := fun n => notConnComp G n i
  have hpart := gatedSourcePairSum_partition G beta J {i, j} {k, l} P f
  unfold grahamFirstMixedRemainderMass
  change gatedSourcePairSum G beta J {i, j} {k, l} P = _
  rw [hpart]
  calc
    (∑ S : Finset V,
        gatedSourcePairSum G beta J {i, j} {k, l} (fun n => f n = S ∧ P n)) =
      ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l m,
        gatedSourcePairSum G beta J {i, j} {k, l} (fun n => f n = S) := by
          rw [grahamFirstAdmissibleComponentComplements, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro S _
          by_cases hS : i ∉ S ∧ j ∉ S ∧ k ∈ S ∧ l ∈ S ∧ m ∈ S
          · rw [if_pos hS]
            apply gatedSourcePairSum_congr_sources
            intro p q hp hq
            have hadm := grahamFirstMixedRemainder_admissible_iff
              G p q (m := m) hij hkl hp hq
            constructor
            · exact And.left
            · intro hf
              have : f (ofEdgeFun G (fun e => p e + q e)) ∈
                  grahamFirstAdmissibleComponentComplements i j k l m := by
                rw [grahamFirstAdmissibleComponentComplements,
                  Finset.mem_filter]
                simpa [hf] using hS
              exact ⟨hf, hadm.mp this⟩
          · rw [if_neg hS]
            rw [gatedSourcePairSum_congr_sources G beta J {i, j} {k, l}
              (fun n => f n = S ∧ P n) (fun _ => False)]
            · unfold gatedSourcePairSum
              simp
            · intro p q hp hq
              constructor
              · rintro ⟨hf, hP⟩
                apply hS
                have hadm := (grahamFirstMixedRemainder_admissible_iff
                  G p q (m := m) hij hkl hp hq).mpr hP
                rw [grahamFirstAdmissibleComponentComplements,
                  Finset.mem_filter] at hadm
                have hprops := hadm.2
                dsimp [f] at hf
                rw [hf] at hprops
                exact hprops
              · exact False.elim
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      rfl


theorem grahamFirstGlobalGKSDrop_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    {i j k l m : V} (hij : i ≠ j) (hkl : k ≠ l) :
    0 ≤ currentSum G beta J {k, l} *
        grahamFirstRemainderMass G beta J i j k l m -
      currentSum G beta J ∅ *
        grahamFirstMixedRemainderMass G beta J i j k l m := by
  rw [grahamFirstRemainderMass_eq_componentSum G beta J hij]
  rw [grahamFirstMixedRemainderMass_eq_componentSum G beta J hij hkl]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro S hS
  rw [grahamFirstAdmissibleComponentComplements, Finset.mem_filter] at hS
  exact grahamFirstComponentGKSDrop_nonneg G beta J hbeta hJ S
    hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1

end StatMech.FrontierA
