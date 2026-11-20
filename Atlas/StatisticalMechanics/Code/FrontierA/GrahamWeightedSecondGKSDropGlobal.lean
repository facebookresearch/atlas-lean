/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamWeightedSecondGKSDrop

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]



def grahamSecondAdmissibleComponentComplements
    (i j k l m : V) : Finset (Finset V) :=
  Finset.univ.filter (fun S =>
    i ∈ S ∧ j ∈ S ∧ m ∈ S ∧ k ∉ S ∧ l ∉ S)

noncomputable def grahamSecondRemainderMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) : Real :=
  gatedSourcePairSum G beta J {k, l} ∅
    (fun n => ¬ CurrentConnected G n k m ∧
      ¬ CurrentConnected G n k i ∧ ¬ CurrentConnected G n k j)

noncomputable def grahamSecondMixedRemainderMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) : Real :=
  gatedSourcePairSum G beta J {i, j} {k, l}
    (fun n => ¬ CurrentConnected G n i k ∧ CurrentConnected G n i m)

theorem grahamSecondRemainder_admissible_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : G.edgeFinset -> Nat) {i j k l m : V} (hkl : k ≠ l)
    (hp : sources G (ofEdgeFun G p) = {k, l})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    notConnComp G (ofEdgeFun G (fun e => p e + q e)) k ∈
        grahamSecondAdmissibleComponentComplements i j k l m ↔
      ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) k m ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) k i ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) k j := by
  let n := ofEdgeFun G (fun e => p e + q e)
  have hklP : CurrentConnected G (ofEdgeFun G p) k l :=
    currentConnected_of_sources_pair G p hkl hp
  have hklN : CurrentConnected G n k l :=
    grahamCurrentConnected_add_right G p q hklP
  rw [grahamSecondAdmissibleComponentComplements, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, hj, hm, _, _⟩
    rw [mem_notConnComp] at hi hj hm
    exact ⟨hm, hi, hj⟩
  · rintro ⟨hm, hi, hj⟩
    have hiS : i ∈ notConnComp G n k := by rw [mem_notConnComp]; exact hi
    have hjS : j ∈ notConnComp G n k := by rw [mem_notConnComp]; exact hj
    have hmS : m ∈ notConnComp G n k := by rw [mem_notConnComp]; exact hm
    have hkS : k ∉ notConnComp G n k := by
      rw [mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G n k)
    have hlS : l ∉ notConnComp G n k := by
      rw [mem_notConnComp]
      exact not_not.mpr hklN
    exact ⟨hiS, hjS, hmS, hkS, hlS⟩

theorem grahamSecondMixedRemainder_admissible_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : G.edgeFinset -> Nat) {i j k l m : V}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hp : sources G (ofEdgeFun G p) = {i, j})
    (hq : sources G (ofEdgeFun G q) = {k, l}) :
    (notConnComp G (ofEdgeFun G (fun e => p e + q e)) k ∈
        grahamSecondAdmissibleComponentComplements i j k l m ∧
      CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i m) ↔
      (¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i m) := by
  let n := ofEdgeFun G (fun e => p e + q e)
  have hijP : CurrentConnected G (ofEdgeFun G p) i j :=
    currentConnected_of_sources_pair G p hij hp
  have hijN : CurrentConnected G n i j :=
    grahamCurrentConnected_add_right G p q hijP
  have hklQ : CurrentConnected G (ofEdgeFun G q) k l :=
    currentConnected_of_sources_pair G q hkl hq
  have hklN : CurrentConnected G n k l := by
    simpa [n, Nat.add_comm] using grahamCurrentConnected_add_right G q p hklQ
  constructor
  · rintro ⟨hadm, him⟩
    rw [grahamSecondAdmissibleComponentComplements,
      Finset.mem_filter] at hadm
    have hki : ¬ CurrentConnected G n k i := by
      rw [← mem_notConnComp]
      exact hadm.2.1
    exact ⟨fun hik => hki (CurrentConnected.symm G hik), him⟩
  · rintro ⟨hik, him⟩
    have hki : ¬ CurrentConnected G n k i :=
      fun hki => hik (CurrentConnected.symm G hki)
    have hkj : ¬ CurrentConnected G n k j := by
      intro hkj
      exact hki (CurrentConnected.trans G hkj (CurrentConnected.symm G hijN))
    have hkm : ¬ CurrentConnected G n k m := by
      intro hkm
      exact hki (CurrentConnected.trans G hkm (CurrentConnected.symm G him))
    have hiS : i ∈ notConnComp G n k := by rw [mem_notConnComp]; exact hki
    have hjS : j ∈ notConnComp G n k := by rw [mem_notConnComp]; exact hkj
    have hmS : m ∈ notConnComp G n k := by rw [mem_notConnComp]; exact hkm
    have hkS : k ∉ notConnComp G n k := by
      rw [mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G n k)
    have hlS : l ∉ notConnComp G n k := by
      rw [mem_notConnComp]
      exact not_not.mpr hklN
    refine ⟨?_, him⟩
    rw [grahamSecondAdmissibleComponentComplements, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hiS, hjS, hmS, hkS, hlS⟩

theorem grahamSecondRemainderMass_eq_componentSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l m : V} (hkl : k ≠ l) :
    grahamSecondRemainderMass G beta J i j k l m =
      ∑ S ∈ grahamSecondAdmissibleComponentComplements i j k l m,
        grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) := by
  let P : Current V -> Prop := fun n =>
    ¬ CurrentConnected G n k m ∧ ¬ CurrentConnected G n k i ∧
      ¬ CurrentConnected G n k j
  let f : Current V -> Finset V := fun n => notConnComp G n k
  have hpart := gatedSourcePairSum_partition G beta J {k, l} ∅ P f
  unfold grahamSecondRemainderMass
  change gatedSourcePairSum G beta J {k, l} ∅ P = _
  rw [hpart]
  calc
    (∑ S : Finset V,
        gatedSourcePairSum G beta J {k, l} ∅ (fun n => f n = S ∧ P n)) =
      ∑ S ∈ grahamSecondAdmissibleComponentComplements i j k l m,
        gatedSourcePairSum G beta J {k, l} ∅
          (fun n => f n = S ∧ True) := by
          rw [grahamSecondAdmissibleComponentComplements, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro S _
          by_cases hS : i ∈ S ∧ j ∈ S ∧ m ∈ S ∧ k ∉ S ∧ l ∉ S
          · rw [if_pos hS]
            apply gatedSourcePairSum_congr_sources
            intro p q hp hq
            have hadm := grahamSecondRemainder_admissible_iff G p q
              (i := i) (j := j) (m := m) hkl hp hq
            constructor
            · rintro ⟨hf, hP⟩
              exact ⟨hf, True.intro⟩
            · rintro ⟨hf, _⟩
              have hmemb : f (ofEdgeFun G (fun e => p e + q e)) ∈
                  grahamSecondAdmissibleComponentComplements i j k l m := by
                rw [grahamSecondAdmissibleComponentComplements,
                  Finset.mem_filter]
                simpa [hf] using hS
              exact ⟨hf, hadm.mp hmemb⟩
          · rw [if_neg hS]
            rw [gatedSourcePairSum_congr_sources G beta J {k, l} ∅
              (fun n => f n = S ∧ P n) (fun _ => False)]
            · unfold gatedSourcePairSum
              simp
            · intro p q hp hq
              constructor
              · rintro ⟨hf, hP⟩
                apply hS
                have hadm := (grahamSecondRemainder_admissible_iff G p q
                  (i := i) (j := j) (m := m) hkl hp hq).mpr hP
                rw [grahamSecondAdmissibleComponentComplements,
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

theorem grahamSecondMixedRemainderMass_eq_componentSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l m : V} (hij : i ≠ j) (hkl : k ≠ l) :
    grahamSecondMixedRemainderMass G beta J i j k l m =
      ∑ S ∈ grahamSecondAdmissibleComponentComplements i j k l m,
        grahamSecondComponentFiber G beta J S k {i, j} {k, l}
          (fun n => CurrentConnected G n i m) := by
  let P : Current V -> Prop := fun n =>
    ¬ CurrentConnected G n i k ∧ CurrentConnected G n i m
  let f : Current V -> Finset V := fun n => notConnComp G n k
  have hpart := gatedSourcePairSum_partition G beta J {i, j} {k, l} P f
  unfold grahamSecondMixedRemainderMass
  change gatedSourcePairSum G beta J {i, j} {k, l} P = _
  rw [hpart]
  calc
    (∑ S : Finset V,
        gatedSourcePairSum G beta J {i, j} {k, l} (fun n => f n = S ∧ P n)) =
      ∑ S ∈ grahamSecondAdmissibleComponentComplements i j k l m,
        gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => f n = S ∧ CurrentConnected G n i m) := by
          rw [grahamSecondAdmissibleComponentComplements, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro S _
          by_cases hS : i ∈ S ∧ j ∈ S ∧ m ∈ S ∧ k ∉ S ∧ l ∉ S
          · rw [if_pos hS]
            apply gatedSourcePairSum_congr_sources
            intro p q hp hq
            have hadm := grahamSecondMixedRemainder_admissible_iff
              G p q (m := m) hij hkl hp hq
            constructor
            · rintro ⟨hf, hP⟩
              exact ⟨hf, hP.2⟩
            · rintro ⟨hf, him⟩
              have hmemb : f (ofEdgeFun G (fun e => p e + q e)) ∈
                  grahamSecondAdmissibleComponentComplements i j k l m := by
                rw [grahamSecondAdmissibleComponentComplements,
                  Finset.mem_filter]
                simpa [hf] using hS
              exact ⟨hf, hadm.mp ⟨hmemb, him⟩⟩
          · rw [if_neg hS]
            rw [gatedSourcePairSum_congr_sources G beta J {i, j} {k, l}
              (fun n => f n = S ∧ P n) (fun _ => False)]
            · unfold gatedSourcePairSum
              simp
            · intro p q hp hq
              constructor
              · rintro ⟨hf, hP⟩
                apply hS
                have hadm := (grahamSecondMixedRemainder_admissible_iff
                  G p q (m := m) hij hkl hp hq).mpr hP
                rw [grahamSecondAdmissibleComponentComplements,
                  Finset.mem_filter] at hadm
                have hprops := hadm.1.2
                dsimp [f] at hf
                rw [hf] at hprops
                exact hprops
              · exact False.elim
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      rfl

theorem grahamSecondGlobalGKSDrop_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    0 ≤ (currentSum G beta J {i, m} * currentSum G beta J {j, m}) *
        grahamSecondRemainderMass G beta J i j k l m -
      currentSum G beta J ∅ ^ 2 *
        grahamSecondMixedRemainderMass G beta J i j k l m := by
  rw [grahamSecondRemainderMass_eq_componentSum G beta J hkl]
  rw [grahamSecondMixedRemainderMass_eq_componentSum G beta J hij hkl]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro S hS
  rw [grahamSecondAdmissibleComponentComplements, Finset.mem_filter] at hS
  exact grahamSecondComponentGKSDrop_nonneg G beta J hbeta hJ S
    hij hik hil him hjk hjl hjm hkl hkm hlm
    hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 hS.2.2.2.2.2

end StatMech.FrontierA
