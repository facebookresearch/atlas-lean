/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.FinitePatternEnergy
import Code.FK.TwoPoint



open SimpleGraph

namespace StatMech.FK

noncomputable section



theorem cFE_pow_walk_length_le_twoPoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {x y : V} (w : G.Walk x y) :
    cFE p q ^ w.length <= twoPointFun G p q x y := by
  classical
  let I : Finset (Sym2 V) := w.edges.toFinset
  let eta : ConfigSpace I := fun _ => true
  have huniv : DependsOnOutside I (Set.univ : Set (ConfigSpace (Sym2 V))) := by
    intro omega rho _
    simp
  have hpattern := cFE_pow_mul_event_le_pattern_inter G hp hp1 hq
    I eta Set.univ huniv
  have hbase : cFE p q ^ I.card <=
      ∑ omega, (patternEvent I eta).indicator (fun _ => (1 : Real)) omega *
        fkProb G p q omega := by
    simpa [fkProb_sum_eq_one G hp hp1 (zero_lt_one.trans_le hq)] using hpattern
  have hsubset : patternEvent I eta ⊆ connEvent G x y := by
    intro omega homega
    refine ⟨w.transfer (openSub G omega) ?_⟩
    intro e he
    have heG := w.edges_subset_edgeSet he
    induction e using Sym2.inductionOn with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at heG ⊢
      rw [openSub_adj]
      refine ⟨heG, ?_⟩
      have heI : s(a, b) ∈ I := by
        simpa [I] using he
      have heval := congrFun homega ⟨s(a, b), heI⟩
      simpa [patternEvent, Finset.restrict, eta] using heval
  have hmass :
      (∑ omega, (patternEvent I eta).indicator (fun _ => (1 : Real)) omega *
          fkProb G p q omega) <= twoPointFun G p q x y := by
    unfold twoPointFun
    apply Finset.sum_le_sum
    intro omega _
    by_cases hpat : omega ∈ patternEvent I eta
    · have hconn := hsubset hpat
      rw [Set.indicator_of_mem hpat, Set.indicator_of_mem hconn]
      simp
    · rw [Set.indicator_of_notMem hpat, zero_mul]
      exact mul_nonneg (fkProb_nonneg G hp hp1
        (zero_lt_one.trans_le hq) omega)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
  have hcard : I.card <= w.length := by
    dsimp [I]
    exact (List.toFinset_card_le w.edges).trans_eq w.length_edges
  have hc := cFE_pos hp hp1 hq
  have hc1 : cFE p q <= 1 := by
    linarith [cFE_le_half hp hp1 hq]
  exact (pow_le_pow_of_le_one hc.le hc1 hcard).trans (hbase.trans hmass)

end

end StatMech.FK
