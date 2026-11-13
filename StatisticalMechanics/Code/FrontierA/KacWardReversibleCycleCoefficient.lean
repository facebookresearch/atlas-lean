/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardCycleCoefficient









open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

universe u

open StatMech.Onsager



theorem kwGraphLoop_nonbacktracking_of_scalar_ne_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hscalar : kwGraphLoopScalar G phase loop ≠ 0) :
    kwGraphLoopNonbacktracking G loop := by
  intro k
  have hfactor : kwGraphTransition G (fun _ ↦ 1) phase
      (loop k) (loop (k + 1)) ≠ 0 := by
    intro hzero
    apply hscalar
    unfold kwGraphLoopScalar
    exact Finset.prod_eq_zero (Finset.mem_univ k) hzero
  by_cases hstep : (loop k).snd = (loop (k + 1)).fst ∧
      (loop k).edge ≠ (loop (k + 1)).edge
  · exact hstep
  · unfold kwGraphTransition at hfactor
    rw [if_neg hstep] at hfactor
    exact (hfactor rfl).elim



def KWGraphLoopReversalInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) : Prop :=
  ∀ {n : ℕ} [NeZero n] (loop : Fin n → G.Dart),
    kwGraphLoopNonbacktracking G loop →
      kwGraphLoopScalar G phase (kwGraphLoopRev loop) =
        kwGraphLoopScalar G phase loop

theorem kwGraphLoopOrientation_mem_of_reversalInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hrev : KWGraphLoopReversalInvariant G phase)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S)
    (orientation : Fin n ⊕ Fin n) :
    kwGraphLoopOrientation loop orientation ∈
      kwGraphSquarefreeLoopFinset G phase S := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop ⊢
  have hvalid := kwGraphLoop_nonbacktracking_of_scalar_ne_zero
    G phase loop hloop.2
  cases orientation with
  | inl k =>
      exact ⟨(kwGraphLoopExponent_rotate G loop k).trans hloop.1,
        by simpa [kwGraphLoopOrientation, kwGraphLoopScalar_rotate]
          using hloop.2⟩
  | inr k =>
      refine ⟨?_, ?_⟩
      · rw [kwGraphLoopOrientation, kwGraphLoopExponent_rotate,
          kwGraphLoopExponent_loopRev, hloop.1]
      · rw [kwGraphLoopOrientation, kwGraphLoopScalar_rotate,
          hrev loop hvalid]
        exact hloop.2

theorem kwGraphSquarefreeLoopFinset_card_of_reversalInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
    (kwGraphSquarefreeLoopFinset (n := n) G phase S).card = 2 * n := by
  let loops := kwGraphSquarefreeLoopFinset (n := n) G phase S
  let roots := loops.image (fun e ↦ e 0)
  have hcardRoots : roots.card = loops.card := by
    apply Finset.card_image_of_injOn
    exact kwGraph_squarefreeLoop_eval_zero_injective G phase hdeg S
  have hsubset : roots ⊆ kwGraphLoopRootFinset loop := by
    intro root hroot
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hroot
    apply kwGraph_root_mem_loopRootFinset G phase S hloop (e 0)
    exact kwGraph_squarefreeLoop_root_edge_mem G phase S he
  have hle : loops.card ≤ 2 * n := by
    calc
      loops.card = roots.card := hcardRoots.symm
      _ ≤ (kwGraphLoopRootFinset loop).card := Finset.card_le_card hsubset
      _ = 2 * n := kwGraphLoopRootFinset_card_of_squarefree G phase S hloop
  have hge : 2 * n ≤ loops.card := by
    let orient : Fin n ⊕ Fin n → {e // e ∈ loops} := fun k ↦
      ⟨kwGraphLoopOrientation loop k,
        kwGraphLoopOrientation_mem_of_reversalInvariant
          G phase hrev S hloop k⟩
    have horient : Function.Injective orient := by
      intro i j hij
      apply kwGraphLoopOrientation_injective_of_squarefree G phase S hloop
      exact congrArg Subtype.val hij
    have hcard := Fintype.card_le_of_injective orient horient
    simpa [loops, Fintype.card_sum, two_mul] using hcard
  exact Nat.le_antisymm hle hge

theorem kwGraphSquarefreeLoop_scalar_eq_of_reversalInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {d e : Fin n → G.Dart}
    (hd : d ∈ kwGraphSquarefreeLoopFinset G phase S)
    (he : e ∈ kwGraphSquarefreeLoopFinset G phase S) :
    kwGraphLoopScalar G phase e = kwGraphLoopScalar G phase d := by
  have hddata := (kwGraph_mem_squarefreeLoopFinset G phase S d).mp hd
  have hdvalid := kwGraphLoop_nonbacktracking_of_scalar_ne_zero
    G phase d hddata.2
  have hrootEdge := kwGraph_squarefreeLoop_root_edge_mem G phase S he
  have hroot := kwGraph_root_mem_loopRootFinset
    G phase S hd (e 0) hrootEdge
  unfold kwGraphLoopRootFinset at hroot
  rw [Finset.mem_union] at hroot
  have hinj := kwGraph_squarefreeLoop_eval_zero_injective (n := n)
    G phase hdeg S
  rcases hroot with hroot | hroot
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hroot
    have hrot := kwGraphLoopOrientation_mem_of_reversalInvariant
      G phase hrev S hd (Sum.inl k)
    have heq : e = ons_rotate k d := by
      apply hinj he hrot
      simpa [kwGraphLoopOrientation, ons_rotate] using hk.symm
    rw [heq, kwGraphLoopScalar_rotate]
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hroot
    have hrot := kwGraphLoopOrientation_mem_of_reversalInvariant
      G phase hrev S hd (Sum.inr (-k))
    have heq : e = ons_rotate (-k) (kwGraphLoopRev d) := by
      apply hinj he hrot
      simpa [kwGraphLoopOrientation, ons_rotate,
        kwGraphLoopRev, ons_involutiveLoopRev] using hk.symm
    rw [heq, kwGraphLoopScalar_rotate, hrev d hdvalid]

theorem kwGraphSquarefreeLoop_bucket_sum_of_reversalInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {d : Fin n → G.Dart}
    (hd : d ∈ kwGraphSquarefreeLoopFinset G phase S) :
    (∑ e : Fin n → G.Dart,
      if kwGraphLoopExponent G e = ons_finsetExponent S then
        kwGraphLoopScalar G phase e else 0) =
      (2 * n : ℂ) * kwGraphLoopScalar G phase d := by
  classical
  let loops := kwGraphSquarefreeLoopFinset (n := n) G phase S
  calc
    (∑ e : Fin n → G.Dart,
      if kwGraphLoopExponent G e = ons_finsetExponent S then
        kwGraphLoopScalar G phase e else 0) =
        ∑ e ∈ loops, kwGraphLoopScalar G phase e := by
      rw [← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · intro e he
        simp only [loops, kwGraphSquarefreeLoopFinset,
          Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact he.1
      · intro e heExp heNot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heExp
        by_contra hscalar
        apply heNot
        simp [loops, kwGraphSquarefreeLoopFinset, heExp, hscalar]
    _ = ∑ _e ∈ loops, kwGraphLoopScalar G phase d := by
      apply Finset.sum_congr rfl
      intro e he
      exact kwGraphSquarefreeLoop_scalar_eq_of_reversalInvariant
        G phase hrev hdeg S hd he
    _ = (2 * n : ℂ) * kwGraphLoopScalar G phase d := by
      rw [Finset.sum_const, nsmul_eq_mul,
        kwGraphSquarefreeLoopFinset_card_of_reversalInvariant
          G phase hrev hdeg S hd]
      norm_cast



theorem kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) (r : ℕ)
    (d : Fin (r + 1) → G.Dart)
    (hd : d ∈ kwGraphSquarefreeLoopFinset G phase S) :
    kwGraphFormalLogCoeff G phase (ons_finsetExponent S) =
      -kwGraphLoopScalar G phase d := by
  have hddata := (kwGraph_mem_squarefreeLoopFinset G phase S d).mp hd
  have hdegree : ons_finsuppTotalDegree (ons_finsetExponent S) = r + 1 := by
    rw [← hddata.1]
    exact kwGraphLoopExponent_totalDegree G d
  have hrange : r ∈ Finset.range
      (ons_finsuppTotalDegree (ons_finsetExponent S)) := by
    rw [Finset.mem_range, hdegree]
    omega
  unfold kwGraphFormalLogCoeff
  rw [Finset.sum_eq_single r]
  · rw [kwGraphSquarefreeLoop_bucket_sum_of_reversalInvariant
      G phase hrev hdeg S hd]
    push_cast
    field_simp
  · intro r' hr' hne
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro e he
    by_cases hexp : kwGraphLoopExponent G e = ons_finsetExponent S
    · exfalso
      have hdegree' := kwGraphLoopExponent_totalDegree G e
      rw [hexp, hdegree] at hdegree'
      omega
    · simp [hexp]
  · intro hnot
    exact (hnot hrange).elim

theorem kwGraphFormalLogCoeff_squarefree_eq_one_of_reversalInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) {n : ℕ} [NeZero n]
    (d : Fin n → G.Dart)
    (hd : d ∈ kwGraphSquarefreeLoopFinset G phase S)
    (hscalar : kwGraphLoopScalar G phase d = -1) :
    kwGraphFormalLogCoeff G phase (ons_finsetExponent S) = 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant
    G phase hrev hdeg S r d hd, hscalar]
  ring


theorem kwGraphFormalLogCoeff_cycle_of_reversalInvariant_phaseProduct_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle)
    (hphase :
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
      kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) = -1) :
    kwGraphFormalLogCoeff G phase
      (ons_finsetExponent p.edges.toFinset) = 1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hscalar : kwGraphLoopScalar G phase
      (kwGraphCycleDartLoop p) = -1 := by
    rw [kwGraphCycleDartLoop_scalar_eq_phaseProduct G phase p hp]
    exact hphase
  have hd : kwGraphCycleDartLoop p ∈
      kwGraphSquarefreeLoopFinset G phase p.edges.toFinset := by
    rw [kwGraph_mem_squarefreeLoopFinset]
    exact ⟨kwGraphCycleDartLoop_exponent G p hp, by
      rw [hscalar]
      norm_num⟩
  exact kwGraphFormalLogCoeff_squarefree_eq_one_of_reversalInvariant
    G phase hrev hdeg p.edges.toFinset (kwGraphCycleDartLoop p) hd hscalar

end StatMech.FrontierA
