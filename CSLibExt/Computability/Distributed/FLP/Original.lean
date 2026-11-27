/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Cslib/Computability/Distributed/FLP/PseudoConsensus.lean` and
`Cslib/Computability/Distributed/FLP/Impossibility.lean` (CSLib):
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Ching-Tsun Chou
-/

/-
# The FLP impossibility theorem with its original correctness condition
-/
module

public import CSLibExt.Computability.Distributed.FLP.Bivalence

/-!
# The FLP impossibility theorem with its original correctness condition

Theorem 1 of Fischer, Lynch and Paterson in CSLib's model, by their bivalence argument: every
partially correct algorithm with at least two processes has an admissible run, with at most one
faulty process, in which no process ever decides. Partial correctness asks only that no reachable
state has decided two values and that each value is decided in some reachable state. This is
stronger than CSLib's `Cslib.FLP.Consensus.ge_one_not_exists`, which assumes validity and that
every process that is not faulty decides.

## Proof

Suppose every admissible run with at most one fault decides. Running the processes outside any
one process fairly from any reachable state gives such a run, so a decision is reachable from
every reachable state without any one process (`pseudoTermination_of_forall_decides`). Lemma 2
(`exists_bivalent_start`) then gives a bivalent initial state, and Lemma 3
(`exists_bivalent_recvMsg`) lets CSLib's fair scheduler deliver every pending message while
returning to a bivalent state infinitely often. The resulting run is admissible with no fault,
and it never decides, because a decided state is not bivalent.

## Main results

* `pseudoTermination_of_forall_decides`: if every admissible run with at most one fault decides,
  then a decision is reachable from every reachable state without any one process.
* `flp_original`: Theorem 1 of Fischer, Lynch and Paterson in CSLib's model.

## References

* M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one
  faulty process*, Journal of the ACM 32(2), 1985, 374–382: §2 (partial correctness, admissible
  and deciding runs), Theorem 1 and its proof.
* The fair-run constructions adapt `Cslib.FLP.PseudoConsensus.of_consensus` and
  `Cslib.FLP.OnePseudoConsensus.fair_nonUniform` of CSLib.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.FLP

open Cslib.FLP Function Set Multiset Fintype Filter ωSequence FairScheduler

variable {P M S : Type*} [DecidableEq P] [DecidableEq M] {a : Algorithm P M S}

/-- **Deciding runs give reachable decisions.** If there are at least two processes and every
admissible run of `a` with at most one faulty process decides (some process decides at some
time), then `a` satisfies `PseudoTermination 1`: from every reachable state a decision can be
reached using only the processes of any set that misses at most one process. -/
theorem pseudoTermination_of_forall_decides [Fintype P] (hP : 1 < card P)
    (hdec : ∀ inp ss xs, a.AdmissibleRun inp 1 ss xs → ∃ k b, (ss k).Decided b) :
    a.PseudoTermination 1 := by
  rintro inp s ⟨xl, h_xl⟩ ps h_ps
  let xls := a.fairSegActions (a.simpleDeliver ps) ps s
  obtain ⟨ss, h_omega, h_s, _⟩ :=
    fair_omegaExecution (PseudoConsensus.simpleDeliver_fair ps) s trivial
  obtain ⟨ss', h_omega', _, _, _⟩ := LTS.OmegaExecution.append h_xl h_omega h_s
  have h_dest := omega_forall_actions (r := DestIn ps) (d := a.simpleDeliver ps)
      (PseudoConsensus.simpleDeliver_fair ps) s trivial
      (PseudoConsensus.simpleDeliver_forallActions ps) (by simp [DestIn])
  have : ∀ p, p ∈ ps → ProcFair p ss' (xl ++ω xls.flatten) := by
    intro p h_p
    rw [← Algorithm.drop_procFair_iff h_omega' p xl.length]
    grind [drop_append_of_ge_length]
  have : FairRun ss' (xl ++ω xls.flatten) := by
    intro p
    by_cases h_f : ProcFair p ss' (xl ++ω xls.flatten)
    · grind
    · obtain ⟨m, _, n, _, _⟩ := Algorithm.not_fair_stay_enabled h_omega' h_f
      suffices ProcFaulty p ss' (xl ++ω xls.flatten) by grind
      use n + xl.length, by grind
      intro k h_k m' h_m'
      have : xls.flatten (k - xl.length) = some m' := by grind [get_append_right']
      grind [DestIn]
  have : numProcFaulty ss' (xl ++ω xls.flatten) ≤ 1 := by
    suffices numProcFaulty ss' (xl ++ω xls.flatten) ≤ card P - ps.ncard by grind
    apply numProcFaulty_le_not_procFair
    grind
  have h_adm : a.AdmissibleRun inp 1 ss' (xl ++ω xls.flatten) := by
    grind [Algorithm.AdmissibleRun]
  obtain ⟨n, b, h_nb⟩ := hdec inp ss' _ h_adm
  let m := n + xl.length
  use ss' m, b
  split_ands
  · apply CanReachVia.iff_exists_mTr.mpr
    use (xl ++ω xls.flatten).extract xl.length m, by grind [LTS.OmegaExecution.extract_mTr]
    simp [extract_append_right_right, extract_eq_take,
      List.forall_iff_forall_mem, List.forall_mem_iff_getElem]
    grind
  · suffices a.lts.CanReach (ss' n) (ss' m) by grind [Algorithm.decided_stable]
    use (xl ++ω xls.flatten).extract n m
    grind [LTS.OmegaExecution.extract_mTr]

/-- A reachable bivalent state together with its input. -/
private abbrev ReachableBivalent [Fintype P] (a : Algorithm P M S) (inp : P → Bool)
    (s : State P M S) : Prop :=
  a.Reachable inp s ∧ Bivalent a s

/-- One stage of the construction: deliver `m` and come back to a reachable bivalent state. -/
private lemma bivalent_step_aux [Fintype P] (hP : 2 ≤ card P)
    (hag : ∀ inp s, a.Reachable inp s → s.Agreed) (hpt : a.PseudoTermination 1)
    (inp : P → Bool) (s : State P M S) (m : Message P M) :
    ∃ xl_t, m ∈ s.msgs ∧ ReachableBivalent a inp s →
      let (xl, t) := xl_t
      a.lts.MTr s xl t ∧ some m ∈ xl ∧ ReachableBivalent a inp t := by
  by_cases h : m ∈ s.msgs ∧ ReachableBivalent a inp s
  · obtain ⟨hm, hr, hb⟩ := h
    obtain ⟨t, ⟨xs, hxs, -⟩, hmt, hbt⟩ := exists_bivalent_recvMsg hP hag hpt hr hb hm
    have htr : a.lts.Tr t (some m) (a.recvMsg m t) := ⟨hmt, rfl⟩
    refine ⟨(xs ++ [some m], a.recvMsg m t), fun _ => ⟨LTS.MTr.stepR _ hxs htr, by simp,
      Algorithm.reachable_stable hr ⟨_, LTS.MTr.stepR _ hxs htr⟩, hbt⟩⟩
  · exact ⟨([], s), fun h' => absurd h' h⟩

/-- The stages chosen by `bivalent_step_aux`. -/
private noncomputable def bivalentStep [Fintype P] (hP : 2 ≤ card P)
    (hag : ∀ inp s, a.Reachable inp s → s.Agreed) (hpt : a.PseudoTermination 1)
    (inp : P → Bool) : DeliverMsg P M S :=
  fun s m ↦ Classical.choose (bivalent_step_aux hP hag hpt inp s m)

private theorem fair_bivalentStep [Fintype P] (hP : 2 ≤ card P)
    (hag : ∀ inp s, a.Reachable inp s → s.Agreed) (hpt : a.PseudoTermination 1)
    (inp : P → Bool) :
    a.FairDeliverMsg (bivalentStep hP hag hpt inp) univ (ReachableBivalent a inp) := by
  rintro s m ⟨hm, -, hs⟩
  exact Classical.choose_spec (bivalent_step_aux hP hag hpt inp s m) ⟨hm, hs⟩

/-- **FLP impossibility of asynchronous consensus, original form** (Fischer, Lynch and
Paterson, *Impossibility of distributed consensus with one faulty process*, 1985, Theorem 1, in
CSLib's model). Let there be at least two processes and let `a` be partially correct: no
reachable state has decided two different values, and each value `b` is decided in some state
reachable from some input. Then some admissible run with at most one faulty process never
decides: no process decides at any time. -/
theorem flp_original [Fintype P] (hP : 2 ≤ card P) (a : Algorithm P M S)
    (hagree : ∀ inp s, a.Reachable inp s → s.Agreed)
    (hval : ∀ b, ∃ inp s, a.Reachable inp s ∧ s.Decided b) :
    ∃ inp ss xs, a.AdmissibleRun inp 1 ss xs ∧ ∀ k b, ¬ (ss k).Decided b := by
  by_contra hno
  push Not at hno
  have hpt := pseudoTermination_of_forall_decides (by omega) hno
  obtain ⟨inp, hb⟩ := exists_bivalent_start hval hpt
  let s0 := a.start inp
  have hs0 : ReachableBivalent a inp s0 := ⟨Algorithm.reachable_start, hb⟩
  obtain ⟨ss, h_omega, h_s0, -, h_q, hpos, h_fair⟩ :=
    fair_omegaExecution (fair_bivalentStep hP hagree hpt inp) s0 hs0
  let xls := a.fairSegActions (bivalentStep hP hagree hpt inp) univ s0
  have h_adm : a.AdmissibleRun inp 1 ss xls.flatten := by
    refine ⟨h_s0, h_omega, fun p => Or.inr (h_fair p (mem_univ p)), ?_⟩
    have := numProcFaulty_le_not_procFair (ps := univ) (ss := ss) (xs := xls.flatten)
      (fun p _ => h_fair p (mem_univ p))
    grind [ncard_univ, card_eq_nat_card]
  obtain ⟨k, b, hk⟩ := hno inp ss xls.flatten h_adm
  -- A later stage ends in a reachable bivalent state that has decided `b`.
  have hle : k ≤ xls.cumLen k := (cumLen_strictMono hpos).id_le k
  obtain ⟨hr, hb₀, hb₁⟩ := h_q k
  have hd : (ss (xls.cumLen k)).Decided b :=
    Algorithm.decided_stable hk ⟨xls.flatten.extract k (xls.cumLen k),
      LTS.OmegaExecution.extract_mTr h_omega hle⟩
  have hc : Valent a (ss (xls.cumLen k)) (!b) := by cases b; exacts [hb₁, hb₀]
  obtain ⟨v, hv, hdv⟩ := hc
  have := hagree inp v (Algorithm.reachable_stable hr hv) b (!b)
    ⟨Algorithm.decided_stable hd hv, hdv⟩
  cases b <;> simp at this

end Cslib.Distributed.FLP
