/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.HopcroftWorklist

/-!
# Total predecessor-work of Hopcroft's actual execution

For every fuel, the initialized splitter trace has cost at most
`2 * |Σ| * n * (Nat.log 2 n + 1)`. For `n ≥ 2`, this is at most
`4 * |Σ| * n * Nat.log 2 n`. The full trace terminates at the same
partition as the existing correct Hopcroft minimization algorithm.

The cost is exactly `hopcroftCost`: predecessor visits plus one per pop.
This is NOT a runtime bound for the List/Finset implementation: scanning
`Finset.univ`, scanning partitions and waiting lists, membership tests,
and initialization are not counted. Counting a returned preimage does
not make the scan that computes it constant-time. An efficient runtime
implementation would additionally require verified reverse-transition
indexes and partition/worklist data structures.

The charging proof follows Hopcroft (1971), as presented by Berstel,
Boasson, Carton and Fagnot, *Minimization of automata* (2010). Pending
replacements are accounted for in `HopcroftWorklist`, not assumed to be
fresh smaller-half events.
-/

@[expose] public section

namespace DFA.Hopcroft

variable {α σ : Type*} [Fintype α] [FinEnum α]
  [Fintype σ] [DecidableEq σ]

private theorem sum_predecessor_hit (M : DFA α σ) (C : Finset σ) (a : α) :
    (∑ b : α, ∑ q : σ, if a = b ∧ M.step q b ∈ C then 1 else 0) =
      (preimage M C a).card := by
  rw [Finset.sum_eq_single a]
  · simp [preimage]
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

/-- Double counting visits by source state and letter, retaining every
incoming transition even when many sources have the same successor. -/
theorem hopcroftCost_eq_sum_splitterCount (M : DFA α σ)
    (trace : List (Finset σ × α)) :
    hopcroftCost M trace =
      (∑ b : α, ∑ q : σ, splitterCount (M.step q b) b trace) +
        trace.length := by
  induction trace with
  | nil => simp [hopcroftCost]
  | cons cb trace ih =>
    obtain ⟨C, a⟩ := cb
    change (preimage M C a).card + 1 + hopcroftCost M trace = _
    rw [ih]
    simp only [splitterCount_cons, Finset.sum_add_distrib,
      List.length_cons]
    rw [sum_predecessor_hit]
    omega

/-- A nonempty popped block pays for its pop, even if its preimage is
empty. This bounds the `+1` term independently of predecessor visits. -/
theorem length_le_sum_splitterCount (trace : List (Finset σ × α))
    (hne : ∀ cb ∈ trace, cb.1.Nonempty) :
    trace.length ≤ ∑ b : α, ∑ q : σ, splitterCount q b trace := by
  induction trace with
  | nil => simp
  | cons cb trace ih =>
    obtain ⟨C, a⟩ := cb
    have ht := ih (fun cb hcb => hne cb (List.mem_cons_of_mem _ hcb))
    have hp := (hne (C, a) List.mem_cons_self).card_pos
    change 0 < C.card at hp
    have hh : (∑ b : α, ∑ q : σ,
        if a = b ∧ q ∈ C then 1 else 0) = C.card := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hba
        simp [Ne.symm hba]
      · simp
    simp only [splitterCount_cons, Finset.sum_add_distrib,
      List.length_cons]
    rw [hh]
    omega

/-- **Total predecessor-work bound**, including one unit for every pop,
for every prefix of the initialized execution. No runtime claim is made
for the scanning implementation or for initialization. -/
theorem hopcroftCost_init_trace_le (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] (k : ℕ) :
    hopcroftCost M (hopcroftSplitters M k (initP M) (initW M)) ≤
      2 * Fintype.card α * Fintype.card σ *
        (Nat.log 2 (Fintype.card σ) + 1) := by
  let trace := hopcroftSplitters M k (initP M) (initW M)
  have hb (f : σ → α → σ) :
      (∑ b : α, ∑ q : σ, splitterCount (f q b) b trace) ≤
        Fintype.card α * Fintype.card σ *
          (Nat.log 2 (Fintype.card σ) + 1) := by
    calc
      _ ≤ ∑ _b : α, ∑ _q : σ,
          (Nat.log 2 (Fintype.card σ) + 1) := by
        apply Finset.sum_le_sum
        intro b _
        exact Finset.sum_le_sum fun q _ =>
          splitterCount_init_trace_le M k (f q b) b
      _ = _ := by simp [Nat.mul_assoc]
  have hl := (length_le_sum_splitterCount trace
    (fun _ hcb => nonempty_of_mem_hopcroftSplitters M k (inv_init M) hcb)).trans
    (hb fun q _ => q)
  rw [hopcroftCost_eq_sum_splitterCount]
  have hv := hb M.step
  dsimp only [trace] at hv hl
  nlinarith

/-- A uniform `O(|Σ| n log n)` bound, with the explicit constant `4`.
The condition `n ≥ 2` is essential when absorbing the additive unit
into the logarithm. This concerns predecessor-work, not scan runtime. -/
theorem hopcroftCost_init_trace_le_log (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] (k : ℕ)
    (hn : 2 ≤ Fintype.card σ) :
    hopcroftCost M (hopcroftSplitters M k (initP M) (initW M)) ≤
      4 * Fintype.card α * Fintype.card σ *
        Nat.log 2 (Fintype.card σ) := by
  have hl : 1 ≤ Nat.log 2 (Fintype.card σ) :=
    Nat.le_log_of_pow_le (by decide) (by simpa using hn)
  have hm := Nat.mul_le_mul_left (2 * Fintype.card α * Fintype.card σ)
    (show Nat.log 2 (Fintype.card σ) + 1 ≤
      2 * Nat.log 2 (Fintype.card σ) by omega)
  exact (hopcroftCost_init_trace_le M k).trans (by nlinarith)

/-- The bound for the complete terminating minimization execution.
`DFA.hopcroftLoop_waiting_eq_nil` proves this fuel exhausts the queue;
`hopcroftLoop_eq_hopcroftLoop_of_length` ties the trace to its result. -/
theorem hopcroftCost_complete_le (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] :
    hopcroftCost M (hopcroftSplitters M
      (Fintype.card α * (Fintype.card σ + 1)) (initP M) (initW M)) ≤
        2 * Fintype.card α * Fintype.card σ *
          (Nat.log 2 (Fintype.card σ) + 1) :=
  hopcroftCost_init_trace_le M _

omit [Fintype α] [DecidableEq σ] in
/-- With at most one state, the accepting/rejecting split has an empty
side, so the algorithm has no initial splitters. -/
theorem initW_eq_nil_of_card_le_one (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] (hn : Fintype.card σ ≤ 1) :
    initW M = [] := by
  have : Subsingleton σ := Fintype.card_le_one_iff_subsingleton.mp hn
  unfold initW
  split_ifs with h
  · obtain ⟨x, hx⟩ := h.1
    obtain ⟨y, hy⟩ := h.2
    have heq : x = y := Subsingleton.elim x y
    subst y
    simp only [accBlock, rejBlock, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx hy
    exact (hy hx).elim
  · rfl

omit [Fintype α] in
/-- Zero predecessor-work for zero/one-state boundary parameters.
This does not assert that constructing the initial partition costs zero. -/
theorem hopcroftCost_eq_zero_of_card_le_one (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] (k : ℕ) (hn : Fintype.card σ ≤ 1) :
    hopcroftCost M (hopcroftSplitters M k (initP M) (initW M)) = 0 := by
  rw [initW_eq_nil_of_card_le_one M hn]
  cases k <;> rfl

/-- An empty alphabet causes no predecessor-work, for any state count. -/
theorem hopcroftCost_eq_zero_of_alphabet_card_eq_zero (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] (k : ℕ) (ha : Fintype.card α = 0) :
    hopcroftCost M (hopcroftSplitters M k (initP M) (initW M)) = 0 := by
  have h := hopcroftCost_init_trace_le M k
  simpa [ha] using h

end DFA.Hopcroft
