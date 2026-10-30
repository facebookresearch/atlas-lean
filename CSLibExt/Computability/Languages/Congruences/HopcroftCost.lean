/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Hopcroft
public import Mathlib.Data.Nat.Log

/-!
# The smaller-half counting lemma for Hopcroft's minimization algorithm

Hopcroft's `O(|Σ| n log n)` bound rests on one counting fact: a state can lie in the
smaller half of a split block only `log₂ n` times, because every such step at least halves
the size of the block containing that state. This file proves that counting lemma, in the
form used by the algorithm: the `smaller` half of a split is at most half the block, a chain
of halving steps grows the initial block by a factor of two per step, and every entry that
`newSplitters` adds for a split block is a half of that block, so a smaller-half entry
halves. It also defines `hopcroftSplitters`, the list of splitters the loop pops, so that
the total-work bound can be stated precisely; that bound itself is not proved here
(it needs the charging argument that turns this counting lemma into a bound on the
predecessor cost). The cost model is predecessor
cost: processing a popped splitter `(C, a)` costs one predecessor visit for each state
whose `a`-successor lies in `C`, i.e. `(preimage M C a).card`, plus `O(1)` per-splitter
overhead for popping and bookkeeping. Splitting the blocks only touches the states in
the preimage, and with reverse transitions each predecessor is visited exactly once
(each state has exactly one `a`-successor), so the preimage size, not the splitter size
`C.card`, is the right summand: if all `n` states transition on `a` to one state `q`,
processing the singleton splitter `({q}, a)` costs `n` predecessor visits while
`C.card` charges only `1`.

## Main results

* `DFA.Hopcroft.two_mul_smaller_card_le`: the smaller of two sets has at most half their
  combined size.
* `DFA.Hopcroft.mul_pow_le_card_of_halving_chain`: after `k` halving steps the initial
  block has size at least `2 ^ k` times the final block.
* `DFA.Hopcroft.smaller_half_chain_le_log`: a state can lie in the smaller half of a split
  block at most `Nat.log 2 n` times.
* `DFA.Hopcroft.mem_newSplitters` and
  `DFA.Hopcroft.two_mul_card_le_of_mem_newSplitters_smaller`: entries added by
  `newSplitters` for a split block are halves of it, and a smaller-half entry has at most
  half the block's size.
* `DFA.Hopcroft.hopcroftSplitters_length_le` and
  `DFA.Hopcroft.hopcroftLoop_eq_hopcroftLoop_of_length`: the splitter trace `hopcroftSplitters`
  and the loop `hopcroftLoop` agree: the trace takes at most `k` steps, and running the
  loop for exactly the trace's length gives the full loop result. This pins the trace to
  the loop, so the trace cannot drift from the loop it is supposed to record.
* `DFA.Hopcroft.hopcroftCost`: the predecessor cost of a splitter trace, `∑ (C, a)`,
  `(preimage M C a).card + 1`, the summand of the total-work bound.
-/

@[expose] public section

namespace DFA

namespace Hopcroft

/-- The smaller of two sets has at most half their combined size: it is one of the two
sets, so twice its size is at most the sum of the two sizes. -/
theorem two_mul_smaller_card_le {σ : Type*} (A B : Finset σ) :
    2 * (smaller A B).card ≤ A.card + B.card := by
  unfold smaller
  split_ifs with h
  · omega
  · have h' : B.card ≤ A.card := Nat.le_of_not_le h
    omega

/-- If two disjoint sets union to `D`, the smaller of them has at most half the size of
`D`. -/
theorem two_mul_smaller_card_le_of_split {σ : Type*} [DecidableEq σ] {D A B : Finset σ}
    (hun : A ∪ B = D) (hdis : Disjoint A B) : 2 * (smaller A B).card ≤ D.card := by
  calc 2 * (smaller A B).card ≤ A.card + B.card := two_mul_smaller_card_le A B
    _ = D.card := by rw [← Finset.card_union_of_disjoint hdis, hun]

/-- After `k` halving steps, the initial block is at least `2 ^ k` times the final block.
The halving hypothesis is stated for the cardinalities only; no subset hypothesis is
needed. -/
theorem mul_pow_le_card_of_halving_chain {σ : Type*} {f : ℕ → Finset σ} {k : ℕ}
    (hstep : ∀ i, i < k → 2 * (f (i + 1)).card ≤ (f i).card) :
    2 ^ k * (f k).card ≤ (f 0).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self k)))
    calc 2 ^ (k + 1) * (f (k + 1)).card = 2 ^ k * (2 * (f (k + 1)).card) := by
          rw [pow_succ, Nat.mul_assoc]
      _ ≤ 2 ^ k * (f k).card := Nat.mul_le_mul_left _ (hstep k (Nat.lt_succ_self k))
      _ ≤ (f 0).card := ih'

/-- **The smaller-half counting lemma.** In a chain of blocks where each step at least
halves the size, a block containing a given state can occur at most `Nat.log 2 n` times
past the start, where `n` is the number of states. In Hopcroft's algorithm, the successive
smaller halves containing one fixed state form such a chain: each of them is the smaller
half of a split of the previous block containing that state.
Source: J. E. Hopcroft, "An `n log n` algorithm for minimizing states in a finite
automaton", Theory of Machines and Computations, 1971; the counting argument is presented
in J. Berstel, L. Boasson, O. Carton and I. Fagnot, "Minimization of automata", 2010. -/
theorem smaller_half_chain_le_log {σ : Type*} [Fintype σ] {f : ℕ → Finset σ} {q : σ}
    {k : ℕ} (hmem : ∀ i, i ≤ k → q ∈ f i)
    (hstep : ∀ i, i < k → 2 * (f (i + 1)).card ≤ (f i).card) :
    k ≤ Nat.log 2 (Fintype.card σ) := by
  have hne : (f k).Nonempty := ⟨q, hmem k le_rfl⟩
  have hpos : 1 ≤ (f k).card := Finset.Nonempty.card_pos hne
  have h1 : 2 ^ k ≤ (f 0).card :=
    calc 2 ^ k = 2 ^ k * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ k * (f k).card := Nat.mul_le_mul_left _ hpos
      _ ≤ (f 0).card := mul_pow_le_card_of_halving_chain hstep
  have h2 : (f 0).card ≤ Fintype.card σ := Finset.card_le_univ _
  have h3 : k ≤ Nat.log 2 (f 0).card := Nat.le_log_of_pow_le (by norm_num) h1
  exact h3.trans (Nat.log_mono_right h2)

variable {α σ : Type*} [Fintype α] [FinEnum α] [Fintype σ] [DecidableEq σ]

omit [Fintype α] [Fintype σ] in
/-- Every entry `newSplitters` adds for a block `D` is a half of `D` (one of the two sides
of the split by `pre`), or the smaller half. -/
theorem mem_newSplitters {W : List (Finset σ × α)} {pre D : Finset σ} {X : Finset σ}
    {b : α} (h : (X, b) ∈ newSplitters W pre D) :
    X ⊆ D ∧ (X = D.filter (· ∈ pre) ∨ X = D.filter (· ∉ pre) ∨
      X = smaller (D.filter (· ∈ pre)) (D.filter (· ∉ pre))) := by
  rw [newSplitters, List.mem_flatMap] at h
  obtain ⟨b', -, h⟩ := h
  split_ifs at h with hDb
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨Finset.filter_subset _ _, Or.inl rfl⟩
    · refine ⟨Finset.filter_subset _ _, Or.inr (Or.inl rfl)⟩
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨hX, hb⟩ := h
    subst hb
    exact ⟨by rw [hX]; unfold smaller; split_ifs <;> exact Finset.filter_subset _ _,
      Or.inr (Or.inr hX)⟩

omit [Fintype α] [Fintype σ] in
/-- A smaller-half entry added by `newSplitters` for a block `D` has at most half the size
of `D`: the two halves are disjoint and union to `D`. No split hypothesis is needed: the
halves of any block partition it. -/
theorem two_mul_card_le_of_mem_newSplitters_smaller {W : List (Finset σ × α)}
    {pre D : Finset σ} {X : Finset σ} {b : α} (h : (X, b) ∈ newSplitters W pre D)
    (hDb : (D, b) ∉ W) :
    2 * X.card ≤ D.card := by
  rw [newSplitters, List.mem_flatMap] at h
  obtain ⟨b', -, h⟩ := h
  split_ifs at h with hDb'
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, hEq⟩ | ⟨-, hEq⟩ <;>
      exact absurd (hEq.symm ▸ hDb') hDb
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨hX, -⟩ := h
    rw [hX]
    refine two_mul_smaller_card_le_of_split ?hun ?hdis
    · exact Finset.filter_union_filter_not_eq (· ∈ pre) D
    · exact Finset.disjoint_filter_filter_not D D _

variable (M : DFA α σ) [DecidablePred (· ∈ M.accept)]

/-- The splitters popped by Hopcroft's loop, in order: the same recursion as
`DFA.hopcroftLoop`, collecting each popped splitter. The cost of processing one popped
splitter `(C, a)` is `(preimage M C a).card + 1`: one predecessor visit per state whose
`a`-successor lies in `C`, plus `O(1)` per-splitter overhead. See `hopcroftCost`.
`hopcroftLoop_eq_hopcroftLoop_of_length` proves this trace records exactly the
splitters the loop pops, so the trace cannot drift from the loop. -/
def hopcroftSplitters : ℕ → List (Finset σ) → List (Finset σ × α) → List (Finset σ × α)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | k + 1, P, (C, a) :: W =>
      (C, a) :: hopcroftSplitters k (roundP M P C a) (roundW M P W C a)

/-- The predecessor cost of a splitter trace: for each popped splitter `(C, a)`, one
predecessor visit per state in the preimage `preimage M C a`, plus `1` per-splitter
overhead. This is the quantity the total-work bound, not proved here, constrains
to `O(|Σ| n log n)`. Charging splitter size `C.card` instead
would undercount: if all `n` states transition on `a` to one state `q`, processing the
singleton splitter `({q}, a)` costs `n` predecessor visits while `C.card` charges
only `1`. -/
def hopcroftCost (trace : List (Finset σ × α)) : ℕ :=
  (trace.map fun cb => (preimage M cb.1 cb.2).card + 1).sum

/-- **The splitter trace records exactly the splitters the loop pops.** The loop and the
trace recurse on the same state, so they take the same number of steps. The two
theorems below make the correspondence usable: the trace length is at most `k`, and
running the loop for exactly the trace's length gives the full loop result, so the trace
contains every splitter the loop pops and no others. -/
theorem hopcroftSplitters_length_le {α σ : Type*} [FinEnum α] [Fintype σ]
    [DecidableEq σ] (M : DFA α σ) (k : ℕ)
    (P : List (Finset σ))
    (W : List (Finset σ × α)) :
    (hopcroftSplitters M k P W).length ≤ k := by
  induction k generalizing P W with
  | zero => simp [hopcroftSplitters]
  | succ k ih =>
    cases W with
    | nil => simp [hopcroftSplitters]
    | cons cb W =>
      obtain ⟨C, a⟩ := cb
      simp only [hopcroftSplitters, List.length_cons]
      have h := ih (roundP M P C a) (roundW M P W C a)
      omega

/-- The trace and the loop take the same number of steps: the trace length is the fuel
the loop consumed, i.e. the loop would stop after exactly that many rounds if run with
only that much fuel. -/
theorem hopcroftLoop_eq_hopcroftLoop_of_length {α σ : Type*} [FinEnum α]
    [Fintype σ] [DecidableEq σ] (M : DFA α σ) (k : ℕ)
    (P : List (Finset σ))
    (W : List (Finset σ × α)) :
    M.hopcroftLoop ((hopcroftSplitters M k P W).length) P W =
      M.hopcroftLoop k P W := by
  induction k generalizing P W with
  | zero => simp [hopcroftSplitters]
  | succ k ih =>
    cases W with
    | nil => rfl
    | cons cb W =>
      obtain ⟨C, a⟩ := cb
      have h := ih (roundP M P C a) (roundW M P W C a)
      change _ = hopcroftLoop M (k + 1) P ((C, a) :: W)
      rw [hopcroftLoop]
      have hlen : (hopcroftSplitters M (k + 1) P ((C, a) :: W)).length =
          (hopcroftSplitters M k (roundP M P C a) (roundW M P W C a)).length + 1 := rfl
      rw [hlen]
      change hopcroftLoop M (_ + 1) P ((C, a) :: W) = _
      rw [hopcroftLoop]
      exact h

end Hopcroft

end DFA
