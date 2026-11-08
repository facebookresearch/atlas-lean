/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Throwback sequences of positive integers (Darnell, Dribus)

Statements from J. Darnell and B. F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1.

The throwback operation moves the leader `x₀` of a sequence `X = (x₀, x₁, …)` to index `x₀`:
`τ(X) = (x₁, …, x_{x₀}, x₀, x_{x₀+1}, …)`; the throwback sequence `T(X)` lists the leaders of
`τⁿ(X)`. The special case `X = (3, 4, 5, …)` (Kozar's conjecture for OEIS A357081) is proved as
`MetaMathlibExt.kozar_throwback_recurrence`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The throwback operation `τ` on a sequence `s : ℕ → α` whose entries have positive integer
values `w`: the leader `s 0` moves to index `w (s 0)`, the entries at indices `1, …, w (s 0)`
move one place left, and later entries stay. With `w = id` this is the paper's `τ` on
sequences of positive integers; with `α = ℕ`, `w = X` and initial arrangement `id` it tracks
the original index of each term, so repeated values stay distinguishable.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Section 2. -/
public def throwback {α : Type*} (w : α → ℕ) (s : ℕ → α) : ℕ → α := fun i =>
  if i < w (s 0) then s (i + 1) else if i = w (s 0) then s 0 else s i

/-- The throwback sequence `T(X)`: `t_n` is the leader of `τⁿ(X)`.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Section 2. -/
public def throwbackSequence (X : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((throwback id)^[n] X) 0

/-- Characteristic values: `τ(3, 4, 5, …) = (4, 5, 6, 3, 7, …)`, and the throwback sequence of
`(3, 4, 5, …)` begins `3, 4, 5, 6, 3, 7` (Table 1, OEIS A357081).

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Table 1. -/
public theorem throwback_examples :
    (List.range 5).map (throwback id (fun i => i + 3)) = [4, 5, 6, 3, 7] ∧
      (List.range 6).map (throwbackSequence (fun i => i + 3)) = [3, 4, 5, 6, 3, 7] := by
  decide

/-- The partial placement sequences `P_n(X)` of an increasing sequence `X` of positive
integers, doubly infinite with empty positions (`none`). `P_0(X)` has `x₀` exactly at the
multiples of `x₀ + 1`. `P_{n+1}(X)` keeps `P_n(X)` and places `x_{n+1}` at the first open
position `s ≥ 0` and then, in both directions, at every `(x_{n+1} - (n+1) + 1)`-th open
position (skipping `x_{n+1} - (n+1)` open positions each time): an open position `z` is
filled when the signed number of open positions of `P_n(X)` between `s` and `z` (positions in
`[s, z)` counted positively, in `[z, s)` negatively) is divisible by that period.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Section 4. -/
public noncomputable def partialPlacement (X : ℕ → ℕ) : ℕ → ℤ → Option ℕ
  | 0 => fun z => if ((X 0 : ℤ) + 1) ∣ z then some (X 0) else none
  | n + 1 => fun z =>
      let P := partialPlacement X n
      let s : ℤ := (sInf {p : ℕ | P p = none} : ℕ)
      let openCount : ℤ := (((Finset.Ico s z).filter fun w => P w = none).card : ℤ) -
        (((Finset.Ico z s).filter fun w => P w = none).card : ℤ)
      if P z = none ∧ ((X (n + 1) : ℤ) - (n + 1) + 1) ∣ openCount then some (X (n + 1))
      else P z

/-- Characteristic values: for `X = (3, 4, 5, …)`, `P_0(X)` has `3` at positions `0`, `4` and
`-4` and is empty at positions `1, 2, 3` (Table 4).

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Table 4. -/
public theorem partialPlacement_zero_examples :
    partialPlacement (fun i => i + 3) 0 0 = some 3 ∧
      partialPlacement (fun i => i + 3) 0 4 = some 3 ∧
      partialPlacement (fun i => i + 3) 0 (-4) = some 3 ∧
      ∀ z ∈ ({1, 2, 3} : Finset ℤ), partialPlacement (fun i => i + 3) 0 z = none := by
  simp only [partialPlacement]
  decide

/-- For a sequence `X` of positive integers, each term (tracked by its original index `j`)
either reaches a final nonleader position after finitely many throwbacks, or becomes leader
infinitely often. Terms are tracked by applying `throwback X` to the index arrangement `id`.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 1 (`jis-2025-25.5.1-lem-1`). -/
public theorem_wanted throwback_final_position_or_frequently_leader (X : ℕ → ℕ)
    (hX : ∀ n, 0 < X n) (j : ℕ) :
    (∃ p, 0 < p ∧ ∃ N, ∀ k ≥ N, ((throwback X)^[k] id) p = j) ∨
      {k | ((throwback X)^[k] id) 0 = j}.Infinite

/-- For a sequence `X` of distinct positive integers, every term of `X` appears infinitely
often in the throwback sequence `T(X)`.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 2 (`jis-2025-25.5.1-thm-2`). -/
public theorem_wanted throwbackSequence_infinite_eq (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (j : ℕ) :
    {k | throwbackSequence X k = X j}.Infinite

/-- For a sequence `X` of distinct positive integers and `n ≥ 1`,
`M(n) ≤ M(n - 1) + M(N(n)) + 1`, where `M(n)` is the maximal number of throwbacks needed for
the term at position `n` of any `τᵐ(X)` to become leader and `N(n)` is the number of terms of
`X` below `n`. Stated for upper bounds: if every term at position `n - 1` (of any `τᵐ(X)`)
becomes leader within `a` steps and every term at position `N(n)` within `b` steps, then every
term at position `n` becomes leader within `a + b + 1` steps.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 3 (`jis-2025-25.5.1-lem-3`). -/
public theorem_wanted throwback_leader_time_le (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (n : ℕ) (hn : 0 < n) (a b : ℕ)
    (ha : ∀ m, ∃ k ≤ a, throwbackSequence X (m + k) = ((throwback id)^[m] X) (n - 1))
    (hb : ∀ m, ∃ k ≤ b,
      throwbackSequence X (m + k) = ((throwback id)^[m] X) (Set.ncard {i | X i < n})) :
    ∀ m, ∃ k ≤ a + b + 1, throwbackSequence X (m + k) = ((throwback id)^[m] X) n

open Classical in
/-- For a sequence `X` of distinct positive integers and a term `x = X j`, the limiting
frequency of `x` in `T(X)` is
`f(x) = 1 / (x - σ(x) + 1) · ∏_{w < x, w ∈ X} (w - σ(w)) / (w - σ(w) + 1)`,
where `σ(w) = #{i : X i < w}` is the index of `w` in the sorted sequence `S(X)`.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 4 (`jis-2025-25.5.1-thm-4`). -/
public theorem_wanted throwbackSequence_limiting_frequency (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (j : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ((((Finset.range N).filter fun k => throwbackSequence X k = X j).card : ℕ) : ℝ) / N)
      Filter.atTop
      (nhds (1 / ((X j : ℝ) - Set.ncard {i | X i < X j} + 1) *
        ∏ w ∈ Finset.range (X j),
          if w ∈ Set.range X then
            ((w : ℝ) - Set.ncard {i | X i < w}) / ((w : ℝ) - Set.ncard {i | X i < w} + 1)
          else 1))

/-- For a sequence `X` of distinct positive integers, every term of `X` has a nonzero limiting
frequency in `T(X)` (the limit exists and is nonzero).

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Corollary 5
(`jis-2025-25.5.1-cor-5`). -/
public theorem_wanted throwbackSequence_limiting_frequency_ne_zero (X : ℕ → ℕ)
    (hX : ∀ n, 0 < X n) (hinj : Function.Injective X) (j : ℕ) :
    ∃ c : ℝ, c ≠ 0 ∧ Filter.Tendsto
      (fun N : ℕ =>
        ((((Finset.range N).filter fun k => throwbackSequence X k = X j).card : ℕ) : ℝ) / N)
      Filter.atTop (nhds c)

/-- For an increasing sequence `X` of positive integers, every partial placement sequence
`P_n(X)` is periodic.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 6 (`jis-2025-25.5.1-lem-6`). -/
public theorem_wanted partialPlacement_periodic (X : ℕ → ℕ) (hX : StrictMono X)
    (hX0 : 0 < X 0) (n : ℕ) :
    ∃ p : ℤ, 0 < p ∧ ∀ z, partialPlacement X n (z + p) = partialPlacement X n z

/-- For an increasing sequence `X` of positive integers, the throwback sequence `T(X)` is
uniformly recurrent: every block of consecutive terms recurs with bounded gaps.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 7 (`jis-2025-25.5.1-thm-7`). -/
public theorem_wanted throwbackSequence_uniformly_recurrent (X : ℕ → ℕ) (hX : StrictMono X)
    (hX0 : 0 < X 0) (i L : ℕ) :
    ∃ G, ∀ m, ∃ j, m ≤ j ∧ j ≤ m + G ∧
      ∀ t < L, throwbackSequence X (j + t) = throwbackSequence X (i + t)

/-- For an increasing sequence `X` of positive integers, minimal complete blocks of `P_n(X)`
correspond bijectively to configurations of `x₀, …, x_n` in the sequences `τᵏ(X)`, `k ≥ 0`:
the minimal complete block starting at position `k` (the shortest block containing every
`x_i`, `i ≤ n`) determines and is determined by the positions of `x₀, …, x_n` in `τᵏ(X)`, and
every minimal complete block (at any position in `ℤ`) is one starting at some `k ≥ 0`.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 8 (`jis-2025-25.5.1-lem-8`). -/
public theorem_wanted partialPlacement_minimal_complete_blocks_iff_configurations
    (X : ℕ → ℕ) (hX : StrictMono X) (hX0 : 0 < X 0) (n : ℕ) :
    let len : ℤ → ℕ := fun z =>
      sInf {L | ∀ i ≤ n, ∃ t < L, partialPlacement X n (z + t) = some (X i)}
    let block : ℤ → List (Option ℕ) := fun z =>
      (List.range (len z)).map fun t => partialPlacement X n (z + t)
    (∀ k l : ℕ, block k = block l ↔
      ∀ i ≤ n, ∀ p, (((throwback id)^[k] X) p = X i ↔ ((throwback id)^[l] X) p = X i)) ∧
      ∀ z : ℤ, ∃ k : ℕ, block z = block k

/-- Perfect mixing: for `X = (m, m + 1, m + 2, …)` with `m ≥ 1`, the configurations (positions)
of the first `n + 1` terms `m, …, m + n` in `τᵏ(X)` are pairwise distinct for
`0 ≤ k < (m + 1)^(n + 1)`, and `τ^((m + 1)^(n + 1))` returns them to their original positions.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 9 (`jis-2025-25.5.1-thm-9`). -/
public theorem_wanted throwback_consecutive_perfect_mixing (m n : ℕ) (hm : 0 < m) :
    let Y : ℕ → ℕ → ℕ := fun k => (throwback id)^[k] (fun i => m + i)
    (∀ i ≤ n, ∀ p, (Y ((m + 1) ^ (n + 1)) p = m + i ↔ Y 0 p = m + i)) ∧
      ∀ k l, k < l → l < (m + 1) ^ (n + 1) →
        ¬ ∀ i ≤ n, ∀ p, (Y k p = m + i ↔ Y l p = m + i)

end

end MetaMathlibExt
