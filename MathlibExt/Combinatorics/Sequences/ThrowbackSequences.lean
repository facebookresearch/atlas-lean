/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Lattice.Nat

/-!
# Throwback sequences of positive integers (Darnell, Dribus)

J. Darnell and B. F. Dribus study the following operation in *Throwback Sequences of Positive
Integers*, Journal of Integer Sequences 28 (2025), Article 25.5.1.

The throwback operation moves the leader `x₀` of a sequence `X = (x₀, x₁, …)` to index `x₀`:
`τ(X) = (x₁, …, x_{x₀}, x₀, x_{x₀+1}, …)`; the throwback sequence `T(X)` lists the leaders of
`τⁿ(X)`. The special case `X = (3, 4, 5, …)` (Kozar's conjecture for OEIS A357081) is proved as
`MetaMathlibExt.kozar_throwback_recurrence`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Throwback operation.** Let $s = (s_0, s_1, s_2, \dots)$ be a sequence of elements of a set
$A$, each element $a$ carrying a weight $w(a) \in \mathbb{N}$. The throwback $\tau_w(s)$ moves the
leader $s_0$ to index $w(s_0)$, moves the entries at indices $1, \dots, w(s_0)$ one place left and
leaves later entries in place: $\tau_w(s)_i = s_{i+1}$ for $i < w(s_0)$,
$\tau_w(s)_{w(s_0)} = s_0$, and $\tau_w(s)_i = s_i$ for $i > w(s_0)$.

With $A = \mathbb{N}$ and $w$ the identity, this is the throwback $\tau$ of Darnell and Dribus on
sequences of positive integers. With $A = \mathbb{N}$, the initial arrangement $s_i = i$ and
weights $w(i) = x_i$ for a sequence $X = (x_0, x_1, \dots)$, it tracks the original index of each
term, so repeated values stay distinguishable.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Section 2. -/
public def throwback {α : Type*} (w : α → ℕ) (s : ℕ → α) : ℕ → α := fun i =>
  if i < w (s 0) then s (i + 1) else if i = w (s 0) then s 0 else s i

/-- **Throwback sequence.** For a sequence $X = (x_0, x_1, \dots)$ of natural numbers, the throwback
sequence $T(X) = (t_0, t_1, \dots)$ records the successive leaders under the throwback operation:
$t_n$ is the leader (the entry at index $0$) of $\tau^n(X)$, where $\tau$ is the throwback
operation in which each entry's weight is its own value.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Section 2. -/
public def throwbackSequence (X : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((throwback id)^[n] X) 0

/-- **Throwback of the integers from 3 on.** Let $X = (3, 4, 5, \dots)$, that is, $x_i = i + 3$.
The first five terms of its throwback $\tau(X)$ are $4, 5, 6, 3, 7$, and the first six terms of
its throwback sequence $T(X)$ are $3, 4, 5, 6, 3, 7$ (OEIS A357081).

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Table 1. -/
public theorem throwback_examples :
    (List.range 5).map (throwback id (fun i => i + 3)) = [4, 5, 6, 3, 7] ∧
      (List.range 6).map (throwbackSequence (fun i => i + 3)) = [3, 4, 5, 6, 3, 7] := by
  decide

/-- **Partial placement sequences.** Let $X = (x_0, x_1, \dots)$ be a sequence of natural
numbers; the source takes $X$ strictly increasing with positive terms. The partial placement
sequences $P_n(X)$, for $n \ge 0$, are indexed by positions $z \in \mathbb{Z}$, and each
position is either empty or holds a term of $X$. $P_0(X)$ holds $x_0$ at the multiples of
$x_0 + 1$ and is empty elsewhere. $P_{n+1}(X)$ agrees with $P_n(X)$ at the filled positions of
$P_n(X)$ and fills some of its empty (open) positions with $x_{n+1}$, as follows. Let $s$ be
the least natural number that is an open position of $P_n(X)$ ($s = 0$ if there is none), and
let $d = x_{n+1} - (n + 1) + 1 = x_{n+1} - n$, an integer. An open position $z$ of $P_n(X)$
receives $x_{n+1}$ exactly when $d$ divides the signed number of open positions of $P_n(X)$
between $s$ and $z$, where open positions in $[s, z)$ count $+1$ and those in $[z, s)$ count
$-1$; all other open positions stay empty. When $d > 0$ and $P_n(X)$ has an open position
$\ge 0$, this places $x_{n+1}$ at $s$ and then, in both directions, at every $d$-th open
position.

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

/-- **First partial placement sequence of the integers from 3 on.** Let $X = (3, 4, 5, \dots)$,
that is, $x_i = i + 3$. The partial placement sequence $P_0(X)$ holds the term $3$ at
positions $0$, $4$ and $-4$, and its positions $1$, $2$ and $3$ are empty.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Table 4. -/
public theorem partialPlacement_zero_examples :
    partialPlacement (fun i => i + 3) 0 0 = some 3 ∧
      partialPlacement (fun i => i + 3) 0 4 = some 3 ∧
      partialPlacement (fun i => i + 3) 0 (-4) = some 3 ∧
      ∀ z ∈ ({1, 2, 3} : Finset ℤ), partialPlacement (fun i => i + 3) 0 z = none := by
  simp only [partialPlacement]
  decide

namespace throwback_final_position_or_frequently_leader

/-- The leader moves strictly right, and every other entry stays put or moves left. -/
private theorem exists_next_position {α : Type*} (w : α → ℕ) (hw : ∀ a, 0 < w a)
    (s : ℕ → α) (p : ℕ) :
    ∃ q, throwback w s q = s p ∧ (q ≤ p ↔ 0 < p) := by
  cases p with
  | zero => exact ⟨w (s 0), by simp [throwback], by simp [(hw (s 0)).ne']⟩
  | succ p =>
    by_cases h : p < w (s 0)
    · exact ⟨p, by simp [throwback, h], by omega⟩
    · have hlt : w (s 0) < p + 1 := by omega
      exact ⟨p + 1, by simp [throwback, hlt.not_gt, hlt.ne'], by omega⟩

end throwback_final_position_or_frequently_leader

open throwback_final_position_or_frequently_leader in
/-- **Each term eventually settles or leads infinitely often.** Let $X = (x_0, x_1, \dots)$ be a
sequence of positive integers, with positions numbered from $0$, the leader being at position
$0$. Track the terms of $X$ by their original indices: start from the arrangement
$(0, 1, 2, \dots)$ and apply the throwback repeatedly, where the leader, with original index
$i$, moves to position $x_i$. Then for every index $j$, either there are a position $p > 0$ and
a number $N$ such that the term with original index $j$ is at position $p$ after $k$ throwbacks
for every $k \ge N$, or there are infinitely many $k$ such that this term is the leader after
$k$ throwbacks.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 1 (`jis-2025-25.5.1-lem-1`). -/
public theorem throwback_final_position_or_frequently_leader (X : ℕ → ℕ)
    (hX : ∀ n, 0 < X n) (j : ℕ) :
    (∃ p, 0 < p ∧ ∃ N, ∀ k ≥ N, ((throwback X)^[k] id) p = j) ∨
      {k | ((throwback X)^[k] id) 0 = j}.Infinite := by
  classical
  let A (k : ℕ) := (throwback X)^[k] id
  have step (k : ℕ) : A (k + 1) = throwback X (A k) := Function.iterate_succ_apply' ..
  by_cases hfin : {k | A k 0 = j}.Finite
  · obtain ⟨B, hB⟩ := hfin.bddAbove
    have occurs (k : ℕ) : ∃ p, A k p = j := by
      induction k with
      | zero => exact ⟨j, rfl⟩
      | succ k ih =>
        obtain ⟨p, hp⟩ := ih
        obtain ⟨q, hq, _⟩ := exists_next_position X hX (A k) p
        exact ⟨q, by rw [step, hq, hp]⟩
    -- Take the least position reached strictly after the bound on leader times.
    obtain ⟨q, hq⟩ := occurs (B + 1)
    obtain ⟨p, hmin⟩ := exists_minimal_of_wellFoundedLT (fun p => ∃ k > B, A k p = j)
      ⟨q, B + 1, Nat.lt_succ_self _, hq⟩
    obtain ⟨N, hN, hp⟩ := hmin.prop
    have hpos : 0 < p := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      exact hN.not_ge (hB hp)
    refine Or.inl ⟨p, hpos, N, fun k hk => ?_⟩
    change A k p = j
    induction k, hk using Nat.le_induction with
    | base => exact hp
    | succ k hk ih =>
      obtain ⟨r, hr, hmove⟩ := exists_next_position X hX (A k) p
      have hrj : A (k + 1) r = j := by rw [step, hr, ih]
      rwa [hmin.eq_of_ge ⟨k + 1, by omega, hrj⟩ (hmove.mpr hpos)]
  · exact Or.inr hfin

end

end MetaMathlibExt
