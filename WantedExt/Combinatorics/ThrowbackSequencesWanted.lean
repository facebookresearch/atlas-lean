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
public theorem_wanted throwback_final_position_or_frequently_leader (X : ℕ → ℕ)
    (hX : ∀ n, 0 < X n) (j : ℕ) :
    (∃ p, 0 < p ∧ ∃ N, ∀ k ≥ N, ((throwback X)^[k] id) p = j) ∨
      {k | ((throwback X)^[k] id) 0 = j}.Infinite

/-- **Every term recurs in the throwback sequence.** Let $X = (x_0, x_1, \dots)$ be a sequence of
pairwise distinct positive integers, and let $T(X) = (t_0, t_1, \dots)$ be its throwback
sequence. Then every term $x_j$ of $X$ appears infinitely often in $T(X)$: there are infinitely
many $k$ with $t_k = x_j$.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 2 (`jis-2025-25.5.1-thm-2`). -/
public theorem_wanted throwbackSequence_infinite_eq (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (j : ℕ) :
    {k | throwbackSequence X k = X j}.Infinite

/-- **Recursive bound on the time to become leader.** Let $X = (x_0, x_1, \dots)$ be a sequence
of pairwise distinct positive integers, with positions numbered from $0$, the leader being at
position $0$. Let $\tau$ be the throwback and $T(X) = (t_0, t_1, \dots)$ the throwback
sequence, so $t_k$ is the leader of $\tau^k(X)$. Let $n \ge 1$, and let $N$ be the number of
indices $i$ with $x_i < n$. Suppose $a$ and $b$ are natural numbers such that for every
$m \ge 0$, the term at position $n - 1$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le a$, and
the term at position $N$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le b$. Then for every
$m \ge 0$, the term at position $n$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le a + b + 1$.

This is the bound $M(n) \le M(n - 1) + M(N) + 1$ of the source, stated for upper bounds, where
$M(n)$ is the largest number of throwbacks the term at position $n$ of any $\tau^m(X)$ needs to
become leader.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 3 (`jis-2025-25.5.1-lem-3`). -/
public theorem_wanted throwback_leader_time_le (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (n : ℕ) (hn : 0 < n) (a b : ℕ)
    (ha : ∀ m, ∃ k ≤ a, throwbackSequence X (m + k) = ((throwback id)^[m] X) (n - 1))
    (hb : ∀ m, ∃ k ≤ b,
      throwbackSequence X (m + k) = ((throwback id)^[m] X) (Set.ncard {i | X i < n})) :
    ∀ m, ∃ k ≤ a + b + 1, throwbackSequence X (m + k) = ((throwback id)^[m] X) n

open Classical in
/-- **Limiting frequencies in throwback sequences.** Let $X = (x_0, x_1, \dots)$ be a sequence of
pairwise distinct positive integers with throwback sequence $T(X) = (t_0, t_1, \dots)$, and for a
natural number $w$ let $\sigma(w)$ be the number of indices $i$ with $x_i < w$. Then for every
index $j$, writing $x = x_j$, the number of $k < N$ with $t_k = x$, divided by $N$, converges as
$N \to \infty$ to
$$f(x) = \frac{1}{x - \sigma(x) + 1} \prod_{w} \frac{w - \sigma(w)}{w - \sigma(w) + 1},$$
where the product runs over the values $w < x$ taken by $X$.

For a term $w$ of $X$, $\sigma(w)$ is the index of $w$ in the increasing rearrangement of $X$.

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

/-- **Every term has a nonzero limiting frequency.** Let $X = (x_0, x_1, \dots)$ be a sequence of
pairwise distinct positive integers, and let $T(X) = (t_0, t_1, \dots)$ be its throwback
sequence. Then for every $j$, the proportion $\#\{k < N : t_k = x_j\} / N$ of terms equal to
$x_j$ among the first $N$ terms of $T(X)$ converges, as $N \to \infty$, to a nonzero real number.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Corollary 5
(`jis-2025-25.5.1-cor-5`). -/
public theorem_wanted throwbackSequence_limiting_frequency_ne_zero (X : ℕ → ℕ)
    (hX : ∀ n, 0 < X n) (hinj : Function.Injective X) (j : ℕ) :
    ∃ c : ℝ, c ≠ 0 ∧ Filter.Tendsto
      (fun N : ℕ =>
        ((((Finset.range N).filter fun k => throwbackSequence X k = X j).card : ℕ) : ℝ) / N)
      Filter.atTop (nhds c)

/-- **Partial placement sequences are periodic.** Let $X = (x_0, x_1, \dots)$ be a strictly
increasing sequence of positive integers and let $n \ge 0$. Then the partial placement sequence
$P_n(X)$ is periodic: there is an integer $p > 0$ such that for every position
$z \in \mathbb{Z}$, the positions $z + p$ and $z$ of $P_n(X)$ are either both empty or hold the
same term.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 6 (`jis-2025-25.5.1-lem-6`). -/
public theorem_wanted partialPlacement_periodic (X : ℕ → ℕ) (hX : StrictMono X)
    (hX0 : 0 < X 0) (n : ℕ) :
    ∃ p : ℤ, 0 < p ∧ ∀ z, partialPlacement X n (z + p) = partialPlacement X n z

/-- **Throwback sequences of increasing sequences are uniformly recurrent.** Let
$X = (x_0, x_1, \dots)$ be a strictly increasing sequence of positive integers with throwback
sequence $T(X) = (t_0, t_1, \dots)$. Then every block of consecutive terms of $T(X)$ recurs with
bounded gaps: for all natural numbers $i$ and $L$ there is a natural number $G$ such that for
every natural number $m$ there is an index $j$ with $m \le j \le m + G$ and $t_{j+s} = t_{i+s}$
for all $s < L$.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 7 (`jis-2025-25.5.1-thm-7`). -/
public theorem_wanted throwbackSequence_uniformly_recurrent (X : ℕ → ℕ) (hX : StrictMono X)
    (hX0 : 0 < X 0) (i L : ℕ) :
    ∃ G, ∀ m, ∃ j, m ≤ j ∧ j ≤ m + G ∧
      ∀ t < L, throwbackSequence X (j + t) = throwbackSequence X (i + t)

/-- **Minimal complete blocks of partial placements match configurations.** Let
$X = (x_0, x_1, \dots)$ be a strictly increasing sequence of positive integers, let $\tau$ be
the throwback, let $n \ge 0$, and write $P_n(X)_z$ for the entry, possibly empty, of the
partial placement sequence $P_n(X)$ at position $z \in \mathbb{Z}$. The minimal complete block
at $z$ is the word $P_n(X)_z, P_n(X)_{z+1}, \dots, P_n(X)_{z+L-1}$, empty positions included,
where $L$ is the least length for which these positions contain every $x_i$ with $i \le n$
($L = 0$ if there is no such length). Then for all natural numbers $k$ and $l$, the minimal
complete blocks at $k$ and at $l$ are equal if and only if each of $x_0, \dots, x_n$ occupies
the same positions in $\tau^k(X)$ as in $\tau^l(X)$. Moreover, for every $z \in \mathbb{Z}$ the
minimal complete block at $z$ equals the minimal complete block at some natural number $k$.
So minimal complete blocks of $P_n(X)$ correspond bijectively to the configurations of
$x_0, \dots, x_n$ in the sequences $\tau^k(X)$ with $k \ge 0$.

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

/-- **Perfect mixing for consecutive integers.** Let $m \ge 1$ and $n \ge 0$, let
$X = (m, m + 1, m + 2, \dots)$, and let $\tau$ be the throwback. Then the positions of the terms
$m, m + 1, \dots, m + n$ in $\tau^k(X)$ are different for different $k$ with
$0 \le k < (m + 1)^{n + 1}$: for $0 \le k < l < (m + 1)^{n + 1}$, some $m + i$ with $i \le n$
occupies different positions in $\tau^k(X)$ and $\tau^l(X)$. Moreover, each of
$m, m + 1, \dots, m + n$ occupies the same positions in $\tau^{(m+1)^{n+1}}(X)$ as in $X$.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 9 (`jis-2025-25.5.1-thm-9`). -/
public theorem_wanted throwback_consecutive_perfect_mixing (m n : ℕ) (hm : 0 < m) :
    let Y : ℕ → ℕ → ℕ := fun k => (throwback id)^[k] (fun i => m + i)
    (∀ i ≤ n, ∀ p, (Y ((m + 1) ^ (n + 1)) p = m + i ↔ Y 0 p = m + i)) ∧
      ∀ k l, k < l → l < (m + 1) ^ (n + 1) →
        ¬ ∀ i ≤ n, ∀ p, (Y k p = m + i ↔ Y l p = m + i)

end

end MetaMathlibExt
