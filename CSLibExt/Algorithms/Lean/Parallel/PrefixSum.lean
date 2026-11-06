/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.GetD

/-!
# Parallel prefix sums: the Kogge-Stone (Hillis-Steele) scan

The parallel scan of Kogge and Stone (*A parallel algorithm for the efficient solution of a
general class of recurrence equations*, IEEE Trans. Computers, 1973), popularized as the
Hillis-Steele scan (*Data parallel algorithms*, CACM, 1986), computes all prefix products
`x₀ * x₁ * ⋯ * xᵢ` of a sequence in an associative monoid in `⌈log₂ n⌉` parallel rounds: in round
`k` every position `i ≥ 2 ^ k` combines its value with the value `2 ^ k` places to its left
(`koggeStone`). The order of the factors is kept, so the monoid need not be commutative.

Main results:

* `koggeStone_eq_seg`: after `k` rounds position `i` holds the product of the window of the last
  `min (i + 1) (2 ^ k)` inputs ending at `i` (`seg`).
* `koggeStone_eq_prefix`: after `K` rounds with `n ≤ 2 ^ K`, every position `i < n` holds its
  prefix product.
* `work_le` and `span`: round `k` performs `n - 2 ^ k` combinations (`roundWork`), so the scan does
  at most `n K` combinations (`work`) in `K` rounds; with `K = Nat.clog 2 n` that is
  `O(n log n)` work and `⌈log₂ n⌉` span.

## Cost model

Work-span: a round is one parallel step (span `1`) whose work is the number of monoid
multiplications it performs; reading and writing positions is free. `koggeStone` is the round
recursion used for the proofs; evaluated directly it recomputes earlier rounds (sequential cost
exponential in the number of rounds). `scanList` is the tabulated implementation, one list per
round in `O(n)` time by a lockstep traversal (`roundList`), proved equal to it
(`getD_scanList`, `getD_scanList_eq_prefix`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Parallel.PrefixSum

variable {M : Type*} [Monoid M]

/-- **Window product.** For a sequence $x : \mathbb{N} \to M$ in a monoid $M$ and
$a, b \in \mathbb{N}$, the window product is the ordered product $x_a x_{a+1} \cdots x_{b-1}$ of
the terms with indices $a \le j < b$; it is the empty product $1$ when $b \le a$. -/
def seg (x : ℕ → M) (a b : ℕ) : M := ((List.range' a (b - a)).map x).prod

/-- **Prefix product.** For a sequence $x_0, x_1, \dots$ in a monoid $M$ and a natural number $i$,
the prefix product at $i$ is $x_0 x_1 \cdots x_i$, the factors taken in increasing order of
index. -/
def prefixProd (x : ℕ → M) (i : ℕ) : M := seg x 0 (i + 1)

theorem seg_self (x : ℕ → M) (a : ℕ) : seg x a a = 1 := by simp [seg]

/-- **Products of adjacent windows.** Let $M$ be a monoid and $x : \mathbb{N} \to M$ a sequence,
and for $a, b \in \mathbb{N}$ let $x_{[a, b)}$ be the ordered product $x_a x_{a+1} \cdots x_{b-1}$
(equal to $1$ if $b \le a$). For all $a \le b \le c$, $x_{[a, b)} \, x_{[b, c)} = x_{[a, c)}$. -/
theorem seg_mul_seg (x : ℕ → M) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    seg x a b * seg x b c = seg x a c := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, c = a + d + e := ⟨c - (a + d), by omega⟩
  unfold seg
  rw [← List.prod_append, ← List.map_append, show a + d - a = d by omega,
    show a + d + e - (a + d) = e by omega, show a + d + e - a = d + e by omega,
    List.range'_append_1]

/-- **The Kogge–Stone scan.** Given a sequence $x_0, x_1, \dots$ in a monoid $M$, the value
$s_k(i)$ at position $i$ after $k$ rounds is defined by $s_0(i) = x_i$ and, for each $k$,
$s_{k+1}(i) = s_k(i - 2^k) \, s_k(i)$ if $2^k \le i$ and $s_{k+1}(i) = s_k(i)$ otherwise. -/
def koggeStone (x : ℕ → M) : ℕ → ℕ → M
  | 0, i => x i
  | k + 1, i => if 2 ^ k ≤ i then koggeStone x k (i - 2 ^ k) * koggeStone x k i
      else koggeStone x k i

/-- **What the scan holds after each round.** Let $x_0, x_1, \dots$ be a sequence in a monoid
$M$, let $k$ and $i$ be natural numbers, and let $m = \min(i + 1, 2^k)$. After $k$ rounds of the
Kogge–Stone scan, position $i$ holds the product $x_{i+1-m} \cdots x_i$ of the $m$ consecutive
inputs ending at $i$, taken in increasing order of index. -/
theorem koggeStone_eq_seg (x : ℕ → M) :
    ∀ k i, koggeStone x k i = seg x (i + 1 - min (i + 1) (2 ^ k)) (i + 1)
  | 0, i => by
      simp only [koggeStone, pow_zero, seg]
      rw [show i + 1 - min (i + 1) 1 = i by omega, show i + 1 - i = 1 by omega]
      simp
  | k + 1, i => by
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      simp only [koggeStone]
      split_ifs with h
      · rw [koggeStone_eq_seg x k (i - 2 ^ k), koggeStone_eq_seg x k i,
          show i - 2 ^ k + 1 = i + 1 - 2 ^ k by omega,
          show min (i + 1) (2 ^ k) = 2 ^ k by omega]
        rw [seg_mul_seg x (by omega) (by omega)]
        congr 1
        rw [h2]
        omega
      · rw [koggeStone_eq_seg x k i, h2,
          show min (i + 1) (2 ^ k) = i + 1 by omega, show min (i + 1) (2 * 2 ^ k) = i + 1 by omega]

/-- **The scan computes all prefix products.** Let $x_0, x_1, \dots$ be a sequence in a monoid $M$
and let $n$ and $K$ be natural numbers with $n \le 2^K$. After $K$ rounds of the Kogge–Stone scan,
every position $i < n$ holds the prefix product $x_0 x_1 \cdots x_i$. -/
theorem koggeStone_eq_prefix (x : ℕ → M) {n K : ℕ} (hn : n ≤ 2 ^ K) {i : ℕ} (hi : i < n) :
    koggeStone x K i = prefixProd x i := by
  rw [koggeStone_eq_seg, prefixProd, show min (i + 1) (2 ^ K) = i + 1 by omega, Nat.sub_self]

/-- **Work of a scan round.** The work of round $k$ on $n$ positions is $\max(n - 2^k, 0)$, the
number of positions $i < n$ with $i \ge 2^k$, each of which performs one multiplication. -/
def roundWork (n k : ℕ) : ℕ := n - 2 ^ k

/-- **The work of a round counts its combining positions.** For natural numbers $n$ and $k$, the
work of round $k$ on $n$ positions equals the number of positions $i$ with $2^k \le i < n$. -/
theorem roundWork_eq_card (n k : ℕ) :
    roundWork n k = ((Finset.range n).filter fun i => 2 ^ k ≤ i).card := by
  rw [roundWork]
  have : (Finset.range n).filter (fun i => 2 ^ k ≤ i) = Finset.Ico (2 ^ k) n := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- **Work of the Kogge–Stone scan.** The total work of $K$ rounds on $n$ positions is
$\sum_{k=0}^{K-1} \max(n - 2^k, 0)$, the sum over the rounds $k < K$ of the work
$\max(n - 2^k, 0)$ of round $k$. -/
def work (n K : ℕ) : ℕ := ∑ k ∈ Finset.range K, roundWork n k

/-- **Work bound for the Kogge–Stone scan.** For all $n, K \in \mathbb{N}$, the total work of $K$
rounds of the scan on $n$ positions is at most $nK$. -/
theorem work_le (n K : ℕ) : work n K ≤ n * K := by
  unfold work
  calc ∑ k ∈ Finset.range K, roundWork n k ≤ ∑ _k ∈ Finset.range K, n :=
        Finset.sum_le_sum fun k _ => Nat.sub_le n _
    _ = n * K := by rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range, Nat.mul_comm]

/-- **Span of the Kogge–Stone scan.** The span of $K$ rounds of the scan is $K$: each round is
one parallel step. -/
def span (K : ℕ) : ℕ := K

/-- **The scan computes all prefixes in logarithmically many rounds.** Let $x_0, x_1, \dots$ be a
sequence in a monoid $M$ and let $n$ be a natural number. After $\lceil \log_2 n \rceil$ rounds of
the Kogge–Stone scan (the least $K$ with $n \le 2^K$), every position $i < n$ holds the prefix
product $x_0 x_1 \cdots x_i$. -/
theorem koggeStone_clog_eq_prefix (x : ℕ → M) {n i : ℕ} (hi : i < n) :
    koggeStone x (Nat.clog 2 n) i = prefixProd x i :=
  koggeStone_eq_prefix x (Nat.le_pow_clog (by decide) n) hi

/-! ## A tabulated implementation -/

/-- **One round of the scan on a list.** Given a list $y_0, \dots, y_{n-1}$ in a monoid $M$ and a
natural number $k$, one round produces the list of length $n$ whose entry $i$ is
$y_{i - 2^k} \, y_i$ when $2^k \le i$ and $y_i$ when $i < 2^k$.

The list is traversed in lockstep with its own suffix starting at position $2^k$, so a round
costs $O(n)$. -/
def roundList (k : ℕ) (ys : List M) : List M :=
  ys.take (2 ^ k) ++ List.zipWith (· * ·) ys (ys.drop (2 ^ k))

/-- **Tabulated Kogge–Stone scan.** For a list $y = (y_0, \dots, y_{n-1})$ in a monoid $M$, the
list after $K$ rounds is defined by recursion on $K$: after $0$ rounds it is $y$, and after
$K + 1$ rounds it is round $K$ applied to the list after $K$ rounds. Here round $k$ sends a list
$(z_0, \dots, z_{n-1})$ to the list of length $n$ whose entry $i$ is $z_i$ for $i < 2^k$ and
$z_{i - 2^k} z_i$ for $2^k \le i < n$. -/
def scanList : ℕ → List M → List M
  | 0, ys => ys
  | K + 1, ys => roundList K (scanList K ys)

theorem length_roundList (k : ℕ) (ys : List M) : (roundList k ys).length = ys.length := by
  simp only [roundList, List.length_append, List.length_take, List.length_zipWith,
    List.length_drop]
  have := Nat.two_pow_pos k
  omega

theorem length_scanList : ∀ (K : ℕ) (ys : List M), (scanList K ys).length = ys.length
  | 0, _ => rfl
  | K + 1, ys => by rw [scanList, length_roundList, length_scanList K ys]

theorem getD_roundList (k : ℕ) (ys : List M) {i : ℕ} (hi : i < ys.length) :
    (roundList k ys).getD i 1 =
      if 2 ^ k ≤ i then ys.getD (i - 2 ^ k) 1 * ys.getD i 1 else ys.getD i 1 := by
  have hlt : (ys.take (2 ^ k)).length = min (2 ^ k) ys.length := List.length_take ..
  unfold roundList
  split_ifs with h
  · rw [List.getD_append_right _ _ _ _ (by omega), hlt, Nat.min_eq_left (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_drop,
      show 2 ^ k + (i - 2 ^ k) = i from by omega]
    rw [List.getElem?_eq_getElem (show i - 2 ^ k < ys.length by omega),
      List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getD_append _ _ _ _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, show i < 2 ^ k by omega,
      ↓reduceIte]

/-- **The tabulated scan agrees with the round recursion.** Let $x_0, \dots, x_{n-1}$ be a list of
elements of a monoid $M$, extended to a sequence by $x_j = 1$ for $j \ge n$. For every number of
rounds $K$ and every position $i < n$, entry $i$ of the list produced by $K$ rounds of the
tabulated scan equals the value at position $i$ after $K$ rounds of the Kogge–Stone scan applied
to the sequence $x$. -/
theorem getD_scanList (xs : List M) : ∀ (K i : ℕ), i < xs.length →
    (scanList K xs).getD i 1 = koggeStone (fun j => xs.getD j 1) K i
  | 0, _, _ => rfl
  | K + 1, i, hi => by
      rw [scanList, getD_roundList _ _ (by rw [length_scanList]; exact hi), koggeStone]
      split_ifs with h
      · have := Nat.two_pow_pos K
        rw [getD_scanList xs K (i - 2 ^ K) (by omega), getD_scanList xs K i hi]
      · rw [getD_scanList xs K i hi]

/-- **The tabulated scan computes all prefix products.** Let $x_0, \dots, x_{n-1}$ be a list of
elements of a monoid $M$ and let $K$ be a natural number with $n \le 2^K$. Then for every $i < n$,
entry $i$ of the list produced by $K$ rounds of the tabulated scan equals the prefix product
$x_0 x_1 \cdots x_i$. -/
theorem getD_scanList_eq_prefix (xs : List M) {K : ℕ} (hK : xs.length ≤ 2 ^ K) {i : ℕ}
    (hi : i < xs.length) : (scanList K xs).getD i 1 = prefixProd (fun j => xs.getD j 1) i := by
  rw [getD_scanList xs K i hi, koggeStone_eq_prefix _ hK hi]

end Cslib.Algorithms.Lean.Parallel.PrefixSum
