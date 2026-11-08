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

/-- The product `x a * x (a + 1) * ⋯ * x (b - 1)` (empty if `b ≤ a`). -/
def seg (x : ℕ → M) (a b : ℕ) : M := ((List.range' a (b - a)).map x).prod

/-- The prefix product `x 0 * ⋯ * x i`. -/
def prefixProd (x : ℕ → M) (i : ℕ) : M := seg x 0 (i + 1)

theorem seg_self (x : ℕ → M) (a : ℕ) : seg x a a = 1 := by simp [seg]

/-- Adjacent windows multiply. -/
theorem seg_mul_seg (x : ℕ → M) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    seg x a b * seg x b c = seg x a c := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, c = a + d + e := ⟨c - (a + d), by omega⟩
  unfold seg
  rw [← List.prod_append, ← List.map_append, show a + d - a = d by omega,
    show a + d + e - (a + d) = e by omega, show a + d + e - a = d + e by omega,
    List.range'_append_1]

/-- Round `k` of the scan reads the values after `k` rounds. -/
def koggeStone (x : ℕ → M) : ℕ → ℕ → M
  | 0, i => x i
  | k + 1, i => if 2 ^ k ≤ i then koggeStone x k (i - 2 ^ k) * koggeStone x k i
      else koggeStone x k i

/-- **After `k` rounds**, position `i` holds the product of the last `min (i + 1) (2 ^ k)` inputs
ending at `i`. -/
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

/-- **The scan computes all prefix products**: after `K` rounds with `n ≤ 2 ^ K`, every
position `i < n` holds `x 0 * ⋯ * x i`. -/
theorem koggeStone_eq_prefix (x : ℕ → M) {n K : ℕ} (hn : n ≤ 2 ^ K) {i : ℕ} (hi : i < n) :
    koggeStone x K i = prefixProd x i := by
  rw [koggeStone_eq_seg, prefixProd, show min (i + 1) (2 ^ K) = i + 1 by omega, Nat.sub_self]

/-- The work of round `k` on `n` positions: the positions `i ≥ 2 ^ k` combine. -/
def roundWork (n k : ℕ) : ℕ := n - 2 ^ k

/-- Round `k` combines exactly at the positions `2 ^ k ≤ i < n`. -/
theorem roundWork_eq_card (n k : ℕ) :
    roundWork n k = ((Finset.range n).filter fun i => 2 ^ k ≤ i).card := by
  rw [roundWork]
  have : (Finset.range n).filter (fun i => 2 ^ k ≤ i) = Finset.Ico (2 ^ k) n := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- The total work of `K` rounds on `n` positions. -/
def work (n K : ℕ) : ℕ := ∑ k ∈ Finset.range K, roundWork n k

/-- The scan does at most `n K` combinations. -/
theorem work_le (n K : ℕ) : work n K ≤ n * K := by
  unfold work
  calc ∑ k ∈ Finset.range K, roundWork n k ≤ ∑ _k ∈ Finset.range K, n :=
        Finset.sum_le_sum fun k _ => Nat.sub_le n _
    _ = n * K := by rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range, Nat.mul_comm]

/-- The span: `K` rounds, each one parallel step. -/
def span (K : ℕ) : ℕ := K

/-- With `K = Nat.clog 2 n` rounds the scan computes every prefix, in span `⌈log₂ n⌉`. -/
theorem koggeStone_clog_eq_prefix (x : ℕ → M) {n i : ℕ} (hi : i < n) :
    koggeStone x (Nat.clog 2 n) i = prefixProd x i :=
  koggeStone_eq_prefix x (Nat.le_pow_clog (by decide) n) hi

/-! ## A tabulated implementation -/

/-- One round on a list: position `i ≥ 2 ^ k` combines with position `i - 2 ^ k`. The list is
traversed in lockstep with its own `2 ^ k`-suffix, so a round costs `O(n)`. -/
def roundList (k : ℕ) (ys : List M) : List M :=
  ys.take (2 ^ k) ++ List.zipWith (· * ·) ys (ys.drop (2 ^ k))

/-- `K` rounds of the scan on a list, each round materialized. -/
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

/-- The list implementation agrees with the round recursion. -/
theorem getD_scanList (xs : List M) : ∀ (K i : ℕ), i < xs.length →
    (scanList K xs).getD i 1 = koggeStone (fun j => xs.getD j 1) K i
  | 0, _, _ => rfl
  | K + 1, i, hi => by
      rw [scanList, getD_roundList _ _ (by rw [length_scanList]; exact hi), koggeStone]
      split_ifs with h
      · have := Nat.two_pow_pos K
        rw [getD_scanList xs K (i - 2 ^ K) (by omega), getD_scanList xs K i hi]
      · rw [getD_scanList xs K i hi]

/-- **The tabulated scan computes all prefix products** in `K ≥ log₂ n` rounds. -/
theorem getD_scanList_eq_prefix (xs : List M) {K : ℕ} (hK : xs.length ≤ 2 ^ K) {i : ℕ}
    (hi : i < xs.length) : (scanList K xs).getD i 1 = prefixProd (fun j => xs.getD j 1) i := by
  rw [getD_scanList xs K i hi, koggeStone_eq_prefix _ hK hi]

end Cslib.Algorithms.Lean.Parallel.PrefixSum
