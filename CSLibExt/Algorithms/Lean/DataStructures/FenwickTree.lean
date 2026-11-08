/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Fenwick trees (binary indexed trees)

A Fenwick tree over an additive commutative monoid represents a zero-indexed
array by a one-indexed stored `Array` `bit` whose entry at `j ≥ 1` is the sum of
the `lowbit j` underlying entries ending at position `j - 1`. Only `bit` is
stored at runtime; the underlying array appears solely in the specification
relation `FenwickTree.Valid`. Prefix sums walk `k, k - lowbit k, …` down to `0`
reading stored entries in constant time, with query indices past the end clamped
like `List.take`. A point update walks `i + 1, j + lowbit j, …` and adds its
delta to exactly the stored entries on that walk. Each such write is
constant-time only when the stored array is uniquely referenced; if the
original tree is retained, Lean's persistent `Array.set` may first copy the
array in linear time, so a persistent update can cost `O(n + log n)`.

## Main definitions

* `FenwickTree.lowbit` is the largest power of two dividing its input.
* `FenwickTree.build` constructs the stored interval sums from an array.
* `FenwickTree.add`, `FenwickTree.prefixSum`, and `FenwickTree.rangeSum` are the operations.
* `FenwickTree.Valid t arr` says `t` represents `arr`: every stored entry
  equals its interval sum.

## Main statements

For a tree representing `arr`, `prefixSum` at every index (including past the
end) agrees with the sum of the corresponding `List.take` of `arr`, `rangeSum`
(the one operation needing additive inverses) agrees with the sum over the
corresponding interval, and `add` moves the representation to the point-updated
array and changes prefix sums exactly past the updated position. No logarithmic
cost bound is claimed: the model carries no cost instrumentation, although the
operations follow the usual logarithmic walks over an `Array`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/--
A Fenwick tree over `α`: the one-indexed interval-sum array, with an unused
dummy entry at index `0`. The represented underlying array is not stored; see
`FenwickTree.Valid`.
-/
public structure FenwickTree (α : Type u) [AddCommMonoid α] where
  /-- The one-indexed stored interval sums, with a dummy entry at index `0`,
  backed by an `Array` for constant-time reads; writes are constant-time
  only when the array is uniquely referenced (a shared array is copied
  first). -/
  bit : Array α

namespace FenwickTree

/-- Auxiliary halving recursion for `lowbit`, structurally recursive on its fuel. -/
@[no_expose] private def lowbitAux : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, n => if n % 2 = 1 then 1 else 2 * lowbitAux fuel (n / 2)

private lemma lowbitAux_zero (n : Nat) : lowbitAux 0 n = 1 := rfl

private lemma lowbitAux_succ (fuel n : Nat) :
    lowbitAux (fuel + 1) n = if n % 2 = 1 then 1 else 2 * lowbitAux fuel (n / 2) :=
  rfl

/-- The largest power of two dividing `n`, with `lowbit 0 = 0`. -/
public def lowbit (n : Nat) : Nat :=
  if n = 0 then 0 else lowbitAux n n

private lemma lowbit_eq_aux {n : Nat} (hn : n ≠ 0) : lowbit n = lowbitAux n n :=
  ite_eq_right hn

private lemma lowbitAux_pos (fuel : Nat) (n : Nat) : 0 < lowbitAux fuel n := by
  induction fuel generalizing n with
  | zero => rw [lowbitAux_zero]; decide
  | succ fuel ih =>
      rw [lowbitAux_succ]
      by_cases h : n % 2 = 1
      · rw [ite_eq_left h]; decide
      · rw [ite_eq_right h]
        have := ih (n / 2)
        omega

private lemma lowbitAux_le (fuel : Nat) (n : Nat) (hn : 0 < n) : lowbitAux fuel n ≤ n := by
  induction fuel generalizing n with
  | zero => rw [lowbitAux_zero]; exact hn
  | succ fuel ih =>
      rw [lowbitAux_succ]
      by_cases h : n % 2 = 1
      · rw [ite_eq_left h]; exact hn
      · rw [ite_eq_right h]
        have h2 : n % 2 = 0 := by
          have := Nat.mod_lt n (by decide : 0 < 2)
          omega
        have ih' := ih (n / 2) (by omega)
        omega

private lemma lowbitAux_dvd (fuel : Nat) (n : Nat) : lowbitAux fuel n ∣ n := by
  induction fuel generalizing n with
  | zero => rw [lowbitAux_zero]; exact one_dvd n
  | succ fuel ih =>
      rw [lowbitAux_succ]
      by_cases h : n % 2 = 1
      · rw [ite_eq_left h]; exact one_dvd n
      · rw [ite_eq_right h]
        have h2 : n % 2 = 0 := by
          have := Nat.mod_lt n (by decide : 0 < 2)
          omega
        have hn : n = 2 * (n / 2) := by omega
        nth_rewrite 2 [hn]
        exact mul_dvd_mul_left 2 (ih (n / 2))

private lemma lowbitAux_two_pow (fuel : Nat) (n : Nat) : ∃ k, lowbitAux fuel n = 2 ^ k := by
  induction fuel generalizing n with
  | zero => exact ⟨0, lowbitAux_zero n⟩
  | succ fuel ih =>
      rw [lowbitAux_succ]
      by_cases h : n % 2 = 1
      · rw [ite_eq_left h]; exact ⟨0, rfl⟩
      · rw [ite_eq_right h]
        obtain ⟨k, hk⟩ := ih (n / 2)
        exact ⟨k + 1, by rw [hk, pow_succ']⟩

private lemma lowbitAux_odd (fuel : Nat) (n : Nat) (hn : 0 < n) (hlt : n < 2 ^ (fuel + 1)) :
    (n / lowbitAux fuel n) % 2 = 1 := by
  induction fuel generalizing n with
  | zero =>
      rw [lowbitAux_zero, Nat.div_one]
      have h2 : n < 2 := hlt
      have : n = 1 := by omega
      rw [this]
  | succ fuel ih =>
      rw [lowbitAux_succ]
      by_cases h : n % 2 = 1
      · rw [ite_eq_left h, Nat.div_one]; exact h
      · rw [ite_eq_right h]
        have h2 : n % 2 = 0 := by
          have := Nat.mod_lt n (by decide : 0 < 2)
          omega
        have hlt2 : n / 2 < 2 ^ (fuel + 1) := by
          have hlt' : n < 2 * 2 ^ (fuel + 1) := by
            rwa [pow_succ'] at hlt
          omega
        rw [← Nat.div_div_eq_div_mul]
        exact ih (n / 2) (by omega) hlt2

/-- `lowbit 0` is `0`. -/
public theorem lowbit_zero : lowbit 0 = 0 := by rfl

/-- `lowbit` is positive on positive inputs. -/
public theorem lowbit_pos {n : Nat} (hn : 0 < n) : 0 < lowbit n := by
  rw [lowbit_eq_aux (by omega)]
  exact lowbitAux_pos n n

/-- `lowbit n` is at most `n`. -/
public theorem lowbit_le (n : Nat) : lowbit n ≤ n := by
  cases n with
  | zero => exact Nat.le_refl 0
  | succ n =>
      rw [lowbit_eq_aux (by omega)]
      exact lowbitAux_le _ _ (by omega)

/-- `lowbit n` divides `n`. -/
public theorem lowbit_dvd {n : Nat} (hn : 0 < n) : lowbit n ∣ n := by
  rw [lowbit_eq_aux (by omega)]
  exact lowbitAux_dvd n n

/-- `lowbit n` is a power of two. -/
public theorem lowbit_two_pow {n : Nat} (hn : 0 < n) : ∃ k, lowbit n = 2 ^ k := by
  rw [lowbit_eq_aux (by omega)]
  exact lowbitAux_two_pow n n

/-- The quotient `n / lowbit n` is odd, so `lowbit n` is the largest power of two
dividing `n`. -/
public theorem lowbit_div_odd {n : Nat} (hn : 0 < n) : (n / lowbit n) % 2 = 1 := by
  rw [lowbit_eq_aux (by omega)]
  apply lowbitAux_odd n n hn
  have h := Nat.lt_two_pow_self (n := n)
  have h2 : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- If a power of two divides `n`, it is at most `lowbit n`. -/
private lemma two_pow_le_lowbit {a n : Nat} (hn : 0 < n) (h : 2 ^ a ∣ n) :
    2 ^ a ≤ lowbit n := by
  obtain ⟨m, hm⟩ := lowbit_two_pow hn
  by_contra hlt
  push Not at hlt
  have hma : m < a := by
    by_contra hle
    push Not at hle
    have hle2 : 2 ^ a ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hle
    rw [← hm] at hle2
    omega
  obtain ⟨c, hc⟩ := h
  have hq : n / lowbit n = 2 ^ (a - m) * c := by
    have hmul : lowbit n * (n / lowbit n) = lowbit n * (2 ^ (a - m) * c) := by
      rw [Nat.mul_div_cancel' (lowbit_dvd hn), hm, hc, ← Nat.mul_assoc,
        ← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hma)]
    exact Nat.mul_left_cancel (lowbit_pos hn) hmul
  have hodd := lowbit_div_odd hn
  rw [hq] at hodd
  have hdvd : 2 ∣ 2 ^ (a - m) * c :=
    Dvd.dvd.mul_right (dvd_pow_self 2 (by omega : a - m ≠ 0)) c
  obtain ⟨e, he⟩ := hdvd
  rw [he, Nat.mul_mod_right] at hodd
  exact absurd hodd (by decide)

/-- Adding `lowbit j` to `j` at least doubles the low bit. -/
private lemma two_mul_lowbit_le_lowbit_add {j : Nat} (hj : 0 < j) :
    2 * lowbit j ≤ lowbit (j + lowbit j) := by
  obtain ⟨k, hk⟩ := lowbit_two_pow hj
  have hdvd : 2 ^ (k + 1) ∣ j + lowbit j := by
    have hjeq : j = lowbit j * (j / lowbit j) :=
      (Nat.mul_div_cancel' (lowbit_dvd hj)).symm
    have hodd : (j / lowbit j) % 2 = 1 := lowbit_div_odd hj
    obtain ⟨e, he⟩ : ∃ e, j / lowbit j = 2 * e + 1 :=
      ⟨(j / lowbit j) / 2, by omega⟩
    refine ⟨e + 1, ?_⟩
    nth_rewrite 1 [hjeq]
    rw [he, hk, pow_succ']
    ring
  have h := two_pow_le_lowbit (n := j + lowbit j)
    (by have := lowbit_pos hj; omega) hdvd
  have h2 : 2 * lowbit j = 2 ^ (k + 1) := by
    rw [hk, pow_succ']
  rw [h2]
  exact h

/-- The start of the interval ending at `j + lowbit j` is no later than the start
of the interval ending at `j`. -/
private lemma sub_lowbit_add_le {j : Nat} (hj : 0 < j) :
    (j + lowbit j) - lowbit (j + lowbit j) ≤ j - lowbit j := by
  have h2 := two_mul_lowbit_le_lowbit_add hj
  have hle := lowbit_le j
  omega

private lemma add_le_of_dvd_of_lt {a b p : Nat} (ha : p ∣ a) (hb : p ∣ b)
    (hlt : a < b) : a + p ≤ b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  by_cases hp : p = 0
  · subst hp
    simp at hlt
  · have hxy : x < y := by
      by_contra hle
      push Not at hle
      have hle2 : p * y ≤ p * x := Nat.mul_le_mul (Nat.le_refl p) hle
      omega
    calc p * x + p = p * (x + 1) := by ring
      _ ≤ p * y := Nat.mul_le_mul (Nat.le_refl p) hxy

/-- One Fenwick update step from `s` does not overshoot any `x > s` whose
interval starts before `s`. -/
private lemma add_lowbit_le_of_sub_lowbit_lt {s x : Nat} (hs : 0 < s) (hx : 0 < x)
    (hlt : s < x) (hcover : x - lowbit x < s) : s + lowbit s ≤ x := by
  by_contra hgt
  push Not at hgt
  obtain ⟨k, hk⟩ := lowbit_two_pow hs
  obtain ⟨m, hm⟩ := lowbit_two_pow hx
  have hdvdS : ∀ a : Nat, a ≤ k → 2 ^ a ∣ s := by
    intro a ha
    exact (pow_dvd_pow 2 ha).trans (hk ▸ lowbit_dvd hs)
  have hdvdX : ∀ a : Nat, a ≤ m → 2 ^ a ∣ x := by
    intro a ha
    exact (pow_dvd_pow 2 ha).trans (hm ▸ lowbit_dvd hx)
  by_cases hmk : m ≤ k
  · have hle : s + 2 ^ m ≤ x :=
      add_le_of_dvd_of_lt (hdvdS m hmk) (hdvdX m (Nat.le_refl m)) hlt
    have hle2 : s ≤ x - lowbit x := by
      rw [hm]
      omega
    omega
  · have hmk' : k < m := by omega
    have hle : s + 2 ^ k ≤ x :=
      add_le_of_dvd_of_lt (hdvdS k (Nat.le_refl k))
        (hdvdX k (Nat.le_of_lt hmk')) hlt
    rw [← hk] at hle
    omega

private lemma mem_range'_one {s n m : Nat} :
    m ∈ List.range' s n ↔ s ≤ m ∧ m < s + n := by
  rw [List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [Nat.one_mul]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨m - s, by omega, by simp; omega⟩

private lemma getD_range_map {α : Type u} (f : Nat → α) (n i : Nat) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

private lemma getD_cons_succ {α : Type u} (x : α) (l : List α) (i : Nat) (d : α) :
    (x :: l).getD (i + 1) d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD]

private lemma take_sum_eq {α : Type u} [AddCommMonoid α] (a : List α) (k : Nat) :
    (a.take k).sum = ((List.range k).map (fun i => a.getD i 0)).sum := by
  induction a generalizing k with
  | nil =>
      simp
  | cons x a ih =>
      cases k with
      | zero => rfl
      | succ k =>
          show (x :: a.take k).sum = _
          rw [List.sum_cons, ih k, List.range_succ_eq_map, List.map_cons, List.map_map,
            List.sum_cons]
          simp only [List.getD_cons_zero]
          congr 1

private lemma range_sum_split {α : Type u} [AddCommMonoid α] (a : List α) {m k : Nat}
    (h : m ≤ k) :
    ((List.range k).map (fun i => a.getD i 0)).sum =
      ((List.range m).map (fun i => a.getD i 0)).sum +
        ((List.range' m (k - m)).map (fun i => a.getD i 0)).sum := by
  have hsplit : List.range' 0 m ++ List.range' m (k - m) = List.range k := by
    rw [List.range_eq_range']
    have happ := List.range'_append (s := 0) (m := m) (n := k - m) (step := 1)
    simpa [Nat.add_sub_cancel' h] using happ
  rw [← hsplit, List.map_append, List.sum_append, List.range_eq_range']

private lemma getD_set {α : Type u} (a : List α) {i : Nat} (hi : i < a.length) (v : α)
    (x : Nat) (d : α) : (a.set i v).getD x d = if x = i then v else a.getD x d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : x = i
  · subst h
    simp [hi]
  · simp [h, Ne.symm h]

private lemma sum_ite_eq {α : Type u} [AddCommMonoid α] (L : List Nat) (hL : L.Nodup)
    (i : Nat) (δ : α) :
    (L.map (fun x => if x = i then δ else 0)).sum = if i ∈ L then δ else 0 := by
  revert hL
  induction L with
  | nil =>
      intro _
      simp
  | cons y L ih =>
      intro hL
      obtain ⟨hyn, hLn⟩ := List.nodup_cons.mp hL
      rw [List.map_cons, List.sum_cons, ih hLn]
      by_cases hy : y = i
      · subst hy
        simp [hyn]
      · have hi : i ≠ y := fun e => hy e.symm
        simp [hy, hi]

private lemma sum_map_getD_set {α : Type u} [AddCommMonoid α] (a : List α) (L : List Nat)
    (hL : L.Nodup) {i : Nat} (hi : i < a.length) (δ : α) :
    (L.map (fun x => (a.set i (a.getD i 0 + δ)).getD x 0)).sum =
      (L.map (fun x => a.getD x 0)).sum + (if i ∈ L then δ else 0) := by
  have hpoint : (fun x => (a.set i (a.getD i 0 + δ)).getD x 0) =
      (fun x => a.getD x 0 + (if x = i then δ else 0)) := by
    funext x
    rw [getD_set a hi]
    by_cases h : x = i <;> simp [h]
  rw [hpoint, List.sum_map_add, sum_ite_eq L hL i δ]

/-- The interval sum stored at one-indexed position `j`: the sum of the
`lowbit j` entries of `arr` ending at position `j - 1`, with entries past the end
reading as `0`. -/
@[expose] public def blockSum {α : Type u} [AddCommMonoid α] (arr : List α) (j : Nat) : α :=
  ((List.range' (j - lowbit j) (lowbit j)).map (fun i => arr.getD i 0)).sum

/-- Array-backed interval sum: like `blockSum`, but reads through an `Array`
in constant time per entry instead of traversing a `List` per lookup. This
is the version used by `build`, so construction takes `O(n log n)` reads
rather than quadratic list indexing. -/
@[expose] public def blockSumArray {α : Type u} [AddCommMonoid α]
    (arr : Array α) (j : Nat) : α :=
  ((List.range' (j - lowbit j) (lowbit j)).map (fun i => arr.getD i 0)).sum

private lemma blockSum_set {α : Type u} [AddCommMonoid α] (a : List α) {i : Nat}
    (hi : i < a.length) (δ : α) (j : Nat) :
    blockSum (a.set i (a.getD i 0 + δ)) j =
      blockSum a j + (if j - lowbit j ≤ i ∧ i < j then δ else 0) := by
  unfold blockSum
  rw [sum_map_getD_set _ _ (List.nodup_range' (step := 1)) hi]
  congr 1
  have hmem : i ∈ List.range' (j - lowbit j) (lowbit j) ↔
      (j - lowbit j ≤ i ∧ i < j) := by
    rw [mem_range'_one, Nat.sub_add_cancel (lowbit_le j)]
  by_cases hc : j - lowbit j ≤ i ∧ i < j
  · rw [ite_eq_left hc, ite_eq_left (hmem.mpr hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hmem.mp h))]

private lemma take_sum_set {α : Type u} [AddCommMonoid α] (a : List α) {i : Nat}
    (hi : i < a.length) (δ : α) (k : Nat) :
    ((a.set i (a.getD i 0 + δ)).take k).sum =
      (a.take k).sum + (if i < k then δ else 0) := by
  rw [take_sum_eq, take_sum_eq, sum_map_getD_set _ _ List.nodup_range hi]
  by_cases hk : i < k
  · rw [ite_eq_left hk, ite_eq_left (List.mem_range.mpr hk)]
  · rw [ite_eq_right hk, ite_eq_right (fun h => hk (List.mem_range.mp h))]
private lemma array_getD_set {α : Type u} (a : Array α) {i : Nat} (h : i < a.size)
    (v : α) (j : Nat) (d : α) :
    (a.set i v h).getD j d = if j = i then v else a.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_set h]
  by_cases hji : j = i
  · simp [hji]
  · simp [hji, show i ≠ j from fun e => hji e.symm]

private lemma array_getD_toArray {α : Type u} (l : List α) (i : Nat) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_toArray]

/-- The tree represents `arr`: the stored array has one dummy entry plus one
entry per underlying element, and every stored entry equals its interval sum.
The underlying array itself is not stored at runtime; it appears only in this
specification relation. -/
@[expose] public def Valid {α : Type u} [AddCommMonoid α] (t : FenwickTree α)
    (arr : List α) : Prop :=
  t.bit.size = arr.length + 1 ∧
    ∀ j, 1 ≤ j → j ≤ arr.length → t.bit.getD j 0 = blockSum arr j

/-- The number of underlying elements, read off the stored array in constant
time. -/
public def size {α : Type u} [AddCommMonoid α] (t : FenwickTree α) : Nat :=
  t.bit.size - 1

/-- A tree representing `arr` has size `arr.length`. -/
public theorem size_eq_length_of_valid {α : Type u} [AddCommMonoid α]
    {t : FenwickTree α} {arr : List α} (hv : Valid t arr) :
    t.size = arr.length := by
  show t.bit.size - 1 = arr.length
  rw [hv.1]
  exact Nat.add_sub_cancel _ _

/-- Build a Fenwick tree representing the given array by computing every
interval sum. The input is converted to an `Array` once, so each entry read
is constant-time and construction is `O(n log n)`. -/
public def build {α : Type u} [AddCommMonoid α] (arr : List α) : FenwickTree α where
  bit :=
    let a := arr.toArray
    (0 :: (List.range arr.length).map
      (fun i => blockSumArray a (i + 1))).toArray

/-- The size of a built tree is the length of its input. -/
public theorem size_build {α : Type u} [AddCommMonoid α] (arr : List α) :
    (build arr).size = arr.length := by
  show (build arr).bit.size - 1 = arr.length
  simp [build]

/-- The array-backed interval sum agrees with the list specification. -/
private lemma blockSumArray_toArray {α : Type u} [AddCommMonoid α]
    (arr : List α) (j : Nat) :
    blockSumArray arr.toArray j = blockSum arr j := by
  unfold blockSumArray blockSum
  congr 1
  apply List.map_congr_left
  intro i _
  exact array_getD_toArray arr i 0

/-- `build` produces a tree representing its input. -/
public theorem valid_build {α : Type u} [AddCommMonoid α] (arr : List α) :
    Valid (build arr) arr := by
  refine ⟨by simp [build], ?_⟩
  intro j hj1 hj2
  show (build arr).bit.getD j 0 = blockSum arr j
  rw [show (build arr).bit =
      (0 :: (List.range arr.length).map
        (fun i => blockSumArray arr.toArray (i + 1))).toArray from
    rfl, array_getD_toArray]
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [getD_cons_succ, getD_range_map _ _ _ _ (by omega : j < arr.length),
    blockSumArray_toArray]

/-- Fuelled prefix-sum walk from `k` down to `0`, stepping by `lowbit`; the fuel
is the structural argument. Reads use `Array.getD`, which is constant time. -/
@[no_expose] private def prefixAux {α : Type u} [AddCommMonoid α] (bit : Array α) :
    Nat → Nat → α
  | 0, _ => 0
  | fuel + 1, k => if k = 0 then 0 else bit.getD k 0 + prefixAux bit fuel (k - lowbit k)

private lemma prefixAux_succ {α : Type u} [AddCommMonoid α] (bit : Array α)
    (fuel k : Nat) :
    prefixAux bit (fuel + 1) k =
      if k = 0 then 0 else bit.getD k 0 + prefixAux bit fuel (k - lowbit k) :=
  rfl

private lemma prefixAux_eq {α : Type u} [AddCommMonoid α] (bit : Array α)
    (arr : List α)
    (hsum : ∀ j, 1 ≤ j → j ≤ arr.length → bit.getD j 0 = blockSum arr j)
    (fuel : Nat) :
    ∀ k : Nat, k ≤ fuel → k ≤ arr.length →
      prefixAux bit fuel k = (arr.take k).sum := by
  induction fuel with
  | zero =>
      intro k hk _
      have hk0 : k = 0 := by omega
      subst hk0
      rfl
  | succ fuel ih =>
      intro k hkf hklen
      rw [prefixAux_succ]
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · rw [ite_eq_right hk0, hsum k (by omega) hklen]
        have hlt : k - lowbit k ≤ fuel := by
          have hpos := lowbit_pos (show 0 < k by omega)
          omega
        rw [ih (k - lowbit k) hlt (by omega), take_sum_eq, take_sum_eq,
          range_sum_split arr (Nat.sub_le k (lowbit k)),
          Nat.sub_sub_self (lowbit_le k)]
        exact add_comm _ _

/-- The sum of the first `k` underlying entries, computed by walking the stored
entries at `k, k - lowbit k, …` down to `0`. Indices past the end are clamped:
querying at `k` greater than the size sums the whole represented array, just
like `List.take`. -/
public def prefixSum {α : Type u} [AddCommMonoid α] (t : FenwickTree α) (k : Nat) :
    α :=
  prefixAux t.bit (min k t.size) (min k t.size)

/-- The empty prefix sums to zero. -/
@[simp]
public theorem prefixSum_zero {α : Type u} [AddCommMonoid α] (t : FenwickTree α) :
    prefixSum t 0 = 0 := by
  rfl

/-- For every `k`, including values past the end, `prefixSum` agrees with the
sum of the corresponding `List.take` of the represented array. -/
public theorem prefixSum_eq_take_sum {α : Type u} [AddCommMonoid α]
    (t : FenwickTree α) {arr : List α} (hv : Valid t arr) (k : Nat) :
    prefixSum t k = (arr.take k).sum := by
  obtain ⟨hlen, hsum⟩ := hv
  have hsize : t.size = arr.length :=
    size_eq_length_of_valid ⟨hlen, hsum⟩
  show prefixAux t.bit (min k t.size) (min k t.size) = (arr.take k).sum
  rw [hsize, prefixAux_eq t.bit arr hsum _ _ (Nat.le_refl _) (Nat.min_le_right _ _)]
  congr 1
  by_cases h : k ≤ arr.length
  · rw [Nat.min_eq_left h]
  · have hle : arr.length ≤ k := by omega
    rw [Nat.min_eq_right hle, List.take_of_length_le (Nat.le_refl _),
      List.take_of_length_le hle]

/-- Prefix sums of a freshly built tree agree with the input array's prefix
sums at every index. -/
public theorem prefixSum_build {α : Type u} [AddCommMonoid α] (arr : List α)
    (k : Nat) : prefixSum (build arr) k = (arr.take k).sum :=
  prefixSum_eq_take_sum (build arr) (valid_build arr) k

/-- The indices visited by a point update at one-based position `j` in a tree
of size `n`: `j, j + lowbit j, …` while at most `n`. The first `Nat` argument
after `n` is fuel for structural recursion. -/
@[no_expose] private def walk (n : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, j => if j ≤ n then j :: walk n fuel (j + lowbit j) else []

private lemma walk_zero (n j : Nat) : walk n 0 j = [] := rfl

private lemma walk_succ (n fuel j : Nat) :
    walk n (fuel + 1) j = if j ≤ n then j :: walk n fuel (j + lowbit j) else [] :=
  rfl

private lemma walk_eq_nil_of_lt {n j : Nat} (h : n < j) (fuel : Nat) :
    walk n fuel j = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [walk_succ, ite_eq_right (by omega)]

/-- Every visited index `x` lies between the start and `n`, and the interval
ending at `x` starts no later than the interval ending at the start. -/
private lemma mem_walk {n : Nat} :
    ∀ {fuel s x : Nat}, 0 < s → x ∈ walk n fuel s →
      s ≤ x ∧ x ≤ n ∧ x - lowbit x ≤ s - lowbit s
  | 0, s, x, _, h => by simp [walk_zero] at h
  | fuel + 1, s, x, hs, h => by
      rw [walk_succ] at h
      by_cases hsn : s ≤ n
      · rw [ite_eq_left hsn, List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨le_rfl, hsn, le_rfl⟩
        · have hs' : 0 < s + lowbit s := by
            have := lowbit_pos hs
            omega
          obtain ⟨h1, h2, h3⟩ := mem_walk hs' h
          exact ⟨by omega, h2, Nat.le_trans h3 (sub_lowbit_add_le hs)⟩
      · rw [ite_eq_right hsn] at h
        simp at h

/-- Every index in `(s, n]` whose interval starts before `s` is visited,
provided the fuel exceeds the remaining distance. -/
private lemma mem_walk_of {n : Nat} :
    ∀ {fuel s x : Nat}, 0 < s → s ≤ x → x ≤ n → x - lowbit x < s →
      x - s < fuel → x ∈ walk n fuel s
  | 0, s, x, _, _, _, _, h => by omega
  | fuel + 1, s, x, hs, hsx, hxn, hcover, hfuel => by
      rw [walk_succ, ite_eq_left (show s ≤ n by omega), List.mem_cons]
      by_cases hseq : s = x
      · exact Or.inl hseq.symm
      · have hlt : s < x := by omega
        have hs' : 0 < s + lowbit s := by
          have := lowbit_pos hs
          omega
        have hstep : s + lowbit s ≤ x :=
          add_lowbit_le_of_sub_lowbit_lt hs (by omega) hlt hcover
        have hpos := lowbit_pos hs
        exact Or.inr (mem_walk_of hs' hstep hxn (by omega) (by omega))

private lemma walk_nodup {n : Nat} :
    ∀ {fuel s : Nat}, 0 < s → (walk n fuel s).Nodup
  | 0, s, _ => by simp [walk_zero]
  | fuel + 1, s, hs => by
      rw [walk_succ]
      by_cases hsn : s ≤ n
      · rw [ite_eq_left hsn, List.nodup_cons]
        have hs' : 0 < s + lowbit s := by
          have := lowbit_pos hs
          omega
        refine ⟨fun hmem => ?_, walk_nodup hs'⟩
        have hge := (mem_walk hs' hmem).1
        have := lowbit_pos hs
        omega
      · rw [ite_eq_right hsn]
        exact List.nodup_nil

/-- Add `δ` to the stored entry at `j`, if in bounds. -/
@[no_expose] private def addAt {α : Type u} [AddCommMonoid α] (bit : Array α)
    (j : Nat) (δ : α) : Array α :=
  if h : j < bit.size then bit.set j (bit.getD j 0 + δ) h else bit

private lemma addAt_size {α : Type u} [AddCommMonoid α] (bit : Array α)
    (j : Nat) (δ : α) : (addAt bit j δ).size = bit.size := by
  by_cases h : j < bit.size
  · simp only [addAt, dite_eq_left h]
    exact Array.size_set h
  · simp only [addAt, dite_eq_right h]

private lemma foldl_addAt_size {α : Type u} [AddCommMonoid α] (bit : Array α)
    (l : List Nat) (δ : α) :
    (l.foldl (fun b j => addAt b j δ) bit).size = bit.size := by
  induction l generalizing bit with
  | nil => rfl
  | cons j l ih => simp only [List.foldl_cons, ih, addAt_size]

private lemma getD_addAt {α : Type u} [AddCommMonoid α] (bit : Array α)
    {j : Nat} (hj : j < bit.size) (δ : α) (x : Nat) :
    (addAt bit j δ).getD x 0 = bit.getD x 0 + (if x = j then δ else 0) := by
  simp only [addAt, dite_eq_left hj]
  rw [array_getD_set bit hj]
  by_cases h : x = j
  · rw [ite_eq_left h, ite_eq_left h, h]
    exact congrArg (· + δ) (dite_eq_left hj).symm
  · rw [ite_eq_right h, ite_eq_right h, add_zero]

private lemma getD_foldl_addAt {α : Type u} [AddCommMonoid α] (bit : Array α)
    (l : List Nat) (hl : l.Nodup) (hsz : ∀ j ∈ l, j < bit.size) (δ : α)
    (x : Nat) :
    (l.foldl (fun b j => addAt b j δ) bit).getD x 0 =
      bit.getD x 0 + (if x ∈ l then δ else 0) := by
  induction l generalizing bit with
  | nil => simp
  | cons j l ih =>
      obtain ⟨hjn, hln⟩ := List.nodup_cons.mp hl
      simp only [List.foldl_cons]
      rw [ih _ hln (fun y hy => by
        rw [addAt_size]
        exact hsz y (List.mem_cons_of_mem j hy)),
        getD_addAt bit (hsz j List.mem_cons_self) δ x]
      by_cases hx : x = j
      · subst hx
        simp [hjn]
      · simp [List.mem_cons, hx]

/--
Add `δ` to underlying entry `i` by walking `i + 1, j + lowbit j, …` and adding
`δ` to exactly those stored entries; each write is constant-time only when
the stored array is uniquely referenced, since a shared array is copied by
the first persistent `Array.set`. An out-of-range
`i` visits no index and leaves the tree unchanged. The walk is fuelled by the
size, which always suffices because visited indices strictly increase.
-/
public def add {α : Type u} [AddCommMonoid α] (t : FenwickTree α) (i : Nat)
    (δ : α) : FenwickTree α where
  bit := (walk t.size t.size (i + 1)).foldl (fun b j => addAt b j δ) t.bit

/-- A point update at an out-of-range position is the identity. -/
public theorem add_eq_self_of_le {α : Type u} [AddCommMonoid α]
    (t : FenwickTree α) {i : Nat} (hi : t.size ≤ i) (δ : α) :
    add t i δ = t := by
  cases t with
  | mk bit =>
      show (⟨(walk (FenwickTree.mk bit).size (FenwickTree.mk bit).size
          (i + 1)).foldl (fun b j => addAt b j δ) bit⟩ : FenwickTree α) =
        ⟨bit⟩
      rw [walk_eq_nil_of_lt (n := (FenwickTree.mk bit).size) (by omega)]
      rfl

private lemma getD_add_of_valid {α : Type u} [AddCommMonoid α]
    {t : FenwickTree α} {arr : List α} (hv : Valid t arr) (i : Nat) (δ : α)
    {j : Nat} (_hj1 : 1 ≤ j) (hj : j ≤ arr.length) :
    (add t i δ).bit.getD j 0 =
      t.bit.getD j 0 + (if j - lowbit j ≤ i ∧ i < j then δ else 0) := by
  have hsize : t.size = arr.length := size_eq_length_of_valid hv
  have hbitSize : t.bit.size = t.size + 1 := by
    show t.bit.size = t.bit.size - 1 + 1
    have : 0 < t.bit.size := by
      have := hv.1
      omega
    omega
  have hiff : j ∈ walk t.size t.size (i + 1) ↔
      (j - lowbit j ≤ i ∧ i < j) := by
    constructor
    · intro hmem
      obtain ⟨h1, -, h3⟩ := mem_walk (by omega) hmem
      have hlt : (i + 1) - lowbit (i + 1) < i + 1 :=
        Nat.sub_lt (by omega) (lowbit_pos (by omega))
      omega
    · rintro ⟨h1, h2⟩
      exact mem_walk_of (by omega) (by omega) (by omega) (by omega) (by omega)
  show ((walk t.size t.size (i + 1)).foldl (fun b j => addAt b j δ) t.bit).getD
      j 0 = _
  rw [getD_foldl_addAt _ _ (walk_nodup (by omega)) (fun y hy => by
    obtain ⟨h1, h2, -⟩ := mem_walk (by omega) hy
    omega)]
  by_cases hc : j - lowbit j ≤ i ∧ i < j
  · rw [ite_eq_left hc, ite_eq_left (hiff.mpr hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.mp h))]

/-- Point update at an in-range position moves the representation to the
point-updated array. -/
public theorem valid_add {α : Type u} [AddCommMonoid α] {t : FenwickTree α}
    {arr : List α} (hv : Valid t arr) {i : Nat} (hi : i < arr.length) (δ : α) :
    Valid (add t i δ) (arr.set i (arr.getD i 0 + δ)) := by
  obtain ⟨hlen, hsum⟩ := hv
  refine ⟨?_, ?_⟩
  · have hsize : (add t i δ).bit.size = t.bit.size := foldl_addAt_size _ _ _
    rw [hsize, hlen, List.length_set]
  · intro j hj1 hj2
    have hjlen : j ≤ arr.length := by
      rwa [List.length_set] at hj2
    rw [getD_add_of_valid ⟨hlen, hsum⟩ i δ hj1 hjlen, hsum j hj1 hjlen,
      blockSum_set arr hi δ j]

/-- A point update changes exactly the prefix sums past the updated position,
at every query index including past-the-end ones. -/
public theorem prefixSum_add {α : Type u} [AddCommMonoid α] {t : FenwickTree α}
    {arr : List α} (hv : Valid t arr) {i : Nat} (hi : i < arr.length) (δ : α)
    (k : Nat) :
    prefixSum (add t i δ) k = prefixSum t k + (if i < k then δ else 0) := by
  rw [prefixSum_eq_take_sum _ (valid_add hv hi δ) k,
    prefixSum_eq_take_sum t hv k]
  exact take_sum_set arr hi δ k

/-- The sum of the underlying entries with indices in `[lo, hi)`, as a
difference of prefix sums. This is the one operation that needs additive
inverses. Reversed or empty ranges (`hi ≤ lo`) return `0`, matching the sum
over the empty list interval `((arr.take hi).drop lo)`. -/
public def rangeSum {α : Type u} [AddCommGroup α] (t : FenwickTree α)
    (lo hi : Nat) : α :=
  if hi ≤ lo then 0 else prefixSum t hi - prefixSum t lo

/-- `rangeSum` agrees with the sum of the represented array over `[lo, hi)`,
with both ends clamped through `List.take`. This holds for every `lo` and
`hi`: when `hi ≤ lo` both sides are `0`. -/
public theorem rangeSum_eq {α : Type u} [AddCommGroup α] {t : FenwickTree α}
    {arr : List α} (hv : Valid t arr) (lo hi : Nat) :
    rangeSum t lo hi = ((arr.take hi).drop lo).sum := by
  unfold rangeSum
  by_cases h : hi ≤ lo
  · rw [ite_eq_left h]
    have hlen : (arr.take hi).length ≤ lo := by
      rw [List.length_take]
      omega
    rw [List.drop_eq_nil_of_le hlen, List.sum_nil]
  · rw [ite_eq_right h, prefixSum_eq_take_sum t hv hi, prefixSum_eq_take_sum t hv lo]
    have hlo : lo ≤ hi := by omega
    have hsplit := congrArg List.sum (List.take_append_drop lo (arr.take hi))
    rw [List.sum_append, List.take_take, show lo ⊓ hi = lo by omega] at hsplit
    rw [← hsplit, add_comm ((arr.take lo).sum), add_sub_cancel_right]

end FenwickTree

end Cslib.Algorithms.Lean
