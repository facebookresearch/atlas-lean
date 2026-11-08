/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.FenwickTree
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Int.Basic

/-!
# Tests for the Fenwick tree API

Client examples over `Nat` (an additive commutative monoid that is not a
group) exercise `lowbit` at powers of two, empty and singleton builds,
prefix sums including past-the-end clamped queries, point updates along
the `j + lowbit j` walk, out-of-range update identity, and validity as a
representation relation. `rangeSum`, the one operation needing inverses,
is exercised over `Int`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FenwickTreeTests

open FenwickTree

private theorem le_of_dvd_of_odd {a b n : Nat} (ha : 2 ^ a ∣ n)
    (hodd : (n / 2 ^ a) % 2 = 1) (hb : 2 ^ b ∣ n) : b ≤ a := by
  by_contra hlt
  have hab : a < b := Nat.lt_of_not_ge hlt
  obtain ⟨d, hd⟩ := hb
  have hq : n / 2 ^ a = 2 ^ (b - a) * d := by
    have hmul : 2 ^ a * (n / 2 ^ a) = 2 ^ a * (2 ^ (b - a) * d) := by
      rw [Nat.mul_div_cancel' ha, hd, ← Nat.mul_assoc, ← pow_add,
        Nat.add_sub_cancel' (Nat.le_of_lt hab)]
    exact Nat.mul_left_cancel (Nat.two_pow_pos a) hmul
  have hdvd : 2 ∣ n / 2 ^ a := by
    rw [hq]
    exact Nat.dvd_mul_right_of_dvd
      (by simpa using Nat.pow_dvd_pow 2 (by omega : 1 ≤ b - a)) d
  obtain ⟨e, he⟩ := hdvd
  rw [he, Nat.mul_mod_right] at hodd
  exact absurd hodd (by decide)

/-- Pin a concrete `lowbit` value from the public characterization, since the
fuelled auxiliary behind `lowbit` is private to the production module. -/
private theorem lowbit_eq_of {n v k : Nat} (hn : 0 < n) (hv : v = 2 ^ k)
    (hdvd : v ∣ n) (hodd : (n / v) % 2 = 1) : lowbit n = v := by
  obtain ⟨m, hm⟩ := lowbit_two_pow hn
  have hmk : m ≤ k := by
    have h1 : 2 ^ k ∣ n := hv ▸ hdvd
    have h2 : (n / 2 ^ k) % 2 = 1 := hv ▸ hodd
    have h3 : 2 ^ m ∣ n := hm ▸ lowbit_dvd hn
    exact le_of_dvd_of_odd h1 h2 h3
  have hkm : k ≤ m := by
    have h1 : 2 ^ m ∣ n := hm ▸ lowbit_dvd hn
    have h2 : (n / 2 ^ m) % 2 = 1 := hm ▸ lowbit_div_odd hn
    have h3 : 2 ^ k ∣ n := hv ▸ hdvd
    exact le_of_dvd_of_odd h1 h2 h3
  rw [hm, hv, Nat.le_antisymm hkm hmk]

private theorem lowbit_one : lowbit 1 = 1 :=
  lowbit_eq_of (k := 0) (by decide) rfl (by decide) (by decide)

private theorem lowbit_two : lowbit 2 = 2 :=
  lowbit_eq_of (k := 1) (by decide) rfl (by decide) (by decide)

private theorem lowbit_three : lowbit 3 = 1 :=
  lowbit_eq_of (k := 0) (by decide) rfl (by decide) (by decide)

private theorem lowbit_four : lowbit 4 = 4 :=
  lowbit_eq_of (k := 2) (by decide) rfl (by decide) (by decide)

private theorem lowbit_six : lowbit 6 = 2 :=
  lowbit_eq_of (k := 1) (by decide) rfl (by decide) (by decide)

private theorem lowbit_eight : lowbit 8 = 8 :=
  lowbit_eq_of (k := 3) (by decide) rfl (by decide) (by decide)

private theorem lowbit_twelve : lowbit 12 = 4 :=
  lowbit_eq_of (k := 2) (by decide) rfl (by decide) (by decide)

example : lowbit 0 = 0 := lowbit_zero

example : lowbit 1 = 1 := lowbit_one

example : lowbit 2 = 2 := lowbit_two

example : lowbit 3 = 1 := lowbit_three

example : lowbit 4 = 4 := lowbit_four

example : lowbit 6 = 2 := lowbit_six

example : lowbit 8 = 8 := lowbit_eight

example : lowbit 12 = 4 := lowbit_twelve

example {n : Nat} (hn : 0 < n) : 0 < lowbit n := lowbit_pos hn

example (n : Nat) : lowbit n ≤ n := lowbit_le n

example {n : Nat} (hn : 0 < n) : lowbit n ∣ n := lowbit_dvd hn

example {n : Nat} (hn : 0 < n) : ∃ k, lowbit n = 2 ^ k := lowbit_two_pow hn

example {n : Nat} (hn : 0 < n) : (n / lowbit n) % 2 = 1 := lowbit_div_odd hn

example : blockSum [1, 2, 3, 4] 1 = 1 := by
  show ((List.range' (1 - lowbit 1) (lowbit 1)).map
    (fun i => ([1, 2, 3, 4] : List Nat).getD i 0)).sum = 1
  rw [lowbit_one]
  rfl

example : blockSum [1, 2, 3, 4] 2 = 3 := by
  show ((List.range' (2 - lowbit 2) (lowbit 2)).map
    (fun i => ([1, 2, 3, 4] : List Nat).getD i 0)).sum = 3
  rw [lowbit_two]
  rfl

example : blockSum [1, 2, 3, 4] 3 = 3 := by
  show ((List.range' (3 - lowbit 3) (lowbit 3)).map
    (fun i => ([1, 2, 3, 4] : List Nat).getD i 0)).sum = 3
  rw [lowbit_three]
  rfl

example : blockSum [1, 2, 3, 4] 4 = 10 := by
  show ((List.range' (4 - lowbit 4) (lowbit 4)).map
    (fun i => ([1, 2, 3, 4] : List Nat).getD i 0)).sum = 10
  rw [lowbit_four]
  rfl

example : (build ([] : List Nat)).size = 0 := size_build _

example : Valid (build ([] : List Nat)) [] := valid_build _

example : (build ([] : List Nat)).prefixSum 0 = 0 := by
  rw [prefixSum_build]
  rfl

example : (build ([] : List Nat)).prefixSum 5 = 0 := by
  rw [prefixSum_build]
  rfl

example : (build [5] : FenwickTree Nat).size = 1 := size_build _

example : (build [5] : FenwickTree Nat).prefixSum 0 = 0 :=
  prefixSum_zero _

example : (build [5] : FenwickTree Nat).prefixSum 1 = 5 := by
  rw [prefixSum_build]
  rfl

/-- Regression: a past-the-end query clamps to the whole array instead of
dropping stored sums (the old walk returned `0` here). -/
example : (build [1] : FenwickTree Nat).prefixSum 2 = 1 := by
  rw [prefixSum_build]
  rfl

example : (build [5] : FenwickTree Nat).prefixSum 100 = 5 := by
  rw [prefixSum_build]
  rfl

private def sample : FenwickTree Nat := build [1, 2, 3, 4]

example : sample.size = 4 := size_build _

example : Valid sample [1, 2, 3, 4] := valid_build _

example : sample.size = [1, 2, 3, 4].length :=
  size_eq_length_of_valid (valid_build _)

example : sample.bit.getD 4 0 = 10 := by
  show (build [1, 2, 3, 4]).bit.getD 4 0 = 10
  obtain ⟨-, hsum⟩ := valid_build [1, 2, 3, 4]
  rw [hsum 4 (by decide) (by decide)]
  show ((List.range' (4 - lowbit 4) (lowbit 4)).map
    (fun i => ([1, 2, 3, 4] : List Nat).getD i 0)).sum = 10
  rw [lowbit_four]
  rfl

example : sample.prefixSum 2 = 3 := by
  show (build [1, 2, 3, 4]).prefixSum 2 = 3
  rw [prefixSum_build]
  rfl

example : sample.prefixSum 4 = 10 := by
  show (build [1, 2, 3, 4]).prefixSum 4 = 10
  rw [prefixSum_build]
  rfl

example : sample.prefixSum 9 = 10 := by
  show (build [1, 2, 3, 4]).prefixSum 9 = 10
  rw [prefixSum_build]
  rfl

example (k : Nat) : sample.prefixSum k = ([1, 2, 3, 4].take k).sum :=
  prefixSum_eq_take_sum sample (valid_build _) k

example {arr : List Nat} (k : Nat) :
    (build arr).prefixSum k = (arr.take k).sum :=
  prefixSum_build arr k

/-- The represented-array API needs no additive inverses. -/
example {M : Type} [AddCommMonoid M] (arr : List M) (k : Nat) :
    (build arr).prefixSum k = (arr.take k).sum :=
  prefixSum_build arr k

example : ((build [1, 2, 3, 4]).add 0 10).prefixSum 4 = 20 := by
  rw [prefixSum_add (valid_build _) (by decide) 10 4, prefixSum_build]
  rfl

example : ((build [1, 2, 3, 4]).add 0 10).prefixSum 1 = 11 := by
  rw [prefixSum_add (valid_build _) (by decide) 10 1, prefixSum_build]
  rfl

/-- Prefix sums at or before the updated position are unchanged. -/
example : ((build [1, 2, 3, 4]).add 2 10).prefixSum 2 = 3 := by
  rw [prefixSum_add (valid_build _) (by decide) 10 2, prefixSum_build]
  rfl

example : ((build [1, 2, 3, 4]).add 2 10).prefixSum 3 = 16 := by
  rw [prefixSum_add (valid_build _) (by decide) 10 3, prefixSum_build]
  rfl

/-- Updated prefix sums clamp too. -/
example : ((build [1, 2, 3, 4]).add 3 10).prefixSum 100 = 20 := by
  rw [prefixSum_add (valid_build _) (by decide) 10 100, prefixSum_build]
  rfl

example :
    Valid ((build [1, 2, 3, 4]).add 2 10)
      ([1, 2, 3, 4].set 2 ([1, 2, 3, 4].getD 2 0 + 10)) :=
  valid_add (valid_build _) (by decide) 10

/-- An out-of-range update is the identity. -/
example : (build [1, 2]).add 5 9 = build [1, 2] := by
  apply add_eq_self_of_le
  have hsize : (build [1, 2] : FenwickTree Nat).size = 2 := size_build _
  omega

example {t : FenwickTree Nat} {arr : List Nat} (hv : Valid t arr)
    {i : Nat} (hi : i < arr.length) (δ : Nat) (k : Nat) :
    (t.add i δ).prefixSum k = t.prefixSum k + (if i < k then δ else 0) :=
  prefixSum_add hv hi δ k

private def intSample : FenwickTree Int := build [1, 2, 3, 4]

example : intSample.rangeSum 1 3 = 5 := by
  show (build ([1, 2, 3, 4] : List Int)).rangeSum 1 3 = 5
  rw [rangeSum_eq (valid_build _) _ _]
  rfl

example : intSample.rangeSum 0 4 = 10 := by
  show (build ([1, 2, 3, 4] : List Int)).rangeSum 0 4 = 10
  rw [rangeSum_eq (valid_build _) _ _]
  rfl

example : intSample.rangeSum 2 100 = 7 := by
  show (build ([1, 2, 3, 4] : List Int)).rangeSum 2 100 = 7
  rw [rangeSum_eq (valid_build _) _ _]
  rfl

example : intSample.rangeSum 3 3 = 0 := by
  show (build ([1, 2, 3, 4] : List Int)).rangeSum 3 3 = 0
  rw [rangeSum_eq (valid_build _) _ _]
  rfl

example {t : FenwickTree Int} {arr : List Int} (hv : Valid t arr)
    (lo hi : Nat) :
    t.rangeSum lo hi = ((arr.take hi).drop lo).sum :=
  rangeSum_eq hv lo hi

example : intSample.rangeSum 3 1 = 0 := by
  show (build ([1, 2, 3, 4] : List Int)).rangeSum 3 1 = 0
  rw [rangeSum_eq (valid_build _) _ _]
  rfl


#check FenwickTree.lowbit
#check FenwickTree.blockSum
#check FenwickTree.Valid
#check FenwickTree.size
#check FenwickTree.build
#check FenwickTree.prefixSum
#check FenwickTree.add
#check FenwickTree.rangeSum
#check FenwickTree.valid_build
#check FenwickTree.prefixSum_eq_take_sum
#check FenwickTree.prefixSum_build
#check FenwickTree.valid_add
#check FenwickTree.prefixSum_add
#check FenwickTree.add_eq_self_of_le
#check FenwickTree.rangeSum_eq

#print axioms FenwickTree.lowbit_pos
#print axioms FenwickTree.lowbit_dvd
#print axioms FenwickTree.lowbit_two_pow
#print axioms FenwickTree.lowbit_div_odd
#print axioms FenwickTree.size_eq_length_of_valid
#print axioms FenwickTree.size_build
#print axioms FenwickTree.valid_build
#print axioms FenwickTree.prefixSum_eq_take_sum
#print axioms FenwickTree.prefixSum_build
#print axioms FenwickTree.add_eq_self_of_le
#print axioms FenwickTree.valid_add
#print axioms FenwickTree.prefixSum_add
#print axioms FenwickTree.rangeSum_eq

end Cslib.Algorithms.Lean.FenwickTreeTests
