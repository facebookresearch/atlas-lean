/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Max

@[expose] public section

namespace MetaMathlibExt

/-- **Raney's cycle lemma for arbitrary integer lists.** Let $a = (a_0, \dots, a_{n-1})$ be a
list of integers whose entries sum to $-1$. Then there is exactly one index $r$ with $0 \le r < n$
such that every proper prefix of the rotation $(a_r, \dots, a_{n-1}, a_0, \dots, a_{r-1})$ has
nonnegative sum: for every $t$ with $0 \le t < n$, the sum of the first $t$ entries of this
rotation is at least $0$. -/
theorem raney_cycle_lemma_sum_neg_one_general
    (a : List Int) (hsum : a.sum = -1) :
    ∃! r : Fin a.length, ∀ t : Nat, t < a.length → 0 ≤ ((a.rotate r.val).take t).sum := by
  classical
  set n := a.length with hn_def
  set S : Nat → Int := fun k => (a.take k).sum with hS_def
  have hS0 : S 0 = 0 := by simp [hS_def]
  have hSn : S n = -1 := by
    have h : a.take n = a := List.take_length (l := a)
    simp [hS_def, h, hsum]
  have h_take_add_sum : ∀ r t : Nat, S (r + t) = S r + ((a.drop r).take t).sum := by
    intro r t
    have h := List.take_add (l := a) (i := r) (j := t)
    have hs : ((a.take (r + t)).sum) = ((a.take r).sum) + (((a.drop r).take t).sum) := by
      rw [h, List.sum_append]
    simpa [hS_def] using hs
  have h_sum_drop : ∀ r : Nat, S r + (a.drop r).sum = -1 := by
    intro r
    have h := List.sum_take_add_sum_drop (L := a) (i := r)
    rw [hsum] at h
    simpa [hS_def] using h
  have hlen_drop : ∀ r : Nat, (a.drop r).length = n - r := by
    intro r; simp [hn_def, List.length_drop]
  have h_rot_small : ∀ r t : Nat, r < n → t < n → t + r ≤ n →
      (((a.rotate r).take t).sum) = S (r + t) - S r := by
    intro r t hr ht hle
    have hrot : a.rotate r = (a.drop r) ++ (a.take r) :=
      List.rotate_eq_drop_append_take (by omega : r ≤ a.length)
    rw [hrot, List.take_append]
    have hlen : (a.drop r).length = n - r := hlen_drop r
    have hsub : t - (a.drop r).length = 0 := by omega
    rw [hsub]
    simp only [List.take_zero, List.append_nil]
    have h2 := h_take_add_sum r t
    have hcomm : r + t = t + r := by omega
    omega
  have h_rot_large : ∀ r t : Nat, r < n → t < n → n < t + r →
      (((a.rotate r).take t).sum) = -1 - S r + S (t + r - n) := by
    intro r t hr ht hgt
    have hrot : a.rotate r = (a.drop r) ++ (a.take r) :=
      List.rotate_eq_drop_append_take (by omega : r ≤ a.length)
    rw [hrot, List.take_append]
    have hlen : (a.drop r).length = n - r := hlen_drop r
    have htake_full : (a.drop r).take t = a.drop r := by
      exact List.take_of_length_le (by omega : (a.drop r).length ≤ t)
    rw [htake_full]
    have hsub_eq : t - (n - r) = t + r - n := by omega
    rw [hlen] at *
    rw [hsub_eq]
    have htake_take : ((a.take r).take (t + r - n)) = a.take (t + r - n) := by
      rw [List.take_take]
      have hmin : min (t + r - n) r = t + r - n := by omega
      rw [hmin]
    rw [htake_take, List.sum_append]
    have h1 := h_sum_drop r
    simp only [hS_def] at h1 ⊢
    omega
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have ha : a = [] := List.length_eq_zero_iff.mp (by omega : a.length = 0)
    simp [ha] at hsum
  have hne : (Finset.range n).Nonempty := by
    refine ⟨0, ?_⟩
    simp only [Finset.mem_range]
    omega
  set T := (Finset.range n).image S with hT_def
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨S x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  set m := T.min' hTne with hm_def
  have hm_mem : m ∈ T := Finset.min'_mem T hTne
  have hm_le : ∀ y ∈ T, m ≤ y := fun y hy => Finset.min'_le T y hy
  obtain ⟨k0, hk0mem, hk0eq⟩ : ∃ k0, k0 ∈ Finset.range n ∧ S k0 = m := by
    rw [hT_def] at hm_mem
    simp only [Finset.mem_image, Finset.mem_range] at hm_mem
    obtain ⟨k0, hk0, heq⟩ := hm_mem
    exact ⟨k0, Finset.mem_range.mpr hk0, heq⟩
  have hk0lt : k0 < n := Finset.mem_range.mp hk0mem
  have hex : ∃ n0 : Nat, S n0 = m := ⟨k0, hk0eq⟩
  set r0 := Nat.find hex with hr0_def
  have hr0eq : S r0 = m := Nat.find_spec hex
  have hr0le : r0 ≤ k0 := Nat.find_min' hex hk0eq
  have hr0lt : r0 < n := by omega
  have hr0min : ∀ k : Nat, k < r0 → S k ≠ m := fun k hk => Nat.find_min hex hk
  have hmin_le : ∀ k : Nat, k < n → m ≤ S k := by
    intro k hk
    have hSk : S k ∈ T := Finset.mem_image.mpr ⟨k, by simp [Finset.mem_range, hk], rfl⟩
    exact hm_le (S k) hSk
  have hstrict : ∀ k : Nat, k < n → k < r0 → m + 1 ≤ S k := by
    intro k hkn hkr
    have hne' : S k ≠ m := hr0min k hkr
    have hle := hmin_le k hkn
    omega
  have hm_neg : r0 ≠ 0 → m ≤ -1 := by
    intro hr0ne
    have h0lt : (0 : Nat) < n := by omega
    have hle0 := hmin_le 0 h0lt
    have hne0 : S 0 ≠ m := by
      intro heq
      apply hr0ne
      have : r0 ≤ 0 := Nat.find_min' hex (by rw [hS0] at heq ⊢; omega : S 0 = m)
      omega
    rw [hS0] at hle0
    omega
  have hgood : ∀ t : Nat, t < n → 0 ≤ (((a.rotate r0).take t).sum) := by
    intro t ht
    by_cases hle : t + r0 ≤ n
    · rw [h_rot_small r0 t hr0lt ht hle]
      by_cases heq : r0 + t < n
      · have hle' := hmin_le (r0 + t) heq
        omega
      · have heqn : r0 + t = n := by omega
        have hr0ne : r0 ≠ 0 := by omega
        have hm1 := hm_neg hr0ne
        rw [heqn, hSn]
        omega
    · have hlt : n < t + r0 := by omega
      rw [h_rot_large r0 t hr0lt ht hlt]
      have hk_lt_n : t + r0 - n < n := by omega
      have hk_lt_r0 : t + r0 - n < r0 := by omega
      have hst := hstrict (t + r0 - n) hk_lt_n hk_lt_r0
      omega
  refine ⟨⟨r0, hr0lt⟩, hgood, ?_⟩
  intro r' hr'
  obtain ⟨r1, hr1lt⟩ := r'
  have hr1lt_n : r1 < n := by omega
  have hr1good : ∀ t : Nat, t < n → 0 ≤ (((a.rotate r1).take t).sum) := by
    intro t ht
    exact hr' t (by omega)
  have hge_after : ∀ k : Nat, r1 ≤ k → k < n → S r1 ≤ S k := by
    intro k hrk hkn
    have ht_lt : k - r1 < n := by omega
    have hsum_nn := hr1good (k - r1) ht_lt
    rw [h_rot_small r1 (k - r1) hr1lt ht_lt (by omega : (k - r1) + r1 ≤ n)] at hsum_nn
    have hkk : r1 + (k - r1) = k := by omega
    rw [hkk] at hsum_nn
    omega
  have hle_neg : r1 ≠ 0 → S r1 ≤ -1 := by
    intro hr1ne
    have ht_lt : n - r1 < n := by omega
    have hsum_nn := hr1good (n - r1) ht_lt
    rw [h_rot_small r1 (n - r1) hr1lt ht_lt (by omega : (n - r1) + r1 ≤ n)] at hsum_nn
    have hkk : r1 + (n - r1) = n := by omega
    rw [hkk, hSn] at hsum_nn
    omega
  have hgt_before : ∀ k : Nat, k < n → k < r1 → S r1 + 1 ≤ S k := by
    intro k hkn hkr
    by_cases hk0 : k = 0
    · subst hk0
      have hr1ne : r1 ≠ 0 := by omega
      have hs := hle_neg hr1ne
      rw [hS0]
      omega
    · have ht_lt : k + n - r1 < n := by omega
      have hsum_nn := hr1good (k + n - r1) ht_lt
      have hgt : n < (k + n - r1) + r1 := by omega
      rw [h_rot_large r1 (k + n - r1) hr1lt ht_lt hgt] at hsum_nn
      have hkk : (k + n - r1) + r1 - n = k := by omega
      rw [hkk] at hsum_nn
      omega
  have hSr1_ge : m ≤ S r1 := hmin_le r1 hr1lt
  have hSr1_le : S r1 ≤ m := by
    by_cases hle : r0 < r1
    · have h := hgt_before r0 hr0lt hle
      omega
    · have hle' : r1 ≤ r0 := by omega
      have h := hge_after r0 hle' hr0lt
      omega
  have hSr1_eq : S r1 = m := by omega
  have hr0_le_r1 : r0 ≤ r1 := Nat.find_min' hex (by rw [hSr1_eq] : S r1 = m)
  have hr1_le_r0 : r1 ≤ r0 := by
    by_contra hlt
    have hlt' : r0 < r1 := by omega
    have h := hgt_before r0 hr0lt hlt'
    omega
  have hr1_eq : r1 = r0 := by omega
  exact Fin.ext hr1_eq

set_option linter.unusedVariables false in
/-- **Raney's cycle lemma.** Let $a = (a_0, \dots, a_{n-1})$ be a list of integers, each at least
$-1$, whose entries sum to $-1$. Then there is exactly one index $r$ with $0 \le r < n$ such that
every proper prefix of the rotation $(a_r, \dots, a_{n-1}, a_0, \dots, a_{r-1})$ has nonnegative
sum: for every $t$ with $0 \le t < n$, the sum of the first $t$ entries of this rotation is at
least $0$.

The hypothesis that every entry is at least $-1$ is not needed; Raney's cycle lemma for arbitrary
integer lists proves the same conclusion without it.

Proves `Wanted` entry `raney_cycle_lemma_sum_neg_one`.

Source: `https://cs.uwaterloo.ca/journals/JIS/VOL24/Haupt/haupt4.tex`, lines 804-807 (frozen).
Lean's zero-based left rotation is a bijective reindexing of the source's cut after `a_r`;
`t < a.length` ranges over every proper prefix, with `t = 0` giving the true empty-prefix
condition. The lower bound `hlower` is not needed; see `raney_cycle_lemma_sum_neg_one_general`.
Grounded record: `jis_grounded_7df8f01cf825a78240bfc1d3`.
Concept: `jis_dep_4e5e1a90d8c5f1fdb136c3c0`.
Source file SHA-256: `1b412146e9dba7d9302d274268baf3e35239b8369473faf57f086f918e3b66af`.
Exact span SHA-256: `c5a3ab122e3bf8a75f6f8c7999cd1e20f508115ff91a537497e61ab7c1359b23`.
Corrected counts: 3 mentions / 1 paper / 1 proof use.
-/
@[nolint unusedArguments]
theorem raney_cycle_lemma_sum_neg_one
    (a : List Int) (hlower : ∀ x ∈ a, -1 ≤ x) (hsum : a.sum = -1) :
    ∃! r : Fin a.length, ∀ t : Nat, t < a.length → 0 ≤ ((a.rotate r.val).take t).sum := by
  exact raney_cycle_lemma_sum_neg_one_general a hsum

end MetaMathlibExt
