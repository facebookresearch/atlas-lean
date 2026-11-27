/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.IrrationalStepProgressions
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An interval and a separated integer progression do not form an MSTD set

We bound the sumset above and the difference set below for the union of an initial integer
interval and a later integer progression.
-/

namespace MetaMathlibExt

open scoped Pointwise

private theorem int_mem_bounds (a : ℝ) (n : ℕ) (ha : a ∈ realIntervalSet n) :
    0 ≤ a ∧ a ≤ (n : ℝ) - 1 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  rw [Finset.mem_range] at hi
  refine ⟨Nat.cast_nonneg i, ?_⟩
  have hle : i + 1 ≤ n := by omega
  have hcast : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hle
  linarith

private theorem ap_mem_ge (c : ℝ) (x m d : ℕ)
    (hc : c ∈ realAPSet (x : ℝ) m (d : ℝ)) : (x : ℝ) ≤ c := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg d))

private theorem interval_add_interval (n : ℕ) (hn : 1 ≤ n) :
    realIntervalSet n + realIntervalSet n = realIntervalSet (2 * n - 1) := by
  ext z
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_range] at hi hj
    refine Finset.mem_image.mpr ⟨i + j, Finset.mem_range.mpr (by omega), ?_⟩
    push_cast
    ring
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_range] at hk
    by_cases hkn : k < n
    · refine Finset.mem_add.mpr ⟨(k : ℝ),
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkn, rfl⟩, (0 : ℝ),
        Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩, ?_⟩
      simp
    · push Not at hkn
      refine Finset.mem_add.mpr ⟨((n - 1 : ℕ) : ℝ),
        Finset.mem_image.mpr ⟨n - 1, Finset.mem_range.mpr (by omega), rfl⟩,
        ((k - (n - 1) : ℕ) : ℝ),
        Finset.mem_image.mpr ⟨k - (n - 1), Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
      have h2 : (((k - (n - 1) : ℕ)) : ℝ) = (k : ℝ) - (((n - 1 : ℕ)) : ℝ) :=
        Nat.cast_sub (by omega : n - 1 ≤ k)
      rw [h2]
      ring

private theorem card_interval_add (n : ℕ) (hn : 1 ≤ n) :
    (realIntervalSet n + realIntervalSet n).card = 2 * n - 1 := by
  rw [interval_add_interval n hn, card_realIntervalSet]

private theorem interval_sub_interval (n : ℕ) (hn : 1 ≤ n) :
    realIntervalSet n - realIntervalSet n =
      (Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1)).image (fun t : ℤ => (t : ℝ)) := by
  ext z
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_range] at hi hj
    refine Finset.mem_image.mpr ⟨(i : ℤ) - (j : ℤ),
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    push_cast
    ring
  · intro h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_Icc] at ht
    by_cases ht0 : 0 ≤ t
    · have htn : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
      have hlt : (t.toNat : ℤ) < (n : ℤ) := by omega
      have hmem : t.toNat < n := by exact_mod_cast hlt
      have htnR : ((t.toNat : ℕ) : ℝ) = (t : ℝ) := by rw [← Int.cast_natCast, htn]
      refine Finset.mem_sub.mpr ⟨((t.toNat : ℕ) : ℝ),
        Finset.mem_image.mpr ⟨t.toNat, Finset.mem_range.mpr hmem, rfl⟩, (0 : ℝ),
        Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩, ?_⟩
      rw [htnR, sub_zero]
    · push Not at ht0
      have hnt : ((-t).toNat : ℤ) = -t := Int.toNat_of_nonneg (by omega : 0 ≤ -t)
      have hlt : ((-t).toNat : ℤ) < (n : ℤ) := by omega
      have hmem : (-t).toNat < n := by exact_mod_cast hlt
      have hntR : (((-t).toNat : ℕ) : ℝ) = -(t : ℝ) := by
        rw [← Int.cast_natCast, hnt, Int.cast_neg]
      refine Finset.mem_sub.mpr ⟨(0 : ℝ),
        Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩,
        (((-t).toNat : ℕ) : ℝ),
        Finset.mem_image.mpr ⟨(-t).toNat, Finset.mem_range.mpr hmem, rfl⟩, ?_⟩
      rw [hntR]
      ring

private theorem card_interval_sub (n : ℕ) (hn : 1 ≤ n) :
    (realIntervalSet n - realIntervalSet n).card = 2 * n - 1 := by
  rw [interval_sub_interval n hn, Finset.card_image_of_injective _ Int.cast_injective,
    Int.card_Icc]
  have hcast : (((2 * n - 1 : ℕ)) : ℤ) = 2 * (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  have he : (n : ℤ) - 1 + 1 - -((n : ℤ) - 1) = 2 * (n : ℤ) - 1 := by ring
  rw [he, ← hcast, Int.toNat_natCast]

private theorem ap_add_ap (x m d : ℕ) :
    realAPSet (x : ℝ) m (d : ℝ) + realAPSet (x : ℝ) m (d : ℝ) =
      realAPSet (2 * (x : ℝ)) (2 * m) (d : ℝ) := by
  ext z
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_range] at hi hj
    refine Finset.mem_image.mpr ⟨i + j, Finset.mem_range.mpr (by omega), ?_⟩
    push_cast
    ring
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_range] at hk
    by_cases hkm : k ≤ m
    · refine Finset.mem_add.mpr ⟨(x : ℝ) + (k : ℝ) * (d : ℝ),
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩,
        (x : ℝ) + ((0 : ℕ) : ℝ) * (d : ℝ),
        Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
      simp only [Nat.cast_zero, zero_mul, add_zero]
      ring
    · push Not at hkm
      refine Finset.mem_add.mpr ⟨(x : ℝ) + (m : ℝ) * (d : ℝ),
        Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), rfl⟩,
        (x : ℝ) + ((k - m : ℕ) : ℝ) * (d : ℝ),
        Finset.mem_image.mpr ⟨k - m, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
      have hsub : (((k - m : ℕ)) : ℝ) = (k : ℝ) - (m : ℝ) := Nat.cast_sub (le_of_lt hkm)
      rw [hsub]
      ring

private theorem card_ap_add (x m d : ℕ) (hd : (d : ℝ) ≠ 0) :
    (realAPSet (x : ℝ) m (d : ℝ) + realAPSet (x : ℝ) m (d : ℝ)).card = 2 * m + 1 := by
  rw [ap_add_ap x m d, card_realAPSet _ _ hd]

private theorem interval_add_ap_eq (n m d x : ℕ) (hn : 1 ≤ n) :
    realIntervalSet n + realAPSet (x : ℝ) m (d : ℝ) =
      (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n).image (· + ((n : ℝ) - 1)) := by
  ext z
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_range] at hi
    have hi' : i ≤ n - 1 := by omega
    have hcast : (((n - 1 - i : ℕ)) : ℝ) = ((n : ℝ) - 1) - (i : ℝ) := by
      rw [Nat.cast_sub hi', Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    refine Finset.mem_image.mpr ⟨b - ((n - 1 - i : ℕ) : ℝ), ?_, ?_⟩
    · exact Finset.mem_sub.mpr ⟨b, hb, ((n - 1 - i : ℕ) : ℝ),
        Finset.mem_image.mpr ⟨n - 1 - i, Finset.mem_range.mpr (by omega), rfl⟩, rfl⟩
    · rw [hcast]
      ring
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨b, hb, a, ha, rfl⟩ := Finset.mem_sub.mp hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_range] at hj
    have hj' : j ≤ n - 1 := by omega
    have hcast : (((n - 1 - j : ℕ)) : ℝ) = ((n : ℝ) - 1) - (j : ℝ) := by
      rw [Nat.cast_sub hj', Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    refine Finset.mem_add.mpr ⟨((n - 1 - j : ℕ) : ℝ),
      Finset.mem_image.mpr ⟨n - 1 - j, Finset.mem_range.mpr (by omega), rfl⟩, b, hb, ?_⟩
    rw [hcast]
    ring

private theorem card_interval_add_ap (n m d x : ℕ) (hn : 1 ≤ n) :
    (realIntervalSet n + realAPSet (x : ℝ) m (d : ℝ)).card =
      (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n).card := by
  rw [interval_add_ap_eq n m d x hn,
    Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]

private theorem interval_sub_ap_eq (n m d x : ℕ) :
    realIntervalSet n - realAPSet (x : ℝ) m (d : ℝ) =
      (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n).image Neg.neg := by
  ext z
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp h
    exact Finset.mem_image.mpr ⟨b - a, Finset.mem_sub.mpr ⟨b, hb, a, ha, rfl⟩, neg_sub b a⟩
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨b, hb, a, ha, rfl⟩ := Finset.mem_sub.mp hw
    exact Finset.mem_sub.mpr ⟨a, ha, b, hb, (neg_sub b a).symm⟩

private theorem card_interval_sub_ap (n m d x : ℕ) :
    (realIntervalSet n - realAPSet (x : ℝ) m (d : ℝ)).card =
      (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n).card := by
  rw [interval_sub_ap_eq n m d x, Finset.card_image_of_injective _ neg_injective]

private theorem zero_mem_interval (n : ℕ) (hn : 1 ≤ n) : (0 : ℝ) ∈ realIntervalSet n :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩

private theorem one_mem_interval (n : ℕ) (hn : 2 ≤ n) : (1 : ℝ) ∈ realIntervalSet n :=
  Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), by simp⟩

private theorem card_ap_sub_zero (x m d : ℕ) (hd : (d : ℝ) ≠ 0) :
    (realAPSet (x : ℝ) m (d : ℝ) - {(0 : ℝ)}).card = m + 1 := by
  have hset : realAPSet (x : ℝ) m (d : ℝ) - {(0 : ℝ)} = realAPSet (x : ℝ) m (d : ℝ) := by
    ext z
    constructor
    · intro h
      obtain ⟨b, hb, c, hc, hsub⟩ := Finset.mem_sub.mp h
      rw [Finset.mem_singleton.mp hc, sub_zero] at hsub
      subst hsub
      exact hb
    · intro h
      exact Finset.mem_sub.mpr ⟨z, h, 0, Finset.mem_singleton_self 0, sub_zero z⟩
  rw [hset, card_realAPSet _ _ hd]

private theorem card_ap_sub_one (x m d : ℕ) (hd : (d : ℝ) ≠ 0) :
    (realAPSet (x : ℝ) m (d : ℝ) - {(1 : ℝ)}).card = m + 1 := by
  have hset : realAPSet (x : ℝ) m (d : ℝ) - {(1 : ℝ)} =
      (realAPSet (x : ℝ) m (d : ℝ)).image (· - 1) := by
    ext z
    constructor
    · intro h
      obtain ⟨b, hb, c, hc, hsub⟩ := Finset.mem_sub.mp h
      rw [Finset.mem_singleton.mp hc] at hsub
      exact Finset.mem_image.mpr ⟨b, hb, hsub⟩
    · intro h
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_sub.mpr ⟨b, hb, 1, Finset.mem_singleton_self 1, rfl⟩
  rw [hset, Finset.card_image_of_injective _ (fun a b h => by
    have h2 := congrArg (· + (1 : ℝ)) h
    simpa using h2), card_realAPSet _ _ hd]

private theorem disjoint_ap_sub_zero_one (x m d : ℕ) (hd : 2 ≤ d) :
    Disjoint (realAPSet (x : ℝ) m (d : ℝ) - {(0 : ℝ)})
      (realAPSet (x : ℝ) m (d : ℝ) - {(1 : ℝ)}) := by
  rw [Finset.disjoint_left]
  intro z hz hcon
  obtain ⟨b, hb, c, hc, hsub⟩ := Finset.mem_sub.mp hz
  obtain ⟨b', hb', c', hc', hsub'⟩ := Finset.mem_sub.mp hcon
  rw [Finset.mem_singleton.mp hc, sub_zero] at hsub
  rw [Finset.mem_singleton.mp hc'] at hsub'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb'
  have hreal : (1 : ℝ) + (i : ℝ) * (d : ℝ) = (j : ℝ) * (d : ℝ) := by linarith
  have hnat : 1 + i * d = j * d := by
    have hcast : (((1 + i * d : ℕ)) : ℝ) = (((j * d : ℕ)) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have hlt : i * d < j * d := by omega
  have hij : i < j := lt_of_mul_lt_mul_right hlt (Nat.zero_le d)
  have hle : (i + 1) * d ≤ j * d := Nat.mul_le_mul_right d (by omega : i + 1 ≤ j)
  have hexpand : (i + 1) * d = i * d + d := by ring
  omega

private theorem ap_sub_lower_bound (n x m d : ℕ) (hn : 2 ≤ n) (hd0 : (d : ℝ) ≠ 0)
    (hd : 2 ≤ d) :
    2 * m + 2 ≤ (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n).card := by
  have hsub : (realAPSet (x : ℝ) m (d : ℝ) - {(0 : ℝ)}) ∪
      (realAPSet (x : ℝ) m (d : ℝ) - {(1 : ℝ)}) ⊆
      realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_sub.mp hz
      obtain rfl := Finset.mem_singleton.mp hc
      exact Finset.mem_sub.mpr ⟨b, hb, 0, zero_mem_interval n (by omega), rfl⟩
    · obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_sub.mp hz
      obtain rfl := Finset.mem_singleton.mp hc
      exact Finset.mem_sub.mpr ⟨b, hb, 1, one_mem_interval n hn, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (disjoint_ap_sub_zero_one x m d hd),
    card_ap_sub_zero x m d hd0, card_ap_sub_one x m d hd0] at hcard
  omega

private theorem sub_mem_bounds_diff (y : ℝ) (n : ℕ)
    (h : y ∈ realIntervalSet n - realIntervalSet n) :
    -((n : ℝ) - 1) ≤ y ∧ y ≤ (n : ℝ) - 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp h
  obtain ⟨ha0, ha1⟩ := int_mem_bounds a n ha
  obtain ⟨hb0, hb1⟩ := int_mem_bounds b n hb
  constructor <;> linarith

private theorem ap_sub_mem_ge (w : ℝ) (n x m d : ℕ)
    (h : w ∈ realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n) :
    (x : ℝ) - (n : ℝ) + 1 ≤ w := by
  obtain ⟨c, hc, a, ha, rfl⟩ := Finset.mem_sub.mp h
  obtain ⟨ha0, ha1⟩ := int_mem_bounds a n ha
  have hxc := ap_mem_ge c x m d hc
  linarith

private theorem interval_sub_ap_mem_le (v : ℝ) (n x m d : ℕ)
    (h : v ∈ realIntervalSet n - realAPSet (x : ℝ) m (d : ℝ)) :
    v ≤ (n : ℝ) - 1 - (x : ℝ) := by
  obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_sub.mp h
  obtain ⟨ha0, ha1⟩ := int_mem_bounds a n ha
  have hxc := ap_mem_ge c x m d hc
  linarith

private theorem nat_le_ap_start (n x : ℕ) (hn : 3 ≤ n) (hx : 2 * n - 1 ≤ x) :
    (n : ℝ) ≤ (x : ℝ) - (n : ℝ) + 1 := by
  have hcast' : (((2 * n - 1 : ℕ)) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)] at hcast'
  push_cast at hcast'
  linarith

private theorem disjoint_diff_left (n x m d : ℕ) (hn : 3 ≤ n) (hx : 2 * n - 1 ≤ x) :
    Disjoint (realIntervalSet n - realIntervalSet n)
      (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n) := by
  rw [Finset.disjoint_left]
  intro y hyI hyJ
  obtain ⟨hyIlo, hyIhi⟩ := sub_mem_bounds_diff y n hyI
  have hyJlo := ap_sub_mem_ge y n x m d hyJ
  have hnx := nat_le_ap_start n x hn hx
  linarith

private theorem disjoint_diff_right (n x m d : ℕ) (hn : 3 ≤ n) (hx : 2 * n - 1 ≤ x) :
    Disjoint ((realIntervalSet n - realIntervalSet n) ∪
        (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n))
      (realIntervalSet n - realAPSet (x : ℝ) m (d : ℝ)) := by
  rw [Finset.disjoint_left]
  intro y hyL hyR
  have hyRhi := interval_sub_ap_mem_le y n x m d hyR
  have hnx := nat_le_ap_start n x hn hx
  rw [Finset.mem_union] at hyL
  rcases hyL with hyL | hyL
  · obtain ⟨hyLlo, -⟩ := sub_mem_bounds_diff y n hyL
    linarith
  · have hyLlo := ap_sub_mem_ge y n x m d hyL
    linarith

private theorem sum_subset (n m d x : ℕ) :
    (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) +
        (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) ⊆
      (realIntervalSet n + realIntervalSet n) ∪
        ((realIntervalSet n + realAPSet (x : ℝ) m (d : ℝ)) ∪
          (realAPSet (x : ℝ) m (d : ℝ) + realAPSet (x : ℝ) m (d : ℝ))) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  rw [Finset.mem_union] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
      (Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩))))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
      (Finset.mem_add.mpr ⟨b, hb, a, ha, add_comm b a⟩))))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
      (Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩))))

private theorem diff_superset (n m d x : ℕ) :
    ((realIntervalSet n - realIntervalSet n) ∪
        (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n)) ∪
      (realIntervalSet n - realAPSet (x : ℝ) m (d : ℝ)) ⊆
    (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) -
        (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) := by
  intro z hz
  rw [Finset.mem_union] at hz
  rcases hz with hz | hz
  · rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
      exact Finset.mem_sub.mpr ⟨a, Finset.mem_union.mpr (Or.inl ha), b,
        Finset.mem_union.mpr (Or.inl hb), rfl⟩
    · obtain ⟨c, hc, a, ha, rfl⟩ := Finset.mem_sub.mp hz
      exact Finset.mem_sub.mpr ⟨c, Finset.mem_union.mpr (Or.inr hc), a,
        Finset.mem_union.mpr (Or.inl ha), rfl⟩
  · obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_sub.mp hz
    exact Finset.mem_sub.mpr ⟨a, Finset.mem_union.mpr (Or.inl ha), c,
      Finset.mem_union.mpr (Or.inr hc), rfl⟩

-- Retain the named hypotheses of the source statement.
set_option linter.unusedVariables false in
/-- **Interval plus integer progression starting at $2n - 1$ or later is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and $x \ge 2n - 1$, the set
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 2
(`integers-2026-A58-lem-2`). -/
public theorem not_isMSTDSet_intervalAP_nat_of_two_mul_sub_one_le (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx : 2 * n - 1 ≤ x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (lt_trans zero_lt_one one_lt_two) (by exact_mod_cast hd))
  have hsum := Finset.card_le_card (sum_subset n m d x)
  have hub1 := Finset.card_union_le (realIntervalSet n + realIntervalSet n)
    ((realIntervalSet n + realAPSet (x : ℝ) m (d : ℝ)) ∪
      (realAPSet (x : ℝ) m (d : ℝ) + realAPSet (x : ℝ) m (d : ℝ)))
  have hub2 := Finset.card_union_le (realIntervalSet n + realAPSet (x : ℝ) m (d : ℝ))
    (realAPSet (x : ℝ) m (d : ℝ) + realAPSet (x : ℝ) m (d : ℝ))
  rw [card_interval_add n (by omega)] at hub1
  rw [card_interval_add_ap n m d x (by omega), card_ap_add x m d hd0] at hub2
  have hdiff := Finset.card_le_card (diff_superset n m d x)
  rw [Finset.card_union_of_disjoint (disjoint_diff_right n x m d hn hx),
    Finset.card_union_of_disjoint (disjoint_diff_left n x m d hn hx),
    card_interval_sub n (by omega), card_interval_sub_ap n m d x] at hdiff
  have ht : 2 * m + 2 ≤ (realAPSet (x : ℝ) m (d : ℝ) - realIntervalSet n).card :=
    ap_sub_lower_bound n x m d (by omega) hd0 hd
  rw [IsMSTDSet]
  intro hlt
  omega

end MetaMathlibExt
