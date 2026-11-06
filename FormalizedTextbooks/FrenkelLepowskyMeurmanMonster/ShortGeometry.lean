/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Short-vector class addition in the actual Leech lattice.
The converse uses its proved minimum, rather than a table of intersections.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Pairing before division by the lattice normalization factor eight. -/
def leechIntegralPairing (u v : Fin 24 → ℤ) : ℤ := ∑ i, u i * v i

theorem leechSquareSum_add (u v : Fin 24 → ℤ) :
    leechSquareSum (u + v) =
      leechSquareSum u + leechSquareSum v + 2 * leechIntegralPairing u v := by
  simp only [leechSquareSum, leechIntegralPairing, Pi.add_apply,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem leechSquareSum_sub (u v : Fin 24 → ℤ) :
    leechSquareSum (u - v) =
      leechSquareSum u + leechSquareSum v - 2 * leechIntegralPairing u v := by
  simp only [leechSquareSum, leechIntegralPairing, Pi.sub_apply,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem leechSquareSum_neg (u : Fin 24 → ℤ) :
    leechSquareSum (-u) = leechSquareSum u := by
  simp [leechSquareSum]

/-- Four lattice vectors in the same half-sum configuration cannot all be
nonzero: their total square length is only three times the lattice minimum. -/
theorem leechShort_four_half_sums (u v w z : leechIntegral)
    (hu : leechSquareSum u.val = 32) (hv : leechSquareSum v.val = 32)
    (hw : leechSquareSum w.val = 32) (hz : u + v - w = z + z) :
    z = 0 ∨ u - z = 0 ∨ v - z = 0 ∨ u + v - z = 0 := by
  have hid : leechSquareSum z.val + leechSquareSum (u - z).val +
      leechSquareSum (v - z).val + leechSquareSum (u + v - z).val = 96 := by
    have hcoord (i : Fin 24) : w.val i = u.val i + v.val i - 2 * z.val i := by
      have h := congrFun (congrArg Subtype.val hz) i
      change u.val i + v.val i - w.val i = z.val i + z.val i at h
      omega
    have he : leechSquareSum z.val + leechSquareSum (u - z).val +
        leechSquareSum (v - z).val + leechSquareSum (u + v - z).val =
        leechSquareSum u.val + leechSquareSum v.val + leechSquareSum w.val := by
      simp only [leechSquareSum, Submodule.coe_sub, Submodule.coe_add,
        Pi.sub_apply, Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoord]
      ring
    rw [he, hu, hv, hw]
    norm_num
  by_contra h
  simp only [not_or] at h
  have hmin (a : leechIntegral) (ha : a ≠ 0) : 32 ≤ leechSquareSum a.val := by
    apply leechIntegral_minimum a.val a.property
    intro he
    exact ha (Subtype.ext he)
  have h0 := hmin z h.1
  have h1 := hmin (u - z) h.2.1
  have h2 := hmin (v - z) h.2.2.1
  have h3 := hmin (u + v - z) h.2.2.2
  omega

/-- A sum of two short classes is short only when their integral pairing is
sixteen or minus sixteen (normalized pairing two or minus two). -/
theorem leechShort_sum_class_pairing (u v : leechIntegral)
    (hu : leechSquareSum u.val = 32) (hv : leechSquareSum v.val = 32)
    (hshort : IsLeechShortClass (leechReduction u + leechReduction v)) :
    leechIntegralPairing u.val v.val = 16 ∨
      leechIntegralPairing u.val v.val = -16 := by
  obtain ⟨w, hclass, hw⟩ := hshort
  have hm : u + v - w ∈ twiceLeechIntegral := by
    apply QuotientAddGroup.eq_iff_sub_mem.mp
    change leechReduction (u + v) = leechReduction w
    rw [map_add, hclass]
  obtain ⟨z, hz⟩ := hm
  have hz' : u + v - w = z + z := by
    change (2 : ℕ) • z = u + v - w at hz
    simpa only [two_nsmul] using hz.symm
  rcases leechShort_four_half_sums u v w z hu hv hw hz' with h | h | h | h
  · have he : w = u + v := by
      rw [h] at hz'
      simpa using (sub_eq_zero.mp hz').symm
    rw [he] at hw
    change leechSquareSum (u.val + v.val) = 32 at hw
    rw [leechSquareSum_add, hu, hv] at hw
    right
    omega
  · have he : w = v - u := by
      have hez : u = z := sub_eq_zero.mp h
      rw [← hez] at hz'
      apply Subtype.ext
      funext i
      have hc := congrFun (congrArg Subtype.val hz') i
      change u.val i + v.val i - w.val i = u.val i + u.val i at hc
      change w.val i = v.val i - u.val i
      omega
    rw [he] at hw
    change leechSquareSum (v.val - u.val) = 32 at hw
    rw [leechSquareSum_sub, hv, hu] at hw
    have hc : leechIntegralPairing v.val u.val = leechIntegralPairing u.val v.val := by
      simp [leechIntegralPairing, mul_comm]
    rw [hc] at hw
    left
    omega
  · have he : w = u - v := by
      have hez : v = z := sub_eq_zero.mp h
      rw [← hez] at hz'
      apply Subtype.ext
      funext i
      have hc := congrFun (congrArg Subtype.val hz') i
      change u.val i + v.val i - w.val i = v.val i + v.val i at hc
      change w.val i = u.val i - v.val i
      omega
    rw [he] at hw
    change leechSquareSum (u.val - v.val) = 32 at hw
    rw [leechSquareSum_sub, hu, hv] at hw
    left
    omega
  · have he : w = -(u + v) := by
      have hez : u + v = z := sub_eq_zero.mp h
      rw [← hez] at hz'
      apply Subtype.ext
      funext i
      have hc := congrFun (congrArg Subtype.val hz') i
      change u.val i + v.val i - w.val i =
        (u.val i + v.val i) + (u.val i + v.val i) at hc
      change w.val i = -(u.val i + v.val i)
      omega
    rw [he] at hw
    change leechSquareSum (-(u.val + v.val)) = 32 at hw
    rw [leechSquareSum_neg, leechSquareSum_add, hu, hv] at hw
    right
    omega

/-- Pairing sixteen supplies the difference vector; pairing minus sixteen
supplies the sum vector. Both are actual short representatives. -/
theorem leechShort_sum_class_iff_pairing (u v : leechIntegral)
    (hu : leechSquareSum u.val = 32) (hv : leechSquareSum v.val = 32) :
    IsLeechShortClass (leechReduction u + leechReduction v) ↔
      leechIntegralPairing u.val v.val = 16 ∨
        leechIntegralPairing u.val v.val = -16 := by
  constructor
  · exact leechShort_sum_class_pairing u v hu hv
  · rintro (h | h)
    · refine ⟨u - v, ?_, ?_⟩
      · rw [map_sub]
        have hn : -leechReduction v = leechReduction v := by
          rw [← map_neg, leechReduction_neg]
        rw [sub_eq_add_neg, hn]
      · change leechSquareSum (u.val - v.val) = 32
        rw [leechSquareSum_sub, hu, hv, h]
        norm_num
    · refine ⟨u + v, map_add leechReduction u v, ?_⟩
      change leechSquareSum (u.val + v.val) = 32
      rw [leechSquareSum_add, hu, hv, h]
      norm_num

theorem griessShort_sum_class_iff_pairing (r s : GriessShortIndex) :
    IsLeechShortClass (griessShortClass r + griessShortClass s) ↔
      leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) = 16 ∨
        leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) = -16 :=
  leechShort_sum_class_iff_pairing (griessShortLatticeVector r)
    (griessShortLatticeVector s) (griessShortIntegral_squareSum r)
    (griessShortIntegral_squareSum s)

/-- The physical pairing is the integral pairing divided by eight. -/
theorem griessShortVector_pairing (r s : GriessShortIndex) :
    stdPairingFun (griessShortVector r) (griessShortVector s) =
      (leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) : ℝ) / 8 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  simp only [stdPairingFun, griessShortVector, div_mul_div_comm, hs,
    ← Finset.sum_div, leechIntegralPairing, Int.cast_sum, Int.cast_mul]

theorem griessShort_sum_class_iff_real_pairing (r s : GriessShortIndex) :
    IsLeechShortClass (griessShortClass r + griessShortClass s) ↔
      stdPairingFun (griessShortVector r) (griessShortVector s) = 2 ∨
        stdPairingFun (griessShortVector r) (griessShortVector s) = -2 := by
  rw [griessShort_sum_class_iff_pairing, griessShortVector_pairing]
  constructor
  · rintro (h | h)
    · left
      rw [h]
      norm_num
    · right
      rw [h]
      norm_num
  · rintro (h | h)
    · left
      have hh : (leechIntegralPairing (griessShortIntegral r)
          (griessShortIntegral s) : ℝ) = 16 := by linarith
      exact_mod_cast hh
    · right
      have hh : (leechIntegralPairing (griessShortIntegral r)
          (griessShortIntegral s) : ℝ) = -16 := by linarith
      exact_mod_cast hh

/-- Distinct short labels represent neither equal nor opposite lattice vectors.
Applying the minimum to their sum and difference bounds their pairing. -/
theorem griessShort_integral_pairing_bounds (r s : GriessShortIndex) (hrs : r ≠ s) :
    -16 ≤ leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) ∧
      leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) ≤ 16 := by
  have hsub : griessShortIntegral r - griessShortIntegral s ≠ 0 := by
    intro h
    exact hrs (griessShort_label_unique r s (Or.inl (sub_eq_zero.mp h)))
  have hadd : griessShortIntegral r + griessShortIntegral s ≠ 0 := by
    intro h
    exact hrs (griessShort_label_unique r s (Or.inr (eq_neg_of_add_eq_zero_left h)))
  have hminus := leechIntegral_minimum _
    (leechIntegral.sub_mem (griessShortIntegral_mem r) (griessShortIntegral_mem s)) hsub
  have hplus := leechIntegral_minimum _
    (leechIntegral.add_mem (griessShortIntegral_mem r) (griessShortIntegral_mem s)) hadd
  rw [leechSquareSum_sub, griessShortIntegral_squareSum,
    griessShortIntegral_squareSum] at hminus
  rw [leechSquareSum_add, griessShortIntegral_squareSum,
    griessShortIntegral_squareSum] at hplus
  constructor <;> omega

theorem griessShort_pairing_bounds (r s : GriessShortIndex) (hrs : r ≠ s) :
    -2 ≤ stdPairingFun (griessShortVector r) (griessShortVector s) ∧
      stdPairingFun (griessShortVector r) (griessShortVector s) ≤ 2 := by
  obtain ⟨hlo, hhi⟩ := griessShort_integral_pairing_bounds r s hrs
  have hlo' : (-16 : ℝ) ≤
      (leechIntegralPairing (griessShortIntegral r) (griessShortIntegral s) : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (leechIntegralPairing (griessShortIntegral r)
      (griessShortIntegral s) : ℝ) ≤ 16 := by exact_mod_cast hhi
  rw [griessShortVector_pairing]
  constructor <;> linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
