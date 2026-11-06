/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence

/-! The actual standard Golay octad and uniqueness through five points.
This supplies the geometric orbit upper bounds for the Mathieu stabilizer chain. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Hamming distance and support intersection identity for arbitrary binary words. -/
theorem golayBinary_difference_weight (c d : Fin 24 → ZMod 2) :
    (∑ i, (c i - d i).val) + 2 * (∑ i, (c i).val * (d i).val) =
      (∑ i, (c i).val) + ∑ i, (d i).val := by
  have h : ∀ a b : ZMod 2, (a - b).val + 2 * (a.val * b.val) = a.val + b.val := by decide
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => h (c i) (d i))

/-- Two distinct octads cannot both contain five specified coordinates. -/
theorem golayOctad_unique_through_first_five (c d : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hd : d ∈ golayCode)
    (hwc : ∑ i, (c i).val = 8) (hwd : ∑ i, (d i).val = 8)
    (hfirst : ∀ i : Fin 24, i.val < 5 → c i = 1 ∧ d i = 1) : c = d := by
  by_contra hn
  have hlo := golayCode_weight_ge_eight (c - d) (golayCode.sub_mem hc hd) (sub_ne_zero.mpr hn)
  have hi : 5 ≤ ∑ i, (c i).val * (d i).val := by
    have hsum : (∑ i : Fin 24, (if i.val < 5 then 1 else 0 : ℕ)) = 5 := by decide
    rw [← hsum]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : i.val < 5
    · simp only [h, ite_true]
      rw [(hfirst i h).1, (hfirst i h).2]
      have h1 : (1 : ZMod 2).val = 1 := by decide
      rw [h1]
    · simp only [h, ite_false]
      exact Nat.zero_le _
  have hw := golayBinary_difference_weight c d
  rw [hwc, hwd] at hw
  change 8 ≤ ∑ i, (c i - d i).val at hlo
  omega

/-- The physical first tetrads form the actual Golay octad encoded by label 2063. -/
def golayStandardOctad : Fin 24 → ZMod 2 := fun i => if i.val < 8 then 1 else 0

set_option maxHeartbeats 2000000 in
-- Check the 24 bits of the explicit source encoder label.
theorem golayStandardOctad_encoder : golayEncoder (golayLabelCoefficients 2063) =
    golayStandardOctad := by
  decide +kernel

/-- The standard octad belongs to the actual published code. -/
theorem golayStandardOctad_mem : golayStandardOctad ∈ golayCode := by
  rw [← golayStandardOctad_encoder]
  exact ⟨_, rfl⟩

/-- The standard octad has exactly eight coordinates. -/
theorem golayStandardOctad_weight : (∑ i, (golayStandardOctad i).val) = 8 := by
  decide +kernel

/-- A code automorphism fixing the first five points preserves the standard octad. -/
theorem golayAutomorphism_preserves_standardOctad (p : golayAutomorphismSubgroup)
    (hp : ∀ i : Fin 24, i.val < 5 → p.val i = i) :
    golayPermute p.val golayStandardOctad = golayStandardOctad := by
  apply golayOctad_unique_through_first_five _ _
    ((p.property _).mp golayStandardOctad_mem) golayStandardOctad_mem
  · exact (Equiv.sum_comp p.val.symm (fun i => (golayStandardOctad i).val)).trans
      golayStandardOctad_weight
  · exact golayStandardOctad_weight
  · intro i hi
    have hpi : p.val.symm i = i := by
      have h := congrArg p.val.symm (hp i hi)
      rw [p.val.symm_apply_apply] at h
      exact h.symm
    have hi8 : i.val < 8 := by omega
    simp only [golayPermute, hpi, golayStandardOctad, hi8, ite_true]
    trivial

/-- Fixing five points preserves the membership of every point in the standard octad. -/
theorem golayAutomorphism_standardOctad_points (p : golayAutomorphismSubgroup)
    (hp : ∀ i : Fin 24, i.val < 5 → p.val i = i) (i : Fin 24) :
    (p.val i).val < 8 ↔ i.val < 8 := by
  have h := congrFun (golayAutomorphism_preserves_standardOctad p hp) (p.val i)
  change golayStandardOctad (p.val.symm (p.val i)) = golayStandardOctad (p.val i) at h
  rw [p.val.symm_apply_apply] at h
  have hn01 : (0 : ZMod 2) ≠ 1 := by decide
  have hn10 : (1 : ZMod 2) ≠ 0 := by decide
  unfold golayStandardOctad at h
  split_ifs at h <;> simp_all
  all_goals omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
