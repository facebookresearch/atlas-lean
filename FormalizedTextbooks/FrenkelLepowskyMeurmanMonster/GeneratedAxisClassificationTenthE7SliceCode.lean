/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOctads
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7ConjugationVectors

/-! A genuine Golay octad cannot have only one or two coordinates outside another octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Two actual octads with at most two coordinates outside one another coincide. -/
theorem generatedTenth_e7_octad_eq_of_outside_weight (c d : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hd : d ∈ golayCode)
    (hwc : ∑ i, (c i).val = 8) (hwd : ∑ i, (d i).val = 8)
    (hout : (∑ i, if d i = 0 then (c i).val else 0) ≤ 2) : c = d := by
  have hsplit : (∑ i, (c i).val * (d i).val) +
      (∑ i, if d i = 0 then (c i).val else 0) = 8 := by
    rw [← Finset.sum_add_distrib, ← hwc]
    apply Finset.sum_congr rfl
    intro i _
    have h : ∀ a b : ZMod 2,
        a.val * b.val + (if b = 0 then a.val else 0) = a.val := by decide
    exact h _ _
  by_contra hne
  have hlo := golayCode_weight_ge_eight (c - d) (golayCode.sub_mem hc hd)
    (sub_ne_zero.mpr hne)
  have hdist := golayBinary_difference_weight c d
  rw [hwc, hwd] at hdist
  change 8 ≤ ∑ i, (c i - d i).val at hlo
  omega

/-- The specified physical support has exactly sixteen complementary coordinates. -/
theorem generatedTenth_e7_octad_complement_card :
    (Finset.univ \ generatedTenthE7OctadSupport).card = 16 := by decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
