/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace WantedExt.Biology.StatisticalGenetics.BerksonBiasWanted

/-- **The odds ratio among admitted persons, two diseases** (Berkson 1946). For two independent
diseases in the population with incidences `p_a, p_b ∈ (0, 1)`, probabilities `t_a, t_b ∈ [0, 1)`
of not triggering admission and `t₀ ∈ (0, 1]`, the admitted masses are `p_a p_b f_{ab}`,
`p_a (1 - p_b) f_a`, `(1 - p_a) p_b f_b` and `(1 - p_a)(1 - p_b) f_∅`, with
`f_{ab} = 1 - t₀ t_a t_b`, `f_a = 1 - t₀ t_a`, `f_b = 1 - t₀ t_b` and `f_∅ = 1 - t₀`. The odds
ratio between the diseases among admitted persons is `f_{ab} f_∅ / (f_a f_b)`, and it is strictly
less than `1`.

Source: Berkson (1946); derived from his selection model. -/
public theorem hospitalOddsRatio (pa pb ta tb t₀ : ℝ) (hpa0 : 0 < pa) (hpa1 : pa < 1)
    (hpb0 : 0 < pb) (hpb1 : pb < 1) (hta0 : 0 ≤ ta) (hta1 : ta < 1) (htb0 : 0 ≤ tb)
    (htb1 : tb < 1) (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1) :
    (pa * pb * (1 - t₀ * ta * tb)) * ((1 - pa) * (1 - pb) * (1 - t₀)) /
          ((pa * (1 - pb) * (1 - t₀ * ta)) * ((1 - pa) * pb * (1 - t₀ * tb))) =
        (1 - t₀ * ta * tb) * (1 - t₀) / ((1 - t₀ * ta) * (1 - t₀ * tb)) ∧
      (1 - t₀ * ta * tb) * (1 - t₀) / ((1 - t₀ * ta) * (1 - t₀ * tb)) < 1 := by
  have hfa : 0 < 1 - t₀ * ta := sub_pos.mpr (calc
    t₀ * ta ≤ 1 * ta := mul_le_mul_of_nonneg_right ht₀' hta0
    _ < 1 := by simpa only [one_mul] using hta1)
  have hfb : 0 < 1 - t₀ * tb := sub_pos.mpr (calc
    t₀ * tb ≤ 1 * tb := mul_le_mul_of_nonneg_right ht₀' htb0
    _ < 1 := by simpa only [one_mul] using htb1)
  constructor
  · let c := pa * pb * (1 - pa) * (1 - pb)
    have hc : c ≠ 0 :=
      (mul_pos (mul_pos (mul_pos hpa0 hpb0) (sub_pos.mpr hpa1)) (sub_pos.mpr hpb1)).ne'
    calc
      _ = c * ((1 - t₀ * ta * tb) * (1 - t₀)) / (c * ((1 - t₀ * ta) * (1 - t₀ * tb))) := by
        dsimp only [c]
        congr 1 <;> ring
      _ = _ := mul_div_mul_left _ _ hc
  · rw [div_lt_iff₀ (mul_pos hfa hfb), one_mul]
    apply sub_pos.mp
    calc
      0 < t₀ * (1 - ta) * (1 - tb) := mul_pos (mul_pos ht₀ (sub_pos.mpr hta1)) (sub_pos.mpr htb1)
      _ = _ := by ring

end WantedExt.Biology.StatisticalGenetics.BerksonBiasWanted
