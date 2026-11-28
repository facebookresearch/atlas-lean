/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Berkson's bias: selection into hospital

With independent admission triggers of common probability $1-t$ and no admission without a
trigger ($t_0=1$), the probability of admission for exactly $k$ diagnoses is $f_k=1-t^k$.
For $0\le t<1$, the ratios $f_2/f_1$ and $f_3/f_1$ equal $1+t$ and $1+t+t^2$. These are
inflation factors for multiple-to-single diagnosis ratios, strictly greater than $1$ when
$0<t<1$. At $t=0$ every person with at least one diagnosis is admitted, so both factors are $1$.
As $t$ tends to $1$ from below, the factors tend to $2$ and $3$; at $t=1$ the ratios have zero
denominators.

## References

* Joseph Berkson, *Limitations of the Application of Fourfold Table Analysis to Hospital Data*,
  Biometrics Bulletin 2 (1946), no. 3, pp. 47–53, especially p. 49, the unnumbered
  equal-selective-rate formulas and discussion preceding Tables 6 and 7.
-/

namespace WantedExt.Biology.StatisticalGenetics.BerksonBiasWanted

open Filter Topology

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

/-- **Admitted persons with multiple diagnoses are over-represented** (Berkson 1946). For a
common probability `t ∈ [0, 1)` of not triggering admission (selective rate `1 - t`) and `t₀ = 1`,
`f_2 / f_1 = (1 - t²) / (1 - t) = 1 + t` and `f_3 / f_1 = (1 - t³) / (1 - t) = 1 + t + t²`;
as the selective rate tends to `0` (`t → 1⁻`) these ratios tend to `2` and `3`.

Source: Berkson (1946), on the ratio of multiple to single diagnoses being "about twice" and
"about three times"; the exact ratios follow from the selection model. -/
public theorem admission_ratios :
    (∀ t : ℝ, 0 ≤ t → t < 1 →
      (1 - t ^ 2) / (1 - t) = 1 + t ∧ (1 - t ^ 3) / (1 - t) = 1 + t + t ^ 2) ∧
    Tendsto (fun t : ℝ => (1 - t ^ 2) / (1 - t)) (𝓝[<] 1) (𝓝 2) ∧
    Tendsto (fun t : ℝ => (1 - t ^ 3) / (1 - t)) (𝓝[<] 1) (𝓝 3) := by
  have hquot (n : ℕ) {t : ℝ} (ht : t < 1) :
      (1 - t ^ n) / (1 - t) = ∑ i ∈ Finset.range n, t ^ i :=
    (div_eq_iff_mul_eq (sub_ne_zero.mpr ht.ne.symm)).2 (geom_sum_mul_neg t n)
  have hlim (n : ℕ) :
      Tendsto (fun t : ℝ => (1 - t ^ n) / (1 - t)) (𝓝[<] 1) (𝓝 (n : ℝ)) := by
    have hcont : Continuous (fun t : ℝ => ∑ i ∈ Finset.range n, t ^ i) :=
      continuous_finsetSum _ fun i _ => continuous_id.pow i
    have htend :
        Tendsto (fun t : ℝ => ∑ i ∈ Finset.range n, t ^ i) (𝓝[<] 1) (𝓝 (n : ℝ)) := by
      simpa only [ContinuousWithinAt, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one] using (hcont.continuousWithinAt (s := Set.Iio 1) (x := 1))
    refine htend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hquot n (Set.mem_Iio.mp ht)).symm
  refine ⟨?_, hlim 2, hlim 3⟩
  intro t _ ht
  simp only [hquot _ ht, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, and_self]

end WantedExt.Biology.StatisticalGenetics.BerksonBiasWanted
