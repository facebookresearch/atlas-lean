/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Series with a rising-product denominator

The series `∑ j, (-b) ^ j * x ^ (j + 1) / ∏ r < j + 1, (c + b * (r + 1))` converges for every `x`
whenever no factor of its denominator vanishes:
`Complex.summable_neg_pow_mul_pow_div_prod_add_mul`.
-/

namespace Complex

/-- **Summability of a rising-product series.** Let $b$, $c$ and $x$ be complex numbers such
that $c + kb \neq 0$ for every integer $k \ge 1$. Then the series
$\sum_{j=0}^{\infty} \frac{(-b)^j x^{j+1}}{\prod_{k=1}^{j+1} (c + kb)}$ is summable. -/
theorem summable_neg_pow_mul_pow_div_prod_add_mul {b c : ℂ} (x : ℂ)
    (hc : ∀ r : ℕ, c + b * ((r + 1 : ℕ) : ℂ) ≠ 0) :
    Summable (fun j : ℕ =>
      (-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1), (c + b * ((r + 1 : ℕ) : ℂ))) := by
  rcases eq_or_ne b 0 with rfl | hb
  · refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    simp [Finset.mem_singleton.not.mp hj]
  rcases eq_or_ne x 0 with rfl | hx
  · -- When `x = 0` every summand vanishes.
    have h0 : (fun j : ℕ => ((-b) ^ j * (0 : ℂ) ^ (j + 1) /
        ∏ r ∈ Finset.range (j + 1), (c + b * (((r + 1 : ℕ)) : ℂ)))) = 0 := by
      funext j
      simp only [Pi.zero_apply]
      have hj : j + 1 ≠ 0 := by omega
      rw [zero_pow hj, mul_zero, zero_div]
    rw [h0]
    exact summable_zero
  · -- Otherwise the ratio test applies: `‖f (n+1)‖ / ‖f n‖ = ‖x‖ / ‖c / b + (n+2)‖ → 0`.
    refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num) ?_ ?_
    · apply Filter.Eventually.of_forall
      intro n
      simp only [ne_eq]
      apply div_ne_zero
      · exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hb)) (pow_ne_zero _ hx)
      · apply Finset.prod_ne_zero_iff.mpr
        intro r _
        exact hc r
    · have htop : Filter.Tendsto (fun n : ℕ => ‖c / b + ((n : ℂ) + 2)‖)
          Filter.atTop Filter.atTop := by
        have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + (-‖c / b + 2‖)))
            Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right Filter.atTop _
            tendsto_natCast_atTop_atTop
        refine Filter.tendsto_atTop_mono (fun n => ?_) h1
        have hle := norm_sub_norm_le ((n : ℂ)) (-(c / b + 2))
        rw [norm_neg, Complex.norm_natCast] at hle
        have heq : ((n : ℂ)) - (-(c / b + 2))
            = c / b + 2 + ((n : ℂ)) := by ring
        have heq2 : c / b + 2 + ((n : ℂ)) = c / b + ((n : ℂ) + 2) := by
          ring
        rw [heq, heq2] at hle
        linarith
      have hratio : (fun n : ℕ => ‖x‖ / ‖c / b + ((n : ℂ) + 2)‖) =
          (fun n : ℕ => ‖(fun j : ℕ => ((-b) ^ j * x ^ (j + 1) /
          ∏ r ∈ Finset.range (j + 1), (c + b * (((r + 1 : ℕ)) : ℂ)))) (n + 1)‖ /
          ‖(fun j : ℕ => ((-b) ^ j * x ^ (j + 1) /
          ∏ r ∈ Finset.range (j + 1), (c + b * (((r + 1 : ℕ)) : ℂ)))) n‖) := by
        funext n
        have hrec : (fun j : ℕ => ((-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1),
              (c + b * (((r + 1 : ℕ)) : ℂ)))) (n + 1) =
            (fun j : ℕ => ((-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1),
              (c + b * (((r + 1 : ℕ)) : ℂ)))) n *
            (-x / (c / b + ((n : ℂ) + 2))) := by
          simp only
          have hPn : ∏ r ∈ Finset.range (n + 1 + 1),
              (c + b * (((r + 1 : ℕ)) : ℂ)) =
              (∏ r ∈ Finset.range (n + 1), (c + b * (((r + 1 : ℕ)) : ℂ))) *
                (c + b * ((((n + 1 + 1 : ℕ))) : ℂ)) :=
            Finset.prod_range_succ _ _
          have hN : (-b : ℂ) ^ (n + 1) * x ^ (n + 1 + 1) =
              ((-b) ^ n * x ^ (n + 1)) * ((-b) * x) := by ring
          have hcast : ((((n + 1 + 1 : ℕ))) : ℂ) = ((n : ℂ) + 2) := by
            push_cast
            ring
          have hF : c + b * ((((n + 1 + 1 : ℕ))) : ℂ) =
              b * (c / b + ((n : ℂ) + 2)) := by
            rw [hcast]
            field_simp
          have hFne : c / b + ((n : ℂ) + 2) ≠ 0 := by
            intro hz
            apply hc (n + 1)
            rw [hF, hz, mul_zero]
          have hPne : (∏ r ∈ Finset.range (n + 1),
              (c + b * (((r + 1 : ℕ)) : ℂ))) ≠ 0 := by
            apply Finset.prod_ne_zero_iff.mpr
            intro r _
            exact hc r
          rw [hPn, hN, hF]
          field_simp
        have hNn : ‖(-b : ℂ) ^ n * x ^ (n + 1)‖ ≠ 0 := by
          apply ne_of_gt
          apply norm_pos_iff.mpr
          apply mul_ne_zero
          · exact pow_ne_zero _ (neg_ne_zero.mpr hb)
          · exact pow_ne_zero _ hx
        have hPn2 : ‖(∏ r ∈ Finset.range (n + 1),
            (c + b * (((r + 1 : ℕ)) : ℂ)))‖ ≠ 0 := by
          apply ne_of_gt
          apply norm_pos_iff.mpr
          apply Finset.prod_ne_zero_iff.mpr
          intro r _
          exact hc r
        have hW : ‖c / b + ((n : ℂ) + 2)‖ ≠ 0 := by
          apply ne_of_gt
          apply norm_pos_iff.mpr
          intro hz
          apply hc (n + 1)
          have hcast : ((((n + 1 + 1 : ℕ))) : ℂ) = ((n : ℂ) + 2) := by
            push_cast
            ring
          have hF : c + b * ((((n + 1 + 1 : ℕ))) : ℂ) =
              b * (c / b + ((n : ℂ) + 2)) := by
            rw [hcast]
            field_simp
          rw [hF, hz, mul_zero]
        have hB : (‖(-b : ℂ) ^ n * x ^ (n + 1)‖ /
            ‖(∏ r ∈ Finset.range (n + 1),
              (c + b * (((r + 1 : ℕ)) : ℂ)))‖) ≠ 0 :=
          div_ne_zero hNn hPn2
        rw [hrec, norm_mul, norm_div, norm_div, norm_neg]
        field_simp
      rw [← hratio]
      exact Filter.Tendsto.const_div_atTop htop _

end Complex
