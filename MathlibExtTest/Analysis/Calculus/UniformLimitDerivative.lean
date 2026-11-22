/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.UniformLimitDerivative
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace MetaMathlibExt

open Filter Topology Set

/-- Scaled quadratics on `[-1, 1]`: `f n x = (1 - 1 / (n + 1)) * x ^ 2`
converges pointwise to `x ^ 2`, while the derivatives
`f' n x = (1 - 1 / (n + 1)) * (2 * x)` converge uniformly to `2 * x`.
The limit derivative is non-constant, so this exercises the theorem
beyond the constant-derivative case. -/
private lemma quad_hasDerivWithinAt :
    (∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun x => x ^ 2) (2 * x) (Icc (-1 : ℝ) 1) x) ∧
      ContinuousOn (fun x => 2 * x) (Icc (-1 : ℝ) 1) := by
  apply hasDerivWithinAt_of_tendstoUniformlyOn_Icc
    (f := fun n x => (1 - 1 / (↑n + 1 : ℝ)) * x ^ 2)
    (f' := fun n x => (1 - 1 / (↑n + 1 : ℝ)) * (2 * x))
    (g := fun x => x ^ 2) (g' := fun x => 2 * x)
    (show (-1 : ℝ) < 1 by norm_num)
  · intro n x _
    have h := (hasDerivAt_pow 2 x).const_mul (1 - 1 / (↑n + 1 : ℝ))
    simpa using h
  · intro n
    fun_prop
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    refine ⟨N, fun n hn x hx => ?_⟩
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    have hnpos : (0 : ℝ) < (↑n : ℝ) + 1 := by positivity
    have h2 : (2 : ℝ) < ε * (↑n + 1) := by
      have h1 : (2 : ℝ) / ε < (↑n : ℝ) + 1 :=
        lt_of_lt_of_le hN (by exact_mod_cast hn.trans (Nat.le_succ n))
      rwa [div_lt_iff₀ hε, mul_comm] at h1
    have hdiff : 2 * x - (1 - 1 / (↑n + 1 : ℝ)) * (2 * x)
        = (2 * x) / (↑n + 1) := by
      field_simp
      ring
    rw [Real.dist_eq, hdiff, abs_div, abs_of_pos hnpos]
    calc |2 * x| / (↑n + 1)
        ≤ 2 / (↑n + 1) := by
          apply div_le_div_of_nonneg_right _ hnpos.le
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          linarith
      _ < ε := by rwa [div_lt_iff₀ hnpos]
  · intro x _
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (↑n + 1)) atTop (𝓝 1) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.mul (tendsto_const_nhds (x := x ^ 2))
    simpa only [one_mul] using h2

/-- The left endpoint `-1`: the within-derivative of `x ^ 2` there is
`2 * (-1) = -2`. This is the one-sided conclusion Mathlib's open-set
theorem does not provide. -/
example : HasDerivWithinAt (fun x : ℝ => x ^ 2) (-2) (Icc (-1 : ℝ) 1) (-1) := by
  simpa using quad_hasDerivWithinAt.1 (-1) (by norm_num)

/-- The right endpoint `1`: the within-derivative of `x ^ 2` there is `2`. -/
example : HasDerivWithinAt (fun x : ℝ => x ^ 2) 2 (Icc (-1 : ℝ) 1) 1 := by
  simpa using quad_hasDerivWithinAt.1 1 (by norm_num)

/-- Interior points upgrade to ordinary derivatives. -/
example : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  intro x hx
  exact (quad_hasDerivWithinAt.1 x (Ioo_subset_Icc_self hx)).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)

/-- The continuity conclusion of the theorem, for the quadratic family. -/
example : ContinuousOn (fun x : ℝ => 2 * x) (Icc (-1 : ℝ) 1) :=
  quad_hasDerivWithinAt.2

/-- A trigonometric family on `[0, 1]`: `f n x = x + sin x / (n + 1)`
converges pointwise to the identity, while the derivatives
`f' n x = 1 + cos x / (n + 1)` converge uniformly to the constant
function `1`. -/
private lemma trig_hasDerivWithinAt :
    ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => x) 1 (Icc (0 : ℝ) 1) x := by
  have h := (hasDerivWithinAt_of_tendstoUniformlyOn_Icc
    (f := fun n x => x + Real.sin x / (↑n + 1 : ℝ))
    (f' := fun n x => 1 + Real.cos x / (↑n + 1 : ℝ))
    (g := fun x => x) (g' := fun _ => 1)
    (show (0 : ℝ) < 1 by norm_num)
    (by
      intro n x _
      show HasDerivAt (fun y => y + Real.sin y / (↑n + 1 : ℝ))
        (1 + Real.cos x / (↑n + 1 : ℝ)) x
      exact (hasDerivAt_id' x).add ((Real.hasDerivAt_sin x).div_const (↑n + 1 : ℝ)))
    (by
      intro n
      fun_prop)
    (by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      rw [Filter.eventually_atTop]
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun n hn x hx => ?_⟩
      have hnpos : (0 : ℝ) < (↑n : ℝ) + 1 := by positivity
      have h1 : (1 : ℝ) < ε * (↑n + 1) := by
        have hh : (1 : ℝ) / ε < (↑n : ℝ) + 1 :=
          lt_of_lt_of_le hN (by exact_mod_cast hn.trans (Nat.le_succ n))
        rwa [div_lt_iff₀ hε, mul_comm] at hh
      have hdiff : 1 - (1 + Real.cos x / (↑n + 1 : ℝ))
          = -(Real.cos x / (↑n + 1)) := by ring
      rw [Real.dist_eq, hdiff, abs_neg, abs_div, abs_of_pos hnpos]
      calc |Real.cos x| / (↑n + 1)
          ≤ 1 / (↑n + 1) :=
            div_le_div_of_nonneg_right (Real.abs_cos_le_one x) hnpos.le
        _ < ε := by rwa [div_lt_iff₀ hnpos])
    (by
      intro x _
      have h1 : Tendsto (fun n : ℕ => Real.sin x / (↑n + 1)) atTop (𝓝 0) := by
        have hh := (tendsto_const_nhds (x := Real.sin x)).mul
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [one_div, div_eq_mul_inv, mul_zero, mul_one, one_mul] using hh
      simpa only [add_zero] using (tendsto_const_nhds (x := x)).add h1)).1
  exact h

/-- The trigonometric family at the left endpoint `0`. -/
example : HasDerivWithinAt (fun x : ℝ => x) 1 (Icc (0 : ℝ) 1) 0 :=
  trig_hasDerivWithinAt 0 (by norm_num)

end MetaMathlibExt
