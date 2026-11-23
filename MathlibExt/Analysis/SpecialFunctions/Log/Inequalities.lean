/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `bc0a5a31aa07d127ead55e6848aa133300c4ce0a`.
Original formalization by EnayatUllah (@EnayatUllah); ported with permission.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Elementary bounds on `Real.log (1 - x)` and `Real.exp (-x)`

For small nonnegative `x`, the logarithm `log (1 - x)` is squeezed between
`-x - x ^ 2` and `-x`, and the exponential `exp (-x)` is bounded above by
`1 - x + x ^ 2`. The lower log bound is proved by monotonicity of
`t ↦ log (1 - t) + t + t ^ 2` on `[0, 1 / 2]`; the upper log bound is a
specialization of `Real.log_le_sub_one_of_pos`; the exponential bound is
proved by monotonicity of `t ↦ 1 - t + t ^ 2 - exp (-t)` on `[0, ∞)`,
using `Real.add_one_le_exp`.
-/

@[expose] public section

namespace Real

open Set

/-- **Linear upper bound for $\log(1 - x)$.** For every real number $x$ with $1 - x > 0$,
$\log(1 - x) \le -x$. -/
theorem log_one_sub_le_neg (x : ℝ) (h1x : (0 : ℝ) < 1 - x) :
    Real.log (1 - x) ≤ -x := by
  have h := Real.log_le_sub_one_of_pos h1x
  linarith

/-- **Quadratic lower bound for $\log(1 - x)$.** For every real number $x$ with $0 < x < 1/2$,
$-x - x^2 \le \log(1 - x)$. -/
theorem neg_add_sq_le_log_one_sub (x : ℝ) (hx0 : 0 < x) (hx : x < 1 / 2) :
    -x - x ^ 2 ≤ Real.log (1 - x) := by
  have hD : Convex ℝ (Set.Icc (0 : ℝ) (1 / 2)) := convex_Icc 0 (1 / 2)
  have hcont : ContinuousOn (fun t => Real.log (1 - t) + t + t ^ 2)
      (Set.Icc (0 : ℝ) (1 / 2)) := by
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · apply ContinuousOn.log
        · apply Continuous.continuousOn
          exact continuous_const.sub continuous_id
        · intro t ht
          simp only [Set.mem_Icc] at ht
          have hne : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
          exact hne
      · exact continuous_id.continuousOn
    · apply Continuous.continuousOn
      exact continuous_pow 2
  have hdiff : DifferentiableOn ℝ (fun t => Real.log (1 - t) + t + t ^ 2)
      (interior (Set.Icc (0 : ℝ) (1 / 2))) := by
    apply DifferentiableOn.add
    · apply DifferentiableOn.add
      · apply DifferentiableOn.log
        · apply Differentiable.differentiableOn
          exact Differentiable.sub (differentiable_const (1 : ℝ)) differentiable_id
        · intro t ht
          have hsub : t ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset ht
          simp only [Set.mem_Icc] at hsub
          have hne : (1 : ℝ) - t ≠ 0 := by linarith [hsub.2]
          exact hne
      · exact differentiable_id.differentiableOn
    · apply Differentiable.differentiableOn
      exact differentiable_pow 2
  have hnonneg : ∀ t ∈ interior (Set.Icc (0 : ℝ) (1 / 2)),
      0 ≤ deriv (fun t => Real.log (1 - t) + t + t ^ 2) t := by
    intro t ht
    have hmem : t ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
      rwa [interior_Icc] at ht
    simp only [Set.mem_Ioo] at hmem
    obtain ⟨ht0, ht12⟩ := hmem
    have h1t : (0 : ℝ) < 1 - t := by linarith
    have hne : (1 : ℝ) - t ≠ 0 := ne_of_gt h1t
    have hsub : HasDerivAt (fun t : ℝ => (1 : ℝ) - t) (-1) t :=
      (hasDerivAt_id t).const_sub (1 : ℝ)
    have hlog : HasDerivAt (fun t => Real.log (1 - t)) ((-1) / (1 - t)) t :=
      hsub.log hne
    have hid : HasDerivAt (fun t : ℝ => t) (1 : ℝ) t := hasDerivAt_id t
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℝ) * t) t := by
      have h := hasDerivAt_pow 2 (t : ℝ)
      simpa using h
    have hfall : HasDerivAt (fun t => Real.log (1 - t) + t + t ^ 2)
        ((-1) / (1 - t) + 1 + (2 * t)) t :=
      (hlog.add hid).add hpow
    rw [hfall.deriv]
    have heq2 : (-1 : ℝ) / (1 - t) + 1 + (2 * t) = t * (1 - 2 * t) / (1 - t) := by
      field_simp
      ring
    rw [heq2]
    apply div_nonneg _ (le_of_lt h1t)
    have hnn0 : 0 ≤ t := le_of_lt ht0
    have hnn1 : 0 ≤ (1 : ℝ) - 2 * t := by linarith
    exact mul_nonneg hnn0 hnn1
  have hmono : MonotoneOn (fun t => Real.log (1 - t) + t + t ^ 2)
      (Set.Icc (0 : ℝ) (1 / 2)) :=
    monotoneOn_of_deriv_nonneg hD hcont hdiff hnonneg
  have hxmem : x ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨le_of_lt hx0, le_of_lt hx⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨le_rfl, by norm_num⟩
  have hle : (0 : ℝ) ≤ Real.log (1 - x) + x + x ^ 2 := by
    have h := hmono h0mem hxmem hxmem.1
    simpa using h
  linarith

/-- **Two-sided bound for $\log(1 - x)$.** For every real number $x$ with $0 < x < 1/2$,
$-x - x^2 \le \log(1 - x) \le -x$. -/
theorem log_one_sub_bounds (x : ℝ) (hx0 : 0 < x) (hx : x < 1 / 2) :
    -x - x ^ 2 ≤ Real.log (1 - x) ∧ Real.log (1 - x) ≤ -x := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  exact ⟨neg_add_sq_le_log_one_sub x hx0 hx, log_one_sub_le_neg x h1x⟩

/-- **Quadratic upper bound for $e^{-x}$.** For every real number $x \ge 0$,
$e^{-x} \le 1 - x + x^2$. -/
theorem exp_neg_le_one_sub_add_sq (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 := by
  have hf_diff :
      Differentiable ℝ (fun t : ℝ => 1 - t + t ^ 2 - Real.exp (-t)) := by
    fun_prop
  have hf_cont :
      ContinuousOn (fun t : ℝ => 1 - t + t ^ 2 - Real.exp (-t)) (Set.Ici 0) :=
    hf_diff.continuous.continuousOn
  have hf'_diff :
      DifferentiableOn ℝ (fun t : ℝ => 1 - t + t ^ 2 - Real.exp (-t))
        (interior (Set.Ici (0 : ℝ))) :=
    hf_diff.differentiableOn
  have hderiv : ∀ t : ℝ,
      deriv (fun t : ℝ => 1 - t + t ^ 2 - Real.exp (-t)) t
        = -1 + 2 * t + Real.exp (-t) := by
    intro t
    have e1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
    have e2 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
    have e3 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      have h := (hasDerivAt_id t).mul (hasDerivAt_id t)
      have hfun : (id * id : ℝ → ℝ) = (fun t : ℝ => t ^ 2) := by
        funext x
        simp [Pi.mul_apply, id, pow_two]
      rw [hfun] at h
      have hval : (2 * t) = (1 * t + t * 1) := by ring
      rw [hval]
      exact h
    have e4 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
      have h := (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
      simpa [Function.comp_def] using h
    have hcomb := ((e1.sub e2).add e3).sub e4
    have hval : (-1 + 2 * t + Real.exp (-t))
        = ((0 - 1) + 2 * t - -Real.exp (-t)) := by
      ring
    rw [hval]
    exact hcomb.deriv
  have hnonneg : ∀ t ∈ interior (Set.Ici (0 : ℝ)),
      0 ≤ deriv (fun t : ℝ => 1 - t + t ^ 2 - Real.exp (-t)) t := by
    intro t ht
    rw [hderiv t]
    have hexp : 1 + (-t) ≤ Real.exp (-t) := by
      have h := Real.add_one_le_exp (-t)
      linarith
    have ht0 : 0 ≤ t := Set.mem_Ici.mp (interior_subset ht)
    linarith
  have hmono : MonotoneOn (fun t : ℝ => 1 - t + t ^ 2 - Real.exp (-t))
      (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hf_cont hf'_diff hnonneg
  have hle : (fun t : ℝ => 1 - t + t ^ 2 - Real.exp (-t)) 0
      ≤ (fun t : ℝ => 1 - t + t ^ 2 - Real.exp (-t)) x :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [neg_zero, Real.exp_zero] at hle
  norm_num at hle
  linarith

end Real
