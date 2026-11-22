/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import MathlibExt.Topology.Order.LocalExtr

/-!
# Strict second-derivative test

Mathlib's second-derivative test
(`isLocalMin_of_deriv_deriv_pos`, `isLocalMax_of_deriv_deriv_neg` in
`Mathlib/Analysis/Calculus/DerivativeTest.lean`) concludes only the
non-strict `IsLocalMin` / `IsLocalMax`: the function value at the critical
point is `≤` nearby values. This file adds the strict version: under the
same hypotheses, the critical point is a *strict* local extremum, i.e. the
inequality is strict at every distinct nearby point.
`MathlibExt.Topology.Order.LocalExtr` supplies the generic strict predicates,
the bridge lemmas back to Mathlib's non-strict notions, and the negation
lemmas used to derive the maximum version from the minimum version.

The proof goes through the sign of the first derivative: if
`deriv (deriv f) x₀ > 0` and `deriv f x₀ = 0`, then
`eventually_nhdsWithin_sign_eq_of_deriv_pos` says `deriv f` is negative
just left of `x₀` and positive just right of `x₀`, so `f` is strictly
antitone on an interval ending at `x₀` and strictly monotone on an
interval starting at `x₀` (`strictAntiOn_of_deriv_neg`,
`strictMonoOn_of_deriv_pos`).

## Main results

* `isStrictLocalMin_of_deriv_deriv_pos`: the strict second-derivative
  test, minimum version.
* `isStrictLocalMax_of_deriv_deriv_neg`: the strict second-derivative
  test, maximum version.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, **Theorem (Second Derivative
Test)**, "Taylor's Theorem section", and
`v1/Atlas/RealAnalysis/code/Derivatives/Taylor.lean`
(`second_derivative_test_min`). The v1 statement assumes `ContDiffAt ℝ 2`
and concludes `IsStrictLocalMin` with `iteratedDeriv 2 f x₀ > 0`. Here the
hypotheses are Mathlib's weaker ones (`deriv (deriv f) x₀ > 0` and
`ContinuousAt f x₀`, no `ContDiffAt` needed: the sign of `deriv f` near
`x₀` comes from Mathlib's sign lemma, and the strict-monotonicity lemmas
derive differentiability on the interval interiors from that sign, so
continuity at `x₀` itself is the only extra hypothesis), the minimum
version is stated in Mathlib's `deriv (deriv f)` form, and the maximum
version (absent from v1) is added.
-/

@[expose] public section

open Filter Topology

/-- **Strict second-derivative test, minimum version.** If the second
derivative of `f` at `x₀` is positive, the first derivative vanishes
there, and `f` is continuous there, then `f` has a strict local minimum
at `x₀`.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorem (Second Derivative
Test), as strengthened in this file's header: the v1 `ContDiffAt ℝ 2`
hypothesis is weakened to `ContinuousAt`, and `iteratedDeriv 2` is written
in Mathlib's `deriv (deriv f)` form. -/
theorem isStrictLocalMin_of_deriv_deriv_pos {f : ℝ → ℝ} {x₀ : ℝ}
    (hf : 0 < deriv (deriv f) x₀) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsStrictLocalMin f x₀ := by
  have hsign : ∀ᶠ x in 𝓝 x₀, SignType.sign (deriv f x) = SignType.sign (x - x₀) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd
  rw [Metric.eventually_nhds_iff] at hsign
  obtain ⟨δ, hδ, hsign⟩ := hsign
  have hdiff_of_ne : ∀ z : ℝ, z ≠ x₀ → dist z x₀ < δ → DifferentiableAt ℝ f z := by
    intro z hz0 hdist
    have hsz := hsign hdist
    have hne : SignType.sign (z - x₀) ≠ 0 := by
      rw [Ne, sign_eq_zero_iff]
      exact sub_ne_zero.mpr hz0
    have hderiv : deriv f z ≠ 0 := by
      intro h0
      rw [h0, sign_zero] at hsz
      exact hne hsz.symm
    exact differentiableAt_of_deriv_ne_zero hderiv
  show ∀ᶠ x in 𝓝[≠] x₀, f x₀ < f x
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun {y} hy hyne => ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hyne
  rcases lt_or_gt_of_ne hyne with hlt | hgt
  · -- `y < x₀`: `f` is strictly antitone on `[y, x₀]`, so `f x₀ < f y`.
    have hdist_le : ∀ z ∈ Set.Icc y x₀, dist z x₀ ≤ dist y x₀ := by
      intro z hz
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [hz.2] : z - x₀ ≤ 0),
        abs_of_nonpos (by linarith [hlt] : y - x₀ ≤ 0)]
      linarith [hz.1]
    have hcont : ContinuousOn f (Set.Icc y x₀) := by
      intro z hz
      by_cases hz0 : z = x₀
      · subst hz0
        exact hc.continuousWithinAt
      · exact (hdiff_of_ne z hz0 (lt_of_le_of_lt (hdist_le z hz) hy)).continuousAt.continuousWithinAt
    have hanti : StrictAntiOn f (Set.Icc y x₀) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc y x₀) hcont
      intro z hz
      rw [interior_Icc] at hz
      have hz0 : z ≠ x₀ := ne_of_lt hz.2
      have hsz :=
        hsign (lt_of_le_of_lt (hdist_le z (Set.Ioo_subset_Icc_self hz)) hy)
      have hneg : z - x₀ < 0 := by linarith [hz.2]
      rw [sign_neg hneg] at hsz
      exact sign_eq_neg_one_iff.mp hsz
    exact hanti (Set.left_mem_Icc.mpr hlt.le) (Set.right_mem_Icc.mpr hlt.le) hlt
  · -- `x₀ < y`: `f` is strictly monotone on `[x₀, y]`, so `f x₀ < f y`.
    have hdist_le : ∀ z ∈ Set.Icc x₀ y, dist z x₀ ≤ dist y x₀ := by
      intro z hz
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - x₀),
        abs_of_nonneg (by linarith [hgt] : 0 ≤ y - x₀)]
      linarith [hz.2]
    have hcont : ContinuousOn f (Set.Icc x₀ y) := by
      intro z hz
      by_cases hz0 : z = x₀
      · subst hz0
        exact hc.continuousWithinAt
      · exact (hdiff_of_ne z hz0 (lt_of_le_of_lt (hdist_le z hz) hy)).continuousAt.continuousWithinAt
    have hmono : StrictMonoOn f (Set.Icc x₀ y) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc x₀ y) hcont
      intro z hz
      rw [interior_Icc] at hz
      have hz0 : z ≠ x₀ := ne_of_gt hz.1
      have hsz :=
        hsign (lt_of_le_of_lt (hdist_le z (Set.Ioo_subset_Icc_self hz)) hy)
      have hpos : 0 < z - x₀ := by linarith [hz.1]
      rw [sign_pos hpos] at hsz
      exact sign_eq_one_iff.mp hsz
    exact hmono (Set.left_mem_Icc.mpr hgt.le) (Set.right_mem_Icc.mpr hgt.le) hgt

/-- **Strict second-derivative test, maximum version.** If the second
derivative of `f` at `x₀` is negative, the first derivative vanishes
there, and `f` is continuous there, then `f` has a strict local maximum
at `x₀`. This is the minimum version applied to `-f`. -/
theorem isStrictLocalMax_of_deriv_deriv_neg {f : ℝ → ℝ} {x₀ : ℝ}
    (hf : deriv (deriv f) x₀ < 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsStrictLocalMax f x₀ := by
  simpa using isStrictLocalMin_of_deriv_deriv_pos (f := (-f ·))
    (by simpa) (by simpa) hc.neg |>.neg
