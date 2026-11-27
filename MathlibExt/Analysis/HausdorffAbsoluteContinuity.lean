/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The theorem statement and the definition of uniform absolute continuity are adapted from
`LeanEval/Analysis/HausdorffAbsoluteContinuity.lean` (leanprover/lean-eval), commit
38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC. Submitter: Kim Morrison.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.Analysis.HausdorffMoments
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import all MathlibExt.Analysis.HausdorffMoments
import MathlibExt.MeasureTheory.Measure.UniquenessOnRd
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Tactic.Ring

/-!
# Hausdorff's absolute continuity criterion on the unit cube

For a probability measure carried by the closed unit cube, domination by a nonnegative multiple of
restricted Lebesgue measure is equivalent to domination of all its iterated backward moment
differences with coordinatewise `k ≤ n` by one real multiple of the corresponding differences for
restricted Lebesgue measure. This is the Lebesgue specialization of the two-probability-measure
comparison in Knill's §115. The restriction `k ≤ n` is the range in which the backward differences
are defined without extending the sequence to negative indices.

## References

* Oliver Knill, *Some Fundamental Theorems in Mathematics*, arXiv:1807.08416v4 (2022),
  §115 (Moments), p. 52, the comparison of two probability measures by their moment differences.
* F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*, Mathematische Zeitschrift 9 (1921),
  pp. 74–109 and 280–299, for the one-dimensional moment problem.
* T. H. Hildebrandt and I. J. Schoenberg, *On Linear Functional Operations and the Moment Problem
  for a Finite Interval in One or Several Dimensions*, The Annals of Mathematics 34 (1933),
  pp. 317–328, for the multivariate moment problem.
* `MathlibExt.Analysis.HausdorffMoments`: `hausdorff_positivity`, `compact_cube`, and
  `continuous_monomial` are used for the positive residual measure and its moments.
* `MathlibExt.MeasureTheory.Measure.UniquenessOnRd`:
  `MeasureTheory.Measure.eq_of_forall_integral_monomial_eq` identifies the restricted measures
  from their mixed moments.
-/

namespace MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted.Analysis.HausdorffAbsoluteContinuity

open MeasureTheory
open scoped BigOperators NNReal

open MathlibExt.Analysis.HausdorffMomentsWanted.Analysis

@[expose] public section

set_option linter.dupNamespace false in
/-- **Uniformly absolutely continuous measures.** A measure $\mu$ on $\mathbb{R}^d$ is uniformly
absolutely continuous with respect to a measure $\nu$ on $\mathbb{R}^d$ if there is a real
constant $C \ge 0$ with $\mu(S) \le C \, \nu(S)$ for every measurable set $S$.

When $\nu$ is $\sigma$-finite, this says that $\mu$ has an essentially bounded Radon–Nikodym
density with respect to $\nu$. -/
def UniformlyAbsolutelyContinuous {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ C : ℝ≥0, μ ≤ C • ν

end

variable {d : ℕ}

private theorem restrict_eq_of_moments {μ ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ∀ n, momentOf μ n = momentOf ν n) :
    μ.restrict (cube d) = ν.restrict (cube d) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin d => ℝ)
  let E := e '' cube d
  have hE : IsCompact E := compact_cube.image e.continuous
  have hsupport (ξ : Measure (EuclideanSpace ℝ (Fin d))) :
      ((ξ.restrict (cube d)).map e) Eᶜ = 0 := by
    rw [Measure.map_apply e.measurable hE.measurableSet.compl, Set.preimage_compl,
      show e ⁻¹' E = cube d from e.injective.preimage_image _,
      Measure.restrict_apply compact_cube.measurableSet.compl, Set.compl_inter_self, measure_empty]
  apply e.measurableEmbedding.map_injective
  apply Measure.eq_of_forall_integral_monomial_eq hE _ _ (hsupport μ) (hsupport ν)
  intro n
  rw [e.measurableEmbedding.integral_map, e.measurableEmbedding.integral_map]
  exact h n

private theorem momentOf_add {μ ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : Fin d → ℕ) :
    momentOf (μ + ν) n = momentOf μ n + momentOf ν n := by
  simp only [momentOf, Measure.restrict_add]
  exact integral_add_measure
    ((continuous_monomial n).continuousOn.integrableOn_compact compact_cube)
    ((continuous_monomial n).continuousOn.integrableOn_compact compact_cube)

private theorem momentOf_smul (r : ℝ≥0) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (n : Fin d → ℕ) : momentOf (r • μ) n = (r : ℝ) * momentOf μ n := by
  rw [momentOf, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  rfl

private theorem diff_smul_sub (c : ℝ) (a b : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) :
    diff (fun j => c * a j - b j) k n = c * diff a k n - diff b k n := by
  simp only [diff, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem diff_zero (a : (Fin d → ℕ) → ℝ) : diff a 0 0 = a 0 := by
  have hIic : Finset.Iic (0 : Fin d → ℕ) = {0} := Finset.Iic_bot
  have hsub : (0 : Fin d → ℕ) - 0 = 0 := funext fun _ => Nat.sub_zero 0
  simp [diff, multiChoose, hIic, hsub]

set_option linter.dupNamespace false in
/-- **Hausdorff's absolute continuity criterion.** Let $\mu$ be a probability measure on
$\mathbb{R}^d$ with $\mu(\mathbb{R}^d \setminus I^d) = 0$, where $I^d = [0,1]^d$ is the closed
unit cube, and let $\lambda$ be Lebesgue measure restricted to $I^d$. For a measure $\rho$ write
$m_\rho(n) = \int_{I^d} x^n \, d\rho(x)$ for its moments, indexed by multi-indices
$n \in \mathbb{N}^d$. Then $\mu$ is uniformly absolutely continuous with respect to $\lambda$ if
and only if there is a real constant $C$ such that
$(\Delta^k m_\mu)_n \le C \, (\Delta^k m_\lambda)_n$ for all multi-indices $k \le n$
(coordinatewise), where $\Delta^k$ is the iterated backward difference.

Source: F. Hausdorff (1921–1923); see Shohat–Tamarkin, *The Problem of Moments*.
Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem
`hausdorff_absolute_continuity`. -/
public theorem hausdorff_absolute_continuity {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (hμ : μ ((cube d)ᶜ) = 0) :
    UniformlyAbsolutelyContinuous μ (volume.restrict (cube d)) ↔
      ∃ C : ℝ, ∀ k n : Fin d → ℕ, k ≤ n →
        diff (momentOf μ) k n ≤ C * diff (momentOf (volume.restrict (cube d))) k n := by
  let ν₀ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (cube d)
  have : IsFiniteMeasure ν₀ := isFiniteMeasure_restrict.mpr compact_cube.measure_ne_top
  change (∃ c : ℝ≥0, μ ≤ c • ν₀) ↔ ∃ C : ℝ, ∀ k n : Fin d → ℕ, k ≤ n →
    diff (momentOf μ) k n ≤ C * diff (momentOf ν₀) k n
  have hμr : μ.restrict (cube d) = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)
  have hνr : ν₀.restrict (cube d) = ν₀ := Measure.restrict_restrict_of_subset Set.Subset.rfl
  constructor
  · rintro ⟨c, hc⟩
    let ρ := c • ν₀ - μ
    have : IsFiniteMeasure ρ := isFiniteMeasure_of_le _ Measure.sub_le
    have hρ : ρ + μ = c • ν₀ := Measure.sub_add_cancel_of_le hc
    have hm (n : Fin d → ℕ) : (c : ℝ) * momentOf ν₀ n - momentOf μ n = momentOf ρ n := by
      rw [← momentOf_smul, ← hρ, momentOf_add, add_sub_cancel_right]
    refine ⟨c, fun k n hkn => sub_nonneg.mp ?_⟩
    rw [← diff_smul_sub, show (fun j => (c : ℝ) * momentOf ν₀ j - momentOf μ j) =
      momentOf ρ from funext hm]
    exact (hausdorff_positivity _).mp ⟨ρ, inferInstance, fun _ => rfl⟩ k n hkn
  · rintro ⟨C, hC⟩
    have hzero := hC 0 0 le_rfl
    rw [diff_zero, diff_zero] at hzero
    have hm0 : momentOf μ 0 = 1 := by simp [momentOf, monomial, hμr]
    have hl0 : 0 ≤ momentOf ν₀ 0 := by simp [momentOf, monomial, hνr]
    have hC0 : 0 ≤ C := by
      by_contra! hneg
      rw [hm0] at hzero
      exact (not_le_of_gt zero_lt_one) (hzero.trans (mul_nonpos_of_nonpos_of_nonneg hneg.le hl0))
    let c : ℝ≥0 := ⟨C, hC0⟩
    obtain ⟨ρ, hρfin, hρ⟩ := (hausdorff_positivity
      (fun j => C * momentOf ν₀ j - momentOf μ j)).mpr fun k n hkn => by
        rw [diff_smul_sub]
        exact sub_nonneg.mpr (hC k n hkn)
    have hm (n : Fin d → ℕ) : momentOf (ρ + μ) n = momentOf (c • ν₀) n := by
      rw [momentOf_add, momentOf_smul, ← hρ, sub_add_cancel]
      rfl
    have heq := restrict_eq_of_moments hm
    rw [Measure.restrict_add, Measure.restrict_smul, hνr, hμr] at heq
    exact ⟨c, heq ▸ Measure.le_add_left le_rfl⟩

end MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted.Analysis.HausdorffAbsoluteContinuity
