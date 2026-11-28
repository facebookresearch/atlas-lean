/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.DeletionStability

/-!
# High-probability bound when deletion stability scales as `κ / m`

O. Bousquet and A. Elisseeff, *Stability and Generalization*, JMLR 2 (2002), Theorem 12
(p. 507) and Remark 13. The result below is a corollary of the repository deletion-stability
theorem `IsDeletionStable.highProbability_generalization`, which already supplies inequality
(11) together with the deletion-to-replacement bridge: nothing here re-proves that inequality.
The corollary only substitutes `β = κ / m` with `m = n + 1` for a size-indexed family, the
scaling regime Remark 13 points at.

The sample is i.i.d. from the product measure. The loss profiles at size `n + 1` and at size
`n` are both assumed jointly measurable and valued in `[0, M]`, since those are the repository
theorem hypotheses this specialization uses. Deletion stability holds with bound `κ / m` in the
sense of the displayed `IsDeletionStable` predicate, and `δ ∈ (0, 1)`. The source's
non-increasing `βₘ` convention needs no adjacent-size comparison in this corollary.

For fixed `κ`, `M` and `δ`, the displayed one-sided correction is `O(1 / √m)`.
-/

@[expose] public section

open MeasureTheory Real

namespace CSLibExt.MachineLearning.GeneralizationBounds

/-- High-probability generalization for a size-indexed family whose deletion stability is
`κ / m`. This is the `β = κ / m`, `m = n + 1` specialization of
`IsDeletionStable.highProbability_generalization` (Bousquet–Elisseeff Remark 13 regime): with
probability at least `1 - δ`, the population risk is at most the empirical risk plus the
displayed one-sided correction. -/
theorem IsDeletionStable.one_sub_le_measureReal_risk_le_div
    {𝒵 H : Type*} [MeasurableSpace 𝒵] {ν : Measure 𝒵} [IsProbabilityMeasure ν]
    {L : H → 𝒵 → ℝ} {A : (k : ℕ) → (Fin k → 𝒵) → H} {n : ℕ} {κ M : ℝ}
    (hmeas : Measurable fun p : (Fin (n + 1) → 𝒵) × 𝒵 => L (A (n + 1) p.1) p.2)
    (hmeas' : Measurable fun p : (Fin n → 𝒵) × 𝒵 => L (A n p.1) p.2)
    (hbdd : ∀ S z, L (A (n + 1) S) z ∈ Set.Icc 0 M)
    (hbdd' : ∀ S z, L (A n S) z ∈ Set.Icc 0 M)
    (hstab : IsDeletionStable L (A (n + 1)) (A n) (κ / ((n : ℝ) + 1)))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin (n + 1) => ν).real
      {S | risk L ν (A (n + 1) S) ≤ empiricalRisk L S (A (n + 1) S) +
        2 * κ / ((n : ℝ) + 1) +
        (4 * κ + M) * √(log (1 / δ) / (2 * ((n : ℝ) + 1)))} := by
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
  have hm0 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hcancel : ((n : ℝ) + 1) * (κ / ((n : ℝ) + 1)) = κ := by field_simp
  have e1 : (2 : ℝ) * (κ / ((n : ℝ) + 1)) = 2 * κ / ((n : ℝ) + 1) := by ring
  have e2 : 4 * ((n : ℝ) + 1) * (κ / ((n : ℝ) + 1)) + M = 4 * κ + M := by
    calc 4 * ((n : ℝ) + 1) * (κ / ((n : ℝ) + 1)) + M
        = 4 * (((n : ℝ) + 1) * (κ / ((n : ℝ) + 1))) + M := by ring
      _ = 4 * κ + M := by rw [hcancel]
  obtain ⟨hgen, -⟩ := hstab.highProbability_generalization ν hmeas hmeas' hbdd hbdd' hδ
  rw [hcast, e1, e2] at hgen
  exact hgen

end CSLibExt.MachineLearning.GeneralizationBounds
