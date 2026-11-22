/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# The Riemannian volume measure

We define the Riemannian volume measure of an `n`-dimensional Riemannian manifold as the
normalized `n`-dimensional Hausdorff measure of its Riemannian distance,
```
vol = (ω_n / 2 ^ n) • μH[n],
```
where `ω_n` is the volume of the unit ball of `ℝⁿ` and `μH[n]` is Mathlib's (unnormalized)
Hausdorff measure, whose content of a set of diameter `r` is `r ^ n`. The factor `ω_n / 2 ^ n` is
the usual normalization of the Hausdorff measure, the gauge `ω_n (diam S / 2) ^ n` (Terra,
*Introduction to Geometric Measure Theory*, IME-USP lecture notes, Def. 2.3; Evans–Gariepy's
scaled Hausdorff measure), which agrees with Lebesgue measure on `ℝⁿ`. On an `n`-dimensional
Riemannian manifold with a `C^∞` metric whose distance is the Riemannian distance
(`[IsRiemannianManifold I M]`), this measure is the Riemannian volume, given in charts by the
density `√det (g_ij)` against Lebesgue measure ("in a Riemannian manifold of dimension n, Hⁿ
coincides with the standard volume", Encyclopedia of Mathematics, "Hausdorff measure"; a
consequence of the area formula). It is stated here as known, not proved: Mathlib has neither
Riemannian densities nor the isodiametric inequality.

## Main definitions and results

* `Manifold.normalizedHausdorffMeasure n X`: the normalized `n`-dimensional Hausdorff measure
  `(ω_n / 2 ^ n) • μH[n]` of an emetric space `X`.
* `Manifold.riemannianVolume I M`: the Riemannian volume of a Riemannian manifold `M` modeled on
  `I : ModelWithCorners ℝ E H`, whose distance is the Riemannian distance: the normalized
  `finrank ℝ E`-dimensional Hausdorff measure.
* `Manifold.riemannianVolume_real`: normalization check in dimension one: the Riemannian volume of
  `ℝ` (with its standard metric, whose distance is the usual one) is Lebesgue measure.
-/

@[expose] public section

open Bundle MeasureTheory Module Metric
open scoped ENNReal Manifold ContDiff

noncomputable section

namespace Manifold

/-- The normalized `n`-dimensional Hausdorff measure `(ω_n / 2 ^ n) • μH[n]` of an emetric space
`X`, where `ω_n` is the volume of the unit ball of `EuclideanSpace ℝ (Fin n)`. With this
normalization it agrees with Lebesgue measure on `ℝⁿ` (classically, by the isodiametric
inequality); `riemannianVolume_real` checks it for `n = 1`. -/
def normalizedHausdorffMeasure (n : ℕ) (X : Type*) [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] : Measure X :=
  (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) • μH[n]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- The Riemannian volume measure of a `C^∞` Riemannian manifold `M` modeled on
`I : ModelWithCorners ℝ E H` with `E` finite-dimensional (so `M` has dimension
`n = finrank ℝ E`), with a `C^∞` metric (`[IsContMDiffRiemannianBundle I ∞ E _]`) and whose distance
is the Riemannian distance (`[IsRiemannianManifold I M]`): the normalized `n`-dimensional Hausdorff
measure of `M` (see the module docstring). The manifold and Riemannian instance arguments are not
used in the formula; they tie the dimension to the model of `M` and restrict the definition to the
setting in which it is the Riemannian volume. -/
@[nolint unusedArguments]
def riemannianVolume [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E H) (M : Type*)
    [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M] : Measure M :=
  normalizedHausdorffMeasure (finrank ℝ E) M

/-- Normalization check: the Riemannian volume of the real line, whose Riemannian distance is the
usual distance, is Lebesgue measure. -/
theorem riemannianVolume_real : riemannianVolume 𝓘(ℝ, ℝ) ℝ = volume := by
  have hball : volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ ℝ))) 1) = 2 := by
    rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by simp)]
    simp
  rw [riemannianVolume, normalizedHausdorffMeasure, hball, finrank_self, pow_one,
    ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top, one_smul, Nat.cast_one,
    hausdorffMeasure_real]

end Manifold
