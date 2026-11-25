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

/-- **Normalized Hausdorff measure.** Let $n$ be a natural number and let $X$ be an extended
metric space with its Borel $\sigma$-algebra. The normalized $n$-dimensional Hausdorff measure of
$X$ is the measure $\frac{\omega_n}{2^n} \mathcal{H}^n$, where $\omega_n$ is the Lebesgue volume of
the open unit ball of the Euclidean space $\mathbb{R}^n$ and $\mathcal{H}^n$ is the unnormalized
$n$-dimensional Hausdorff measure, in which a set of diameter $r$ has content $r^n$.

With this normalization it agrees with Lebesgue measure on $\mathbb{R}^n$ (classically, by the
isodiametric inequality); the case $n = 1$ is checked by the computation of the Riemannian volume
of the real line. -/
def normalizedHausdorffMeasure (n : ℕ) (X : Type*) [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] : Measure X :=
  (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / 2 ^ n) • μH[n]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- **Riemannian volume.** Let $E$ be a finite-dimensional real normed space, let $I$ be a model
with corners on $E$, and let $M$ be a $C^\infty$ manifold modeled on $I$, so that $M$ has dimension
$n = \dim_{\mathbb{R}} E$. Suppose that $M$ carries a $C^\infty$ Riemannian metric and an extended
metric equal to the Riemannian distance (the infimum of the lengths of $C^1$ paths), and is given
its Borel $\sigma$-algebra. The Riemannian volume of $M$ is the normalized $n$-dimensional
Hausdorff measure of $M$.

The manifold and Riemannian hypotheses are not used in the formula; they tie the dimension to the
model of $M$ and restrict the definition to the setting in which, classically, this measure is the
Riemannian volume, given in charts by the density $\sqrt{\det(g_{ij})}$ against Lebesgue measure. -/
@[nolint unusedArguments]
def riemannianVolume [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E H) (M : Type*)
    [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M] : Measure M :=
  normalizedHausdorffMeasure (finrank ℝ E) M

/-- **The Riemannian volume of the real line is Lebesgue measure.** The Riemannian volume of the
real line $\mathbb{R}$, with its standard Riemannian metric (the usual inner product on each tangent
space) and with its usual distance, which is the Riemannian distance, is Lebesgue measure.

This is a normalization check of the Riemannian volume in dimension one. -/
theorem riemannianVolume_real : riemannianVolume 𝓘(ℝ, ℝ) ℝ = volume := by
  have hball : volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ ℝ))) 1) = 2 := by
    rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by simp)]
    simp
  rw [riemannianVolume, normalizedHausdorffMeasure, hball, finrank_self, pow_one,
    ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top, one_smul, Nat.cast_one,
    hausdorffMeasure_real]

end Manifold
