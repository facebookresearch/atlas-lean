/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Gromov's inequality for Hermitian holomorphic line bundles

A common finite cover by complex coordinate charts presents the bundles in local holomorphic
frames. Nonvanishing transition functions with the cocycle condition glue the local complex
lines. Positive weights give the norms of the local frames, and metric compatibility glues
them to smooth Hermitian metrics. The tensor powers use products of the corresponding
transition powers and frame norm powers. Values of local functions off their chart domains
(or overlaps) are irrelevant.

The volume measure has smooth positive Lebesgue densities in these same charts. This is the
measure of a smooth positive volume form for the canonical complex orientation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff Manifold

namespace MetaMathlibExt
namespace Gromov

variable {n k l : ℕ} {M : Type*} [TopologicalSpace M]

-- Coordinate charts in the complex-analytic maximal atlas, small enough for the local frames.
structure ChartCover (n k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Fin n → ℂ) M] where
  chart : Fin k → OpenPartialHomeomorph M (Fin n → ℂ)
  compatible : ∀ i, chart i ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) ω M
  covers : ∀ x : M, ∃ i, x ∈ (chart i).source

variable [ChartedSpace (Fin n → ℂ) M]

-- Restrict on both sides of the coordinate pushforward: no chart is assumed globally injective.
structure PositiveVolume [MeasurableSpace M] (U : ChartCover n k M) where
  measure : Measure M
  density : Fin k → (Fin n → ℂ) → ℝ
  smooth : ∀ i, ContDiffOn ℝ ∞ (density i) (U.chart i).target
  positive : ∀ i z, z ∈ (U.chart i).target → 0 < density i z
  map_restrict : ∀ i, (measure.restrict (U.chart i).source).map (U.chart i) =
    (volume.withDensity fun z ↦ ENNReal.ofReal (density i z)).restrict (U.chart i).target

-- `transition a i j` takes the fiber coordinate in frame `i` to the one in frame `j`.
structure HermitianLines (U : ChartCover n k M) (l : ℕ) where
  transition : Fin l → Fin k → Fin k → M → ℂ
  transition_analytic : ∀ a i j,
    AnalyticOnNhd ℂ (fun z ↦ transition a i j ((U.chart i).symm z))
      {z ∈ (U.chart i).target | (U.chart i).symm z ∈ (U.chart j).source}
  transition_ne_zero : ∀ a i j x,
    x ∈ (U.chart i).source → x ∈ (U.chart j).source → transition a i j x ≠ 0
  cocycle : ∀ a i j h x,
    x ∈ (U.chart i).source → x ∈ (U.chart j).source → x ∈ (U.chart h).source →
    transition a j h x * transition a i j x = transition a i h x
  weight : Fin l → Fin k → M → ℝ
  weight_smooth : ∀ a i,
    ContDiffOn ℝ ∞ (fun z ↦ weight a i ((U.chart i).symm z)) (U.chart i).target
  weight_pos : ∀ a i x, x ∈ (U.chart i).source → 0 < weight a i x
  metric_compatible : ∀ a i j x,
    x ∈ (U.chart i).source → x ∈ (U.chart j).source →
    ‖transition a i j x‖ * weight a j x = weight a i x

variable {U : ChartCover n k M} {H : HermitianLines U l} {m : Fin l → ℕ}

-- Global holomorphic sections are exactly the compatible tuples in the local tensor frames.
structure Section (H : HermitianLines U l) (m : Fin l → ℕ) where
  coord : Fin k → M → ℂ
  analytic : ∀ i,
    AnalyticOnNhd ℂ (fun z ↦ coord i ((U.chart i).symm z)) (U.chart i).target
  compatible : ∀ i j x, x ∈ (U.chart i).source → x ∈ (U.chart j).source →
    coord j x = (∏ a, H.transition a i j x ^ m a) * coord i x

-- Compatibility of the metrics and coordinates makes the result independent of the chart.
def Section.pointwiseNorm (s : Section H m) (x : M) : ℝ :=
  let i := (U.covers x).choose
  ‖s.coord i x‖ * ∏ a, H.weight a i x ^ m a

end Gromov

/-- **Gromov's inequality.** On a nonempty compact complex manifold of dimension `n` with
smooth positive volume form and a finite family of smooth Hermitian holomorphic line bundles,
there is a constant `C > 0` depending only on these data. For every real `p > 0`, nonnegative
multidegree `m`, and global holomorphic section `s` of the corresponding tensor product of
powers, its pointwise tensor-metric norm to the power `p` is bounded everywhere by
`C * (⌈p⌉)^(2n) * (1 + ∑ m)^(2n)` times the integral of that same power of the norm.

Source: A. Moriwaki, *Continuity of volumes on arithmetic varieties*, J. Algebraic Geom. 18 (2009),
407–457, [arXiv:math/0612269v2](https://arxiv.org/abs/math/0612269v2), Corollary 1.1.2, p. 8. -/
theorem_wanted gromov_sup_pow_le_integral {n k l : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (Fin n → ℂ) M] [IsManifold 𝓘(ℂ, Fin n → ℂ) ω M]
    [MeasurableSpace M] [BorelSpace M] (U : Gromov.ChartCover n k M)
    (Ω : Gromov.PositiveVolume U) (H : Gromov.HermitianLines U l) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℝ), 0 < p → ∀ (m : Fin l → ℕ) (s : Gromov.Section H m) (x : M),
      Real.rpow (s.pointwiseNorm x) p ≤
        C * (⌈p⌉ : ℝ) ^ (2 * n) * (1 + ∑ a, (m a : ℝ)) ^ (2 * n) *
          ∫ y, Real.rpow (s.pointwiseNorm y) p ∂Ω.measure

end MetaMathlibExt
