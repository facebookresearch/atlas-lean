/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quasiconformal images of uncountably many lines without rectifiable curves (AimPL, Problem 5.3)

AimPL, Mapping theory in metric spaces, Problem 5.3 (H. Hakobyan, L. Kovalev, J. Tyson): is there a
quasiconformal map `f` of the plane and an uncountable set `E ⊆ ℝ` so that `f(E × ℝ)` contains no
rectifiable curves?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.EMetricSpace.BoundedVariation

@[expose] public section

namespace MathlibExt.Analysis.QuasiconformalUnrectifiableLinesAIMAnalysisProblem124Wanted

/-!
Source: AimPL: Mapping theory in metric spaces, Problem 5.3 (H. Hakobyan, L. Kovalev, J. Tyson),
http://aimpl.org/mappingmetric/5/. UnsolvedMath record UM-20000592 (`AIM-ANALYSIS-0124`), dataset
ulamai/UnsolvedMath v1.8.0.

Quasiconformal uses the metric definition: a homeomorphism of `ℂ` with `limsup_{r → 0} max_{|w - z|
= r} |f w - f z| / min_{|w - z| = r} |f w - f z|` bounded uniformly in `z`, written as an eventual
bound. A rectifiable curve is a nonconstant continuous `γ : [0, 1] → ℂ` of finite total variation.
As in AimPL, the whole union `f(E × ℝ)` contains no rectifiable curve. This is stronger than the
per-line property (each line image `f({x} × ℝ)`, `x ∈ E`, contains no rectifiable curve), since a
curve could meet several line images, but the two agree when `E` is totally disconnected: `f⁻¹` maps
a curve in `f(E × ℝ)` to a curve in `E × ℝ`, whose first coordinate ranges over a connected subset
of `E`, a single point, so the curve lies in one line image. Bishop, Hakobyan and Williams prove the
per-line property (they construct horizontal lines `ℝ × S`; the rotation `z ↦ i z` turns them into
vertical lines), and every `E` with that property is totally disconnected: a quasiconformal map is
absolutely continuous on almost every vertical line, so it maps segments of almost every vertical
line to rectifiable curves, and `E` is Lebesgue-null and contains no interval.
-/

open Metric

/-- A homeomorphism `f` of `ℂ` is quasiconformal (metric definition): there is `H` such that at
every `z`, for all small `r > 0`,
`max_{|w - z| = r} |f w - f z| ≤ H · min_{|w - z| = r} |f w - f z|`
(equivalently `limsup_{r → 0} max / min` is bounded uniformly in `z`). -/
def IsQuasiconformal (f : ℂ ≃ₜ ℂ) : Prop :=
  ∃ H : ℝ, ∀ z : ℂ, ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    sSup ((fun w => ‖f w - f z‖) '' sphere z r) ≤
      H * sInf ((fun w => ‖f w - f z‖) '' sphere z r)

/-- `S ⊆ ℂ` contains a nonconstant rectifiable curve: a continuous `γ : [0, 1] → S` of finite
length (bounded total variation, `BoundedVariationOn`) that is not constant. -/
def ContainsRectifiableCurve (S : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧ BoundedVariationOn γ (Set.Icc 0 1) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ S) ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ γ 0

/-- The question of Hakobyan, Kovalev and Tyson (AimPL, Mapping theory in metric spaces, Problem
5.3): some quasiconformal map `f` of the plane and some uncountable `E ⊆ ℝ` are such that the image
`f(E × ℝ)` of the union of the vertical lines through the points of `E` contains no nonconstant
rectifiable curve. -/
def qcMapUnrectifiableImagesOfUncountablyManyLines : Prop :=
  ∃ f : ℂ ≃ₜ ℂ, IsQuasiconformal f ∧ ∃ E : Set ℝ, ¬ E.Countable ∧
    ¬ ContainsRectifiableCurve (f '' {z : ℂ | z.re ∈ E})

/--
Resolved true: Bishop, Hakobyan and Williams constructed a planar quasiconformal map and a set `S ⊆
ℝ` of Hausdorff dimension arbitrarily close to 1 (Corollary 1.8), or equal to 1 (Theorem 1.9), such
that the image of every line `ℝ × {y}`, `y ∈ S`, has no rectifiable subarc, and state that this
answers AimPL Problem 5.3; such an `S` is totally disconnected, so the image of the union of these
lines contains no rectifiable curve either (module documentation). Source: AimPL: Mapping theory in
metric spaces, Problem 5.3 (H. Hakobyan, L. Kovalev, J. Tyson), http://aimpl.org/mappingmetric/5/;
resolution: C. J. Bishop, H. Hakobyan and
M. Williams, Quasisymmetric dimension distortion of Ahlfors regular subsets of a metric space, Geom.
Funct. Anal. 26 (2016), 379-421, arXiv:1211.0233, Section 1.4: Problem 5.3 of [10] (AimPL mapping
theory list) asks for an uncountable family of lines whose quasiconformal images contain no
rectifiable subarcs, and Corollary 1.8 answers it 'with a resounding yes'; Theorem 1.9 even gives a
compact S ⊂ [0, 1] of Hausdorff dimension 1 and a quasiconformal f with no rectifiable subarc in
f([0, 1] × {y}) for every y ∈ S, https://doi.org/10.1007/s00039-016-0368-5.
-/
public theorem_wanted qcMapUnrectifiableImagesOfUncountablyManyLines_holds :
    qcMapUnrectifiableImagesOfUncountablyManyLines

end MathlibExt.Analysis.QuasiconformalUnrectifiableLinesAIMAnalysisProblem124Wanted
