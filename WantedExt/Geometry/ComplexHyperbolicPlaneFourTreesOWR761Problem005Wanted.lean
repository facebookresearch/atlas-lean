/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The complex hyperbolic plane in a product of four trees (Oberwolfach Reports 47/2004)

Oberwolfach workshop Geometrie (2004), S. V. Buyalo (joint with V. Schroeder): it is open whether
the complex hyperbolic plane admits a quasi-isometric embedding into the 4-fold product of metric
trees.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section

namespace MathlibExt.Geometry.ComplexHyperbolicPlaneFourTreesOWR761Problem005Wanted

/-!
Source: S. V. Buyalo (joint work with V. Schroeder), Embedding and nonembedding results in
asymptotic geometry, in Geometrie, Oberwolfach Reports 1 (2004), no. 47, p. 2504, DOI
10.4171/OWR/2004/47. UnsolvedMath record UM-30000138 (`OWR-761-005`), dataset ulamai/UnsolvedMath
v1.8.0.

`H²_ℂ` is the unit ball of `ℂ²` with the distance `cosh d(z, w) = |1 - ⟨z, w⟩| / √((1 - |z|²)(1 -
|w|²))` (W. Goldman, Complex hyperbolic geometry, 1999, §3.1; the metric of curvature between `-4`
and `-1`, isometric to the source's `dt² + e^{2t}(dx² + dy²) + e^{4t}(dz - x dy)²`); a different
normalization rescales `d` and does not change quasi-isometric embeddability. A metric tree is an
`ℝ`-tree: a geodesic `0`-hyperbolic metric space. Buyalo-Lebedeva's simplicial metric trees are
metric trees in this sense. The product carries the max metric (any product norm gives the same
notion).
-/

/-- The complex hyperbolic plane `H²_ℂ` in the ball model: the open unit ball of `ℂ²`. -/
abbrev ComplexHyperbolicPlane := {z : EuclideanSpace ℂ (Fin 2) // ‖z‖ < 1}

/-- The distance of `H²_ℂ` in the ball model:
`cosh d(z, w) = |1 - ⟪z, w⟫| / √((1 - ‖z‖²)(1 - ‖w‖²))`. This is half the Bergman distance of
holomorphic sectional curvature `-1`, i.e. the Riemannian distance of the normalization with
sectional curvature between `-4` and `-1` (the metric `dt² + e^{2t}(dx² + dy²) + e^{4t}(dz - x dy)²`
of the source in horospherical coordinates); quasi-isometric embeddability does not depend on the
scale. -/
noncomputable def chDist (z w : ComplexHyperbolicPlane) : ℝ :=
  Real.arcosh (‖1 - inner ℂ (z : EuclideanSpace ℂ (Fin 2)) (w : EuclideanSpace ℂ (Fin 2))‖ /
    Real.sqrt ((1 - ‖(z : EuclideanSpace ℂ (Fin 2))‖ ^ 2) *
      (1 - ‖(w : EuclideanSpace ℂ (Fin 2))‖ ^ 2)))

/-- The Gromov product `(x | y)_w = (d(x, w) + d(y, w) - d(x, y)) / 2`. -/
noncomputable def gromovProduct {X : Type*} [MetricSpace X] (w x y : X) : ℝ :=
  (dist x w + dist y w - dist x y) / 2

/-- `X` is a metric tree (an `ℝ`-tree): any two points are joined by a geodesic segment, and `X` is
`0`-hyperbolic, `min ((x | y)_w, (y | z)_w) ≤ (x | z)_w` for all `x, y, z, w`. -/
def IsMetricTree (X : Type*) [MetricSpace X] : Prop :=
  (∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ (dist x y) = y ∧
      ∀ s ∈ Set.Icc 0 (dist x y), ∀ t ∈ Set.Icc 0 (dist x y), dist (γ s) (γ t) = |s - t|) ∧
    ∀ x y z w : X, min (gromovProduct w x y) (gromovProduct w y z) ≤ gromovProduct w x z

/-- Buyalo's question (Oberwolfach Report 47/2004, p. 2504): the complex hyperbolic plane admits a
quasi-isometric embedding into a product `T₁ × T₂ × T₃ × T₄` of four metric trees (product with the
max metric; any product norm gives the same notion): some `f` and `a ≥ 1`, `b ≥ 0` satisfy
`d(z, w) / a - b ≤ d(f z, f w) ≤ a d(z, w) + b` for all `z, w`. -/
def complexHyperbolicPlaneEmbedsInFourTrees : Prop :=
  ∃ (T : Fin 4 → Type) (_ : ∀ i, MetricSpace (T i)), (∀ i, IsMetricTree (T i)) ∧
    ∃ (f : ComplexHyperbolicPlane → ∀ i, T i) (a b : ℝ), 1 ≤ a ∧ 0 ≤ b ∧
      ∀ z w, chDist z w / a - b ≤ dist (f z) (f w) ∧ dist (f z) (f w) ≤ a * chDist z w + b

/--
Resolved true: Buyalo and Lebedeva (Theorem 6.6 and the example after it) show that the complex
hyperbolic plane admits a quasi-isometric embedding into the product of four simplicial metric
trees. Source: S. V. Buyalo (joint work with V. Schroeder), Embedding and nonembedding results in
asymptotic geometry, in Geometrie, Oberwolfach Reports 1 (2004), no. 47, p. 2504, DOI
10.4171/OWR/2004/47; resolution: S. Buyalo and N. Lebedeva, Dimensions of locally and asymptotically
self-similar spaces, Algebra i Analiz 19 (2007), no. 1; St. Petersburg Math. J. 19 (2008), 45-66,
DOI 10.1090/S1061-0022-07-00985-5, arXiv:math/0509433, Theorem 6.6: every cobounded, hyperbolic,
proper, geodesic space X admits a quasi-isometric embedding X → T_1 × ... × T_n into the n-fold
product of simplicial metric trees with n = dim ∂∞X + 1; 'For example, the complex hyperbolic plane
CH² admits a quasi-isometric embedding into the 4-fold product of simplicial metric trees',
https://arxiv.org/abs/math/0509433.
-/
public theorem_wanted complexHyperbolicPlaneEmbedsInFourTrees_holds :
    complexHyperbolicPlaneEmbedsInFourTrees

end MathlibExt.Geometry.ComplexHyperbolicPlaneFourTreesOWR761Problem005Wanted
