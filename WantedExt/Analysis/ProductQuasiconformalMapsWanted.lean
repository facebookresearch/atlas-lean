/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `AIM-ANALYSIS-0126`
# Product quasiconformal mappings of the plane

AIM problem list "Mapping theory in metric spaces", Problem 5.5.

Let `f` be a quasiconformal map of the plane such that at almost every point the differential of `f`
either preserves both the `x`- and `y`-directions or switches them. Does this imply that `f` is a
product map? Quasiconformal maps are homeomorphisms of `ℝ²` with bounded metric dilatation
(`limsup_{r → 0} max_{|y-x|=r} |f(y)-f(x)| / min_{|y-x|=r} |f(y)-f(x)| ≤ K` everywhere, the metric
definition); they are differentiable almost everywhere, and the hypothesis is that at almost every
point the differential is diagonal or anti-diagonal. Product maps are `(x, y) ↦ (g(x), h(y))` or
`(x, y) ↦ (g(y), h(x))`. The affirmative answer is registered (an unrefereed 2026 preprint claims a
counterexample).
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Analysis.Normed.Group.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Analysis.ProductQuasiconformalMapsWanted

open MeasureTheory Filter Topology

/-- The metric dilatation of `f : ℝ² → ℝ²` at `x` (sup norm on `ℝ²` = `Fin 2 → ℝ`, which gives the
same quasiconformal class). -/
noncomputable def dilatation (f : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) : ENNReal :=
  limsup (fun r : ℝ => (⨆ y ∈ Metric.sphere x r, edist (f y) (f x)) /
    ⨅ y ∈ Metric.sphere x r, edist (f y) (f x)) (𝓝[>] 0)

/-- `f` is quasiconformal: a homeomorphism with uniformly bounded metric dilatation. -/
def IsQuasiconformal (f : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ)) : Prop :=
  ∃ K : ENNReal, K < ⊤ ∧ ∀ x, dilatation f x ≤ K

/-- The differential of `f` at `x` maps each coordinate direction to a multiple of a coordinate
direction, the same pattern for both (diagonal or anti-diagonal). -/
def HasDiagonalOrSwapDifferential (f : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) : Prop :=
  DifferentiableAt ℝ f x ∧
    ((fderiv ℝ f x (Pi.single 0 1) 1 = 0 ∧ fderiv ℝ f x (Pi.single 1 1) 0 = 0) ∨
      (fderiv ℝ f x (Pi.single 0 1) 0 = 0 ∧ fderiv ℝ f x (Pi.single 1 1) 1 = 0))

/-- Problem 5.5 (affirmative form). -/
def conjecture : Prop :=
  ∀ f : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ), IsQuasiconformal f →
    (∀ᵐ x, HasDiagonalOrSwapDifferential f x) →
      ∃ g h : ℝ → ℝ, (∀ x, f x = ![g (x 0), h (x 1)]) ∨ ∀ x, f x = ![g (x 1), h (x 0)]

-- Carried source audit `AIM-ANALYSIS-0126` (see the Moved/ record).

/--
Resolved false: Refuted. Kleiner, Müller, Székelyhidi and Xie (Sobolev mappings of Euclidean
space and product structure, arXiv:2603.05979, Theorem 1.3 and Corollary 1.4) construct a
non-split bi-Lipschitz, area-preserving homeomorphism of R x R whose differential is diagonal or
anti-diagonal and invertible almost everywhere (it takes only five values); a bi-Lipschitz map
has bounded metric dilatation, so this is a counterexample to the formal statement. Xie, who
posed the problem, is a coauthor. The source records a proof by Kovalev for small distortion;
for products of R^n with n >= 2 the same paper proves that W^{1,2} maps with split differential
are split. Source: Bruce Kleiner, Stefan Müller, László Székelyhidi and Xiangdong Xie, Sobolev
mappings of Euclidean space and product structure, arXiv:2603.05979 (2026),
https://arxiv.org/abs/2603.05979. Moved from
`OpenConjectures/Analysis/ProductQuasiconformalMaps`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.ProductQuasiconformalMapsWanted
