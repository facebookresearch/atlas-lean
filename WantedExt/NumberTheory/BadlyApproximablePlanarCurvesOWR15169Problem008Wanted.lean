/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Davenport's problem on badly approximable points on planar curves (Oberwolfach Report 48/2016)

H. Husakova, Davenport's problem: an overview, Arbeitsgemeinschaft: Diophantine Approximation,
Fractal Geometry and Dynamics, Oberwolfach Report 48/2016, pp. 2779-2780, Problem 1 (Davenport):
given a planar curve `C`, is the set `C ∩ Bad(i, j)` uncountable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import WantedExt.NumberTheory.NearIntegerDistancePointsShared

@[expose] public section

namespace MathlibExt.NumberTheory.BadlyApproximablePlanarCurvesOWR15169Problem008Wanted

/-!
Source: H. Husakova, Davenport's problem: an overview, in Arbeitsgemeinschaft: Diophantine
Approximation, Fractal Geometry and Dynamics, Oberwolfach Reports 13 (2016), no. 48, pp. 2779-2780,
Problem 1 and Definition 1, DOI 10.4171/OWR/2016/48. UnsolvedMath record UM-30003234
(`OWR-15169-008`), dataset ulamai/UnsolvedMath v1.8.0.

`Bad(i, j)` is defined in the same report (p. 2757, Definition 2) for weights `0 < i, j < 1`, `i + j
= 1`: `(x, y)` with `max(‖qx‖^{1/i}, ‖qy‖^{1/j}) > c q⁻¹` for all `q ∈ ℕ`, some `c > 0`, `‖·‖` the
distance to the nearest integer (WantedExt `NearIntegerDistancePointsShared.distToNearestInt`). The
report notes that the answer is negative for some lines and states the problem for `C^(2)`
non-degenerate curves `C_f = {(x, f(x)) : x ∈ I}` (Definition 1: `f` twice continuously
differentiable on the interval `I`, `f''(x₀) ≠ 0` at some `x₀ ∈ I`), as the record does; `I` is
taken open. The boundary weights `(1, 0)`, `(0, 1)`, allowed by the record but outside Definition 2,
are not covered.
-/

open MathlibExt.NumberTheory.NearIntegerDistancePointsShared

/-- The `(i, j)`-badly approximable points of the plane (Oberwolfach Report 48/2016, p. 2757,
Definition 2, for `0 < i, j < 1`, `i + j = 1`): the `(x, y)` for which some `c > 0` satisfies
`max (‖q x‖^{1/i}, ‖q y‖^{1/j}) > c / q` for every integer `q ≥ 1`, where `‖·‖` is the distance to
the nearest integer. -/
def badSet (i j : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 0 < q →
    c / q < max (distToNearestInt (q * p.1) ^ (1 / i)) (distToNearestInt (q * p.2) ^ (1 / j))}

/-- Davenport's problem for non-degenerate planar curves (Oberwolfach Report 48/2016,
pp. 2779-2780): for every `C^(2)` non-degenerate planar curve `C_f = {(x, f x) : x ∈ I}` (`f` twice
continuously differentiable on the interval `I`, with `f'' (x₀) ≠ 0` at some `x₀ ∈ I`) and all
weights `i, j > 0` with `i + j = 1`, the set `C_f ∩ Bad(i, j)` is uncountable. -/
def davenportProblemPlanarCurves : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContDiffOn ℝ 2 f (Set.Ioo a b) →
    (∃ x₀ ∈ Set.Ioo a b, iteratedDeriv 2 f x₀ ≠ 0) →
    ∀ i j : ℝ, 0 < i → 0 < j → i + j = 1 →
      ¬ Set.Countable {p ∈ badSet i j | ∃ x ∈ Set.Ioo a b, p = (x, f x)}

/--
Resolved true: for every `C^(2)` non-degenerate planar curve `C_f`, `dim (Bad(i, j) ∩ C_f) = 1`
(Badziahin and Velani; An, Beresnevich and Velani), and the report concludes "In particular, the
answer to the Davenport's question in this case is positive" (p. 2780). Source: H. Husakova,
Davenport's problem: an overview, in Arbeitsgemeinschaft: Diophantine Approximation, Fractal
Geometry and Dynamics, Oberwolfach Reports 13 (2016), no. 48, pp. 2779-2780, Problem 1 and
Definition 1, DOI 10.4171/OWR/2016/48; resolution: D. Badziahin and S. Velani, Badly approximable
points on planar curves and a problem of Davenport, Math. Ann. 359 (2014), 969-1023; J. An, V.
Beresnevich and S. Velani, Badly approximable points on planar curves and winning, Adv. Math. 324
(2018), arXiv:1409.0064, Oberwolfach Report 48/2016, p. 2780: for any C^(2) non-degenerate planar
curve C_f, dim(Bad(i,j) ∩ C_f) = 1 [4, 3], 'In particular, the answer to the Davenport's question in
this case is positive', https://doi.org/10.1007/s00208-014-1020-z.
-/
public theorem_wanted davenportProblemPlanarCurves_holds : davenportProblemPlanarCurves

end MathlibExt.NumberTheory.BadlyApproximablePlanarCurvesOWR15169Problem008Wanted
