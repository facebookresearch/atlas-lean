/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Disc discrepancy of infinite planar sets is unbounded (Erdős Problem 989)

Erdős Problem 989: if `A = {z_1, z_2, …} ⊂ ℝ²` is an infinite sequence then let `f(r) = max_C | |A ∩
C| - πr² |`, where the maximum is taken over all circles `C` of radius `r`. Is `f(r)` unbounded for
every `A`? How fast does `f(r)` grow?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.DiscDiscrepancyUnboundedErdosProblem989Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #989, https://www.erdosproblems.com/989 (status
SOLVED). UnsolvedMath record UM-30007112 (`EP-989`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is an infinite set of points of `EuclideanSpace ℝ (Fin 2)` with finitely many points in each
disc (otherwise `|A ∩ C|` is infinite for some disc and `f` is trivially unbounded). Circles of
radius `r` are closed discs, and `f` unbounded means that for every `M` some disc of some radius `r
> 0` has discrepancy greater than `M`. The second question (how fast `f` grows; Beck: `r^{1/2} ≪
f(r)`, and `f(r) ≪ (r log r)^{1/2}` for some `A`) is not formalized. formal-conjectures has no
statement of this problem.
-/

/-- Erdős Problem 989 (first question): for every infinite set `A` of points of the plane with
finitely many points in each disc, `f(r) = max_C | |A ∩ C| - π r² |` (over closed discs `C` of
radius `r`) is unbounded: for every `M` some disc `C` of some radius `r > 0` has
`| |A ∩ C| - π r² | > M`. -/
def discDiscrepancyUnbounded : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin 2)), A.Infinite →
    (∀ c r, (A ∩ Metric.closedBall c r).Finite) → ∀ M : ℝ, ∃ r : ℝ, 0 < r ∧
      ∃ c, M < |((A ∩ Metric.closedBall c r).ncard : ℝ) - Real.pi * r ^ 2|

/--
Resolved true: Beck proved `f(r) ≫ r^{1/2}` for every infinite `A`, so `f` is unbounded;
erdosproblems.com/989 records the problem as settled by Beck. Source: T. F. Bloom, Erdős Problems,
Problem #989, https://www.erdosproblems.com/989 (status SOLVED); resolution: J. Beck, Irregularities
of distribution. I, Acta Math. (1987), 1-49, erdosproblems.com/989: Beck proved f(r) ≫ r^{1/2} for
all A, and that some A has f(r) ≪ (r log r)^{1/2}, https://www.erdosproblems.com/989.
-/
public theorem_wanted discDiscrepancyUnbounded_holds : discDiscrepancyUnbounded

end MathlibExt.Geometry.DiscDiscrepancyUnboundedErdosProblem989Wanted
