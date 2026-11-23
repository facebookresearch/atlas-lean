/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Short paths from the origin inside a polynomial lemniscate (Erdős Problem 1215)

Erdős Problem 1215: is there `C` such that for every polynomial `P` with `P(0) = 1` and all roots on
the unit circle, some path in `{z : |P(z)| < 1}` connecting `0` to the unit circle has length at
most `C`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.EMetricSpace.BoundedVariation

@[expose] public section

namespace MathlibExt.Analysis.LemniscatePathLengthErdosProblem1215Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1215, https://www.erdosproblems.com/1215 (status
DISPROVED). UnsolvedMath record UM-30007256 (`EP-1215`), dataset ulamai/UnsolvedMath v1.8.0.

`P` is non-constant (for `P = 1` the set is empty and no path exists). Since `P(0) = 1`, the point
`0` lies on the boundary of `{z : |P(z)| < 1}`, not in it, so the path is a continuous map on `[0,
1]` from `0` to the unit circle lying in the open set at every interior time (requiring it at `t =
0` would make every instance fail and the refutation trivial). Its length is its total variation
`eVariationOn`. formal-conjectures has no statement.
-/

/-- Erdős Problem 1215: there is `C` such that for every non-constant complex polynomial `P` with
`P 0 = 1` and all roots on the unit circle, some continuous path `γ : [0, 1] → ℂ` from `0` to the
unit circle, inside `{z : |P z| < 1}` at every interior time (`|P 0| = 1`, so `0` is a boundary
point), has length (total variation) at most `C`. -/
def boundedLengthLemniscatePath : Prop :=
  ∃ C : ℝ, ∀ P : Polynomial ℂ, 0 < P.natDegree → P.eval 0 = 1 → (∀ z ∈ P.roots, ‖z‖ = 1) →
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = 0 ∧ ‖γ 1‖ = 1 ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖P.eval (γ t)‖ < 1) ∧
      eVariationOn γ (Set.Icc 0 1) ≤ ENNReal.ofReal C

/--
Resolved false: MacLane proved that for every simply connected compact `A ⊆ {|z| < 1}` with `0 ∉ A`
and all large `d` there is such a `P` of degree `d` with `|P| > 2` on `A`; taking for `A` a
labyrinth around which every path from `0` to the unit circle has length `> C` defeats every `C`
(such a path avoids `A`, where `|P| > 2`). erdosproblems.com/1215 lists the problem as disproved.
Source: T. F. Bloom, Erdős Problems, Problem #1215, https://www.erdosproblems.com/1215 (status
DISPROVED); resolution: G. R. MacLane, On a conjecture of Erdős, Herzog and Piranian, Michigan Math.
J. 2 (1953-54), 147-148, erdosproblems.com/1215: for every simply connected compact A ⊆ {|z| < 1}
with 0 ∉ A and all large d there is such a P of degree d with |P| > 2 on A; a labyrinth A forces
long paths.
-/
public theorem_wanted boundedLengthLemniscatePath_refuted : ¬ boundedLengthLemniscatePath

end MathlibExt.Analysis.LemniscatePathLengthErdosProblem1215Wanted
