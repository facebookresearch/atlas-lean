/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Points of height at most d on curves of degree d (AIM rational points, Problem 27)

AIM workshop Rational and integral points on higher dimensional varieties, Problem 27 (Heath-Brown):
on a plane curve of degree `d` the number of points of height at most `d` is `≪ d³`, and some curves
have `≫ d²`. Can you do better than `≪ d³`? (Remark: `d^{5/2}` is easy.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.CurvePointsHeightDegreeAIMAlgebraicNumberTheoryProblem112Wanted

/-!
Source: AIM workshop Rational and integral points on higher dimensional varieties (2002), problem
list, https://aimath.org/WWN/qptsurface2/qptsurface2.pdf, Problem 27 (D. R. Heath-Brown).
UnsolvedMath record UM-20000460 (`AIM-ALGEBRAIC_NUMBER_THEORY-0112`), dataset ulamai/UnsolvedMath
v1.8.0.

Curves are affine plane curves `P(x, y) = 0` with `P ∈ ℚ[x, y]` irreducible of total degree `d` (an
integral curve of degree `d`), the setting of Binyamini, Cluckers and Novikov, Theorem 2.
Irreducibility is needed: a union of `d` lines carries about `d³` points of height at most `d`. A
rational number has height at most `H` when it is `a / b` with `|a|, |b| ≤ H`. The answer is stated
in the paper's quantitative form at `H = d` (`d ≥ 3`, since the theorem needs `H > 2`): at most `c
d² d^{2/d} (log d)^κ` points, which beats both `d³` and Heath-Brown's `d^{5/2}`.
-/

/-- A rational number has height at most `H` if in lowest terms `a / b` both `|a| ≤ H` and
`b ≤ H`. -/
def RatHeightLE (q : ℚ) (H : ℕ) : Prop :=
  q.num.natAbs ≤ H ∧ q.den ≤ H

/-- The number of rational points `(x, y)` of the plane curve `P = 0` whose coordinates have
height at most `H`. -/
noncomputable def curvePointCount (P : MvPolynomial (Fin 2) ℚ) (H : ℕ) : ℕ :=
  Set.ncard {x : Fin 2 → ℚ | MvPolynomial.eval x P = 0 ∧ ∀ i, RatHeightLE (x i) H}

/-- Heath-Brown's question (AIM workshop Rational and integral points on higher dimensional
varieties, Problem 27), in the quantitative form of its answer: there are absolute constants `c`
and `κ` such that every irreducible plane curve `P = 0` over `ℚ` of degree `d ≥ 3` has at most
`c d² d^{2/d} (log d)^κ` rational points whose coordinates have height at most `d`. -/
def planeCurvePointsAtHeightDegree : Prop :=
  ∃ c κ : ℝ, ∀ d : ℕ, 3 ≤ d → ∀ P : MvPolynomial (Fin 2) ℚ, Irreducible P →
    P.totalDegree = d →
      (curvePointCount P d : ℝ) ≤ c * (d : ℝ) ^ 2 * (d : ℝ) ^ ((2 : ℝ) / d) * Real.log d ^ κ

/--
Resolved true: Binyamini, Cluckers and Novikov proved that an integral affine curve of degree `d`
has at most `c d² H^{2/d} (log H)^κ` rational points with coordinates of height at most `H > 2`; at
`H = d` this is `O(d² (log d)^κ)`, better than `d³` and than Heath-Brown's easy `d^{5/2}`. Source:
AIM workshop Rational and integral points on higher dimensional varieties (2002), problem list,
https://aimath.org/WWN/qptsurface2/qptsurface2.pdf, Problem 27 (D. R. Heath-Brown); resolution: G.
Binyamini, R. Cluckers and D. Novikov, Bounds for rational points on algebraic curves, optimal in
the degree, and dimension growth, Int. Math. Res. Not. IMRN 2024 (2024), no. 11, 9256-9265,
arXiv:2302.04209, Theorem 2: for an integral algebraic curve C in A^n_K of degree d > 0 (K a
subfield of C) there are c = c(n) and an absolute κ with #C(Q, H) ≤ c d^2 H^{2/d} (log H)^κ for
every H > 2; here n = 2, K = Q, H = d, https://doi.org/10.1093/imrn/rnae034.
-/
public theorem_wanted planeCurvePointsAtHeightDegree_holds : planeCurvePointsAtHeightDegree

end MathlibExt.NumberTheory.CurvePointsHeightDegreeAIMAlgebraicNumberTheoryProblem112Wanted
