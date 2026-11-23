/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lp bounds for the determinantal trilinear form (AIM multilinear operators workshop, Question 6)

AIM workshop Carleson theorems and multilinear operators, Question 6 (B. Street): prove `|∫∫ f(x)
g(y) h(x + y) / det(x, y) dx dy| ≲ ‖f‖_p ‖g‖_q ‖h‖_r` on `ℝ² × ℝ²` for certain `p, q, r`. The list
adds: this question has a quite satisfactory answer, see Gressman et al.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

namespace MathlibExt.Analysis.DeterminantalTrilinearFormBoundAIMAnalysisProblem65Wanted

/-!
Source: AIM workshop Carleson theorems and multilinear operators (2015), open problems compiled by
S. Guo, https://aimath.org/pastworkshops/multilinopsproblems.pdf, Question 6 (B. Street).
UnsolvedMath record UM-20000533 (`AIM-ANALYSIS-0065`), dataset ulamai/UnsolvedMath v1.8.0.

The list answers the question by pointing to Gressman et al., so the statement is their Theorem 1
for their form (1.1), `Λ(f, g, h) = p.v. ∫ f(x) g(y) h(z) δ(x + y + z) / det[1 1 1; x y z] dx dy
dz`, on Schwartz functions `f, g, h : ℝ² → ℂ`, with the principal value of their Section 2.1: the
limit as `ε → 0⁺` of the integral over `|det[1 1 1; x y z]| > ε`. The delta function is integrated
out by `z = -x - y` (a constant normalization of the delta would only change `C`). On `x + y + z =
0` they note `det[1 1 1; x y z] = 3 det(x, y)` (Section 3.2), so the list's integral with `h` is `3
Λ(f, g, h(-·))`. The statement covers the full exponent range of Theorem 1, `2 < p, q, r < ∞` with
`1/p + 1/q + 1/r = 1`, while the question asks only for some exponents.
-/

open MeasureTheory

/-- The determinant `det[1 1 1; x y z]` of the `3 × 3` matrix whose first row is `(1, 1, 1)` and
whose columns below it are `x, y, z ∈ ℝ²` (the kernel of Gressman et al.). -/
noncomputable def det3 (x y z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Matrix.det !![1, 1, 1; x 0, y 0, z 0; x 1, y 1, z 1]

/-- The truncated form of Gressman et al. with `δ(x + y + z)` integrated out by `z = -x - y`:
`∫∫_{|det[1 1 1; x y z]| > ε} f(x) g(y) h(z) / det[1 1 1; x y z] dx dy`. -/
noncomputable def truncatedDeterminantalForm
    (f g h : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (ε : ℝ) : ℂ :=
  ∫ w : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
    Set.indicator {w | ε < |det3 w.1 w.2 (-(w.1 + w.2))|}
      (fun w => f w.1 * g w.2 * h (-(w.1 + w.2)) / (det3 w.1 w.2 (-(w.1 + w.2)) : ℂ)) w

/-- The AIM question (Carleson theorems and multilinear operators, Question 6) in the form of its
answer by Gressman, He, Kovač, Street, Thiele and Yung: for `2 < p, q, r < ∞` with
`1/p + 1/q + 1/r = 1`, the principal value
`Λ(f, g, h) = p.v. ∫ f(x) g(y) h(z) δ(x + y + z) / det[1 1 1; x y z]` exists for Schwartz functions
on `ℝ²` and is bounded by `C ‖f‖_p ‖g‖_q ‖h‖_r`. -/
def determinantalTrilinearBound : Prop :=
  ∀ p q r : ℝ, 2 < p → 2 < q → 2 < r → 1 / p + 1 / q + 1 / r = 1 →
    ∃ C : ℝ, ∀ f g h : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ, ∃ L : ℂ,
      Filter.Tendsto (truncatedDeterminantalForm f g h) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
      ‖L‖ ≤ C * (eLpNorm f (ENNReal.ofReal p) volume).toReal *
        (eLpNorm g (ENNReal.ofReal q) volume).toReal * (eLpNorm h (ENNReal.ofReal r) volume).toReal

/--
Resolved true: Gressman, He, Kovač, Street, Thiele and Yung proved that the principal value of their
determinantal form exists for Schwartz functions (Section 2.1) and is bounded by `C ‖f‖_p ‖g‖_q
‖h‖_r` exactly in the range `2 < p, q, r < ∞`, `1/p + 1/q + 1/r = 1` (Theorem 1, which also shows
failure outside it); the AIM list cites their paper as the answer. Source: AIM workshop Carleson
theorems and multilinear operators (2015), open problems compiled by S. Guo,
https://aimath.org/pastworkshops/multilinopsproblems.pdf, Question 6 (B. Street); resolution: P.
Gressman, D. He, V. Kovač, B. Street, C. Thiele and P.-L. Yung, On a trilinear singular integral
form with determinantal kernel, Proc. Amer. Math. Soc. 144 (2016), 3465-3477, arXiv:1510.01069,
Theorem 1 for the form (1.1): |Λ(f, g, h)| ≲_{p,q,r} ‖f‖_p ‖g‖_q ‖h‖_r whenever 2 < p, q, r < ∞ and
1/p + 1/q + 1/r = 1, and the a priori estimate fails for every other 1 ≤ p, q, r ≤ ∞; Section 2.1:
the principal value (limit of the integrals over |det[1 1 1; x y z]| > ε) exists for Schwartz f, g,
h; Section 3.2: det[1 1 1; x y z] = 3 det(x y) when x + y + z = 0; the AIM list itself cites
Gressman et al. as the answer, https://doi.org/10.1090/proc/13007.
-/
public theorem_wanted determinantalTrilinearBound_holds : determinantalTrilinearBound

end MathlibExt.Analysis.DeterminantalTrilinearFormBoundAIMAnalysisProblem65Wanted
