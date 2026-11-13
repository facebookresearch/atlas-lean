/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Plane curves with infinitely many simultaneously PCF quadratic pairs (AimPL Conjecture 2.2)

AimPL, Postcritically finite maps in complex and arithmetic dynamics, Conjecture 2.2
(DeMarco-Ingram), item 1: does a curve `X ⊂ 𝔸²` contain infinitely many points `(c₁, c₂)` with
`z² + c₁` and `z² + c₂` both postcritically finite if and only if it is a vertical line, a
horizontal line or the diagonal? The 'only if' direction is the case `d = 2` of the theorem of
Ghioca, Krieger, Nguyen and Ye.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MathlibExt.Dynamics.SimultaneouslyPCFPlaneCurvesAIMDynamicalSystemsProblem79Wanted

/-!
Source: AimPL: Postcritically finite maps in complex and arithmetic dynamics, Section 2 (Moduli
problems), Conjecture 2.2 (L. DeMarco, P. Ingram), item 1, http://aimpl.org/finitedynamics/2/.
UnsolvedMath record UM-20001421 (`AIM-DYNAMICAL_SYSTEMS-0079`), dataset ulamai/UnsolvedMath v1.8.0.

A curve is an irreducible complex plane curve, given as the zero set of an irreducible
`F ∈ ℂ[x, y]`; it is the vertical line `{x = a}`, the horizontal line `{y = b}` or the diagonal
exactly when `F` is associated to `x - a`, `y - b` or `x - y`. `z² + c` is postcritically finite
when the forward orbit of its finite critical point `0` is finite. Only the 'only if' direction is
formalized: as printed, the 'if' direction fails for a line `{x = a}` with `z² + a` not
postcritically finite (Ghioca-Krieger-Nguyen-Ye add that the fixed coordinate must be a PCF
parameter).
-/

open MvPolynomial

/-- The quadratic polynomial `z ↦ z ^ 2 + c` is postcritically finite: the forward orbit of its
finite critical point `0` is a finite set. -/
def IsPCFQuadratic (c : ℂ) : Prop :=
  (Set.range fun k : ℕ => (fun z : ℂ => z ^ 2 + c)^[k] 0).Finite

/-- AimPL Postcritically finite maps, Conjecture 2.2, item 1, the "only if" direction (true by
Ghioca-Krieger-Nguyen-Ye): if the irreducible complex plane curve `X = {F = 0}` (`F ∈ ℂ[x, y]`
irreducible) contains infinitely many points `(c₁, c₂)` such that `z ^ 2 + c₁` and `z ^ 2 + c₂`
are both postcritically finite, then `X` is a vertical line `{x = a}`, a horizontal line
`{y = b}`, or the diagonal `{x = y}`, i.e. `F` is associated to `x - a`, `y - b` or `x - y`. -/
def simultaneouslyPCFCurveIsSpecial : Prop :=
  ∀ F : MvPolynomial (Fin 2) ℂ, Irreducible F →
    {p : ℂ × ℂ | eval ![p.1, p.2] F = 0 ∧ IsPCFQuadratic p.1 ∧ IsPCFQuadratic p.2}.Infinite →
      (∃ a : ℂ, Associated F (X 0 - C a)) ∨ (∃ b : ℂ, Associated F (X 1 - C b)) ∨
        Associated F (X 0 - X 1)

/--
Resolved true: an irreducible complex plane curve containing infinitely many points `(c₁, c₂)` with
`z² + c₁` and `z² + c₂` both postcritically finite is a vertical line, a horizontal line or the
diagonal. Ghioca-Krieger-Nguyen-Ye Theorem 1.1 (irreducible C ⊂ 𝔸² over ℂ, d ≥ 2): infinitely many
(a, b) ∈ C with z^d + a and z^d + b PCF iff C is {t₀} × 𝔸¹ or 𝔸¹ × {t₀} with z^d + t₀ PCF, or C = {y
= ζx} with ζ^(d-1) = 1; for d = 2 the last curve is the diagonal. The same statement for d = 2 is
Conjecture 1.4 of Ghioca-Krieger-Nguyen (IMRN 2016), a special case of the Baker-DeMarco conjecture.
Source: AimPL: Postcritically finite maps in complex and arithmetic dynamics, Section 2 (Moduli
problems), Conjecture 2.2 (L. DeMarco, P. Ingram), item 1, http://aimpl.org/finitedynamics/2/;
resolution: D. Ghioca, H. Krieger, K. Nguyen and H. Ye, The dynamical André-Oort conjecture:
unicritical polynomials, Duke Math. J. 166 (2017), no. 1, 1-25, arXiv:1505.01447, Theorem 1.1, the
'only if' direction, case d = 2, https://doi.org/10.1215/00127094-3673996.
-/
public theorem_wanted simultaneouslyPCFCurveIsSpecial_holds : simultaneouslyPCFCurveIsSpecial

end MathlibExt.Dynamics.SimultaneouslyPCFPlaneCurvesAIMDynamicalSystemsProblem79Wanted
