/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CurvePositivity
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Curve semiampleness, torsion and asymptotic positivity

Semiampleness of a line bundle on a smooth proper integral curve means
positive degree or torsion. In particular, degree-zero nefness does not by
itself imply semiampleness. Bigness is identified with positive degree
using actual asymptotic global-section dimensions. Over an algebraically
closed field, a smooth curve is integral exactly when it is geometrically
irreducible.

Reference: Lazarsfeld, *Positivity in Algebraic Geometry I*, Chapter 1,
https://doi.org/10.1007/978-3-642-18808-4.

Covered ample-degree/curve Riemann–Roch inputs: AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/AmpleDegreeCriterion/ComponentPositivity.lean`
and `StacksFrontier/AlgebraicGeometry/Curves/LinearSeries.lean`.
Those proved inputs are not re-requested here.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CurvePositivityWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurvePositivity

universe u

/-- Let $k$ be an algebraically closed field, $C$ a smooth proper integral curve over $k$ and $L$ a
line bundle on $C$. Then some positive tensor power of $L$ is globally generated (semiampleness) if
and only if $\deg L > 0$ or some positive tensor power of $L$ is trivial. -/
theorem_wanted semiample_iff (k : Type u) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left]
    (L : C.left.Modules)
    (hL : IsLineBundle L) :
    IsSemiample L hL ↔ 0 < degree C.hom L hL ∨ IsTorsion L hL

/-- Let $k$ be an algebraically closed field, $C$ a smooth proper integral curve over $k$ and $L$ a
line bundle on $C$. Then there are $c > 0$ and $N$ with $\dim_k H^0(C, L^{\otimes n}) \ge c n$ for
all $n \ge N$ (`IsBigOnCurve`) if and only if $\deg L > 0$. -/
theorem_wanted big_iff (k : Type u) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left]
    (L : C.left.Modules)
    (hL : IsLineBundle L) :
    IsBigOnCurve C.hom L hL ↔ 0 < degree C.hom L hL

end WantedExt.AlgebraicGeometry.CurvePositivityWanted
