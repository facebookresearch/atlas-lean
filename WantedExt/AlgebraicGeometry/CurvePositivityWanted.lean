/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CurvePositivity
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Curve semiampleness, torsion and asymptotic positivity

Semiampleness of a line bundle on a smooth proper curve means positive
degree or torsion. In particular, degree-zero nefness does not by itself
imply semiampleness. Bigness is identified with positive degree using
actual asymptotic global-section dimensions.

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

variable (k : Type u) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (L : C.left.Modules)

/-- The precise degree-zero torsion exception in semiampleness. -/
theorem_wanted semiample_iff (hL : IsLineBundle L) :
    IsSemiample L ↔ 0 < degree C.hom L ∨ IsTorsion L

/-- Positive asymptotic section growth agrees with numerical positive degree. -/
theorem_wanted big_iff (hL : IsLineBundle L) :
    IsBigOnCurve C.hom L ↔ 0 < degree C.hom L

end WantedExt.AlgebraicGeometry.CurvePositivityWanted
