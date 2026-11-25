/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PlurigenusFamilies
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Castelnuovo's surface rationality criterion

The irregularity and second plurigenus are dimensions of the actual
coherent cohomology groups. The canonical line is fixed by natural Serre
duality. Rationality is Mathlib's dense-open birational scheme relation.

Reference: Beauville, *Complex Algebraic Surfaces*,
"Castelnuovo's theorem and applications", pp. 55–67,
https://doi.org/10.1017/CBO9780511623936.007
Castelnuovo's criterion: q = P₂ = 0.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SurfaceRationalityWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurvePositivity

universe u

theorem_wanted castelnuovo (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 2 X.hom]
    (hX : MathlibExt.AlgebraicGeometry.ProjectiveSpace.IsProjective X)
    (K : X.left.Modules) (hK : SerreDualizingLine X.hom K 2)
    (hq : Module.finrank k (cohomology X.hom (structureModule X.left) 1) = 0)
    (hP2 : Module.finrank k (cohomology X.hom (power K 2) 0) = 0) :
    Scheme.IsRationalOver X.hom

end WantedExt.AlgebraicGeometry.SurfaceRationalityWanted
