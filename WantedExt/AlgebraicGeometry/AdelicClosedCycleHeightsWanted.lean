/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AdelicClosedCycleHeights

/-!
# Canonical closed-point norm requests

All outputs retain actual closed scheme points and their canonical residue
fields/maps. No residue-field presentation is a new cycle generator.
Source: Yuan--Zhang, arXiv:2105.13587v9, Section 5.3.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AdelicClosedCycleHeights

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.AdelicSemipositiveClosures
open MathlibExt.AlgebraicGeometry.AdelicPicardVectors
open MathlibExt.AlgebraicGeometry.AdelicClosedCycleHeights

public def_wanted closedPointSources (K : Type) [Field K] (X : Over (Spec (.of K)))
    [LocallyOfFiniteType X.hom] : ClosedPointSources X

public def_wanted normSources (K : Type) [Field K] (A : AdelicField K)
    (X : Over (Spec (.of K))) (S : ClosedPointSources X) (G : GroundBase (K := K))
    (M : LineObject (A := A) (X := X) G) : ClosedPointNormSources S G M

public theorem_wanted independentNormSources (K : Type) [Field K] (A : AdelicField K)
    (X : Over (Spec (.of K))) (S : ClosedPointSources X) (G : GroundBase (K := K))
    (M : LineObject (A := A) (X := X) G) (N P : ClosedPointNormSources S G M)
    (z : ZeroCycle X) : cycleNormClass S N z = cycleNormClass S P z

end WantedExt.AlgebraicGeometry.AdelicClosedCycleHeights
