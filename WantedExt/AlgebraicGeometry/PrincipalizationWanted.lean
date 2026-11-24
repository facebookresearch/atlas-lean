/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PrincipalizationModels

/-!
# Characteristic-zero principalization and log-resolution input

Principalization produces a smooth birational modification whose actual
inverse ideal is an effective Cartier divisor with strict normal crossings
reduced support. This is the geometric input for valuations of ideals,
multiplier ideals and log-singularity calculations. Those further
discrepancy and multiplier-ideal interfaces remain additional scope.

Reference: Bierstone–Milman, *Canonical desingularization in characteristic
zero*, Inventiones Mathematicae 128 (1997), 207–302.
Theorem 1.10 is the principalization statement.
https://arxiv.org/abs/alg-geom/9508005
Covered source: AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b,
`ResolutionOfSurfaces/QuadraticTransformations/PointBlowupPrincipalization.lean`
and `ResolutionOfSurfaces/EmbeddedResolution/CartierAfterPointBlowups.lean`.
Their dimension-two results and generic SNC criteria are not new requests.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PrincipalizationWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PrincipalizationModels

universe u

def_wanted principalization (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [Smooth X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (I : X.left.IdealSheafData) (nonzero : I ≠ ⊥) : Principalization X I

end WantedExt.AlgebraicGeometry.PrincipalizationWanted
