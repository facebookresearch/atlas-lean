/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes
public import Batteries.Util.ProofWanted

/-!
# Fixed-source Hom-chart tangent comparison

The chart is an actual étale atlas of a model equivalent on every scheme
to the fixed-source mapping functor. Its comparison map is computed
from the universal map's normalized relative differential, rather than
supplied as a tangent isomorphism. Generic Hom representability and
cotangent functoriality are source-covered; their exact normalized
native tangent comparison is the remaining request.
Reference: Graber--Harris--Starr, arXiv math/0109220v1, §2.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.MapModuliCharts
attribute [local instance] HasDerivedCategory.standard

theorem_wanted fixedHomTangentComparison
    {k : Type} [Field k] [IsAlgClosed k]
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    (C V : Over (Spec (.of k))) [IsProper C.hom] [Smooth C.hom] [Smooth V.hom]
    (M : FixedModel C.hom V.hom) (a : M.stack.EtaleAtlas) [IsNoetherian a.U.left]
    (B : FixedHomDifferentialData C V M a) :
    IsIso ((DerivedCategory.homologyFunctor a.U.left.Modules 0).map B.kodairaSpencer)

end MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes
