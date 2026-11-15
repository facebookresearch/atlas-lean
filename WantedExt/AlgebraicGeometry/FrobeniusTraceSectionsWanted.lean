/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FrobeniusTraceSections
public import Batteries.Util.ProofWanted

/-!
# Sheaf comparison for the actual indexed big-test ideal

Schwede arXiv0901.1154v4, Definition 2.12 and its localization theorem.
The input trace system is the fixed boundary Frobenius counit, indexed by
every actual admissible positive exponent. Local maps are computed from
genuine Cartier generators. The target ideal is pinned on every such
affine frame to the actual compatible-ideal infimum.

Generic compatible quotients/splittings and ordinary tensor/projection
formula are completed source integration inputs, not requested again.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FrobeniusTraceSections

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
open MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

def_wanted bigTestIdealSheafComparison
    {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) (p : ℕ) [Fact p.Prime]
    [CharP k p]
    [∀ q : PrimePoint V, IsDiscreteValuationRing (LocalRing V q.val)]
    [HasDerivedPushforwards.{0}]
    (C : CanonicalWeilReference V) (D : RealWeil V)
    (hp : IsInCharacteristic V.X.left p)
    (S : TraceSystem V C D p hp (structureModule V.X.left))
    [∀ a : AdmissibleExponent V C D p, IsFinite (iterated V.X.left p hp a.val)]
    (A : TraceTrivializingCover V C D p hp S) :
    TestIdealComparison V C D p hp S A

end MathlibExt.AlgebraicGeometry.FrobeniusTraceSections

