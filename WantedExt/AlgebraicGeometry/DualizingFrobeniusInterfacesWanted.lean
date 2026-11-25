/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
public import Batteries.Util.ProofWanted

/-!
# Divisorial identification of the actual Frobenius duality module

This is the exact source-to-native comparison, not a request for generic
finite duality or O(D). It uses an actual dualizing canonical-divisor
reference, permitting imperfect inseparable base fields. The comparison
is up to legitimate units, as in Schwede arXiv0901.1154v4, §3/Theorem 5.2.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
open MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces

def_wanted frobeniusDivisorialIdentification
    {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) (p e : ℕ) [Fact p.Prime]
    [CharP k p] (hp : IsInCharacteristic V.X.left p) (he : 0 < e)
    [∀ x : PrimePoint V, IsDiscreteValuationRing (LocalRing V x.val)]
    [HasDerivedPushforwards.{0}]
    (C : CanonicalWeilReference V) [IsFinite (iterated V.X.left p hp e)]
    [(derivedPushforward (iterated V.X.left p hp e)).IsLeftAdjoint]
    (E : FiniteDualityEmbedding (iterated V.X.left p hp e)) :
    {F : FrobeniusIdentification V C p e hp // F.embedding = E}

end MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
