/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
public import Batteries.Util.ProofWanted

/-!
# Geometric normalization of boundary Frobenius trace

Generic finite duality and the actual O(D) constructor are completed
source/integration inputs. The requested comparison is normalized against
the genuine field Frobenius basis and canonical-form coefficient on every
actual local section, not against an arbitrary trace or test-ideal oracle.

References: Schwede arXiv0901.1154v4, Theorem 5.2;
Hacon--Xu arXiv1302.0298v2, §2.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry

def_wanted normalizedUntwistedIdentification
    {k : Type} [Field k] {n : ℕ} (P : LogPair k n) (p e : ℕ) [Fact p.Prime]
    (hp : IsInCharacteristic P.variety.X.left p) (he : 0 < e)
    [CharP (FunctionField P.variety) p]
    [∀ x : PrimePoint P.variety, IsDiscreteValuationRing (LocalRing P.variety x.val)]
    [IsFinite (iterated P.variety.X.left p hp e)]
    [HasDerivedPushforwards.{0}]
    [(derivedPushforward (iterated P.variety.X.left p hp e)).IsLeftAdjoint]
    (F : CanonicalTraceFrame P p e)
    (C : FiniteDualityEmbedding (iterated P.variety.X.left p hp e)) :
    {U : UntwistedIdentification P p e hp // U.frame = F ∧ U.embedding = C}

end MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
