/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FrobeniusCenterDifferent
public import Batteries.Util.ProofWanted

/-!
# Recovering the actual F-different from the descended normalized trace

A normalization step toward Schwede arXiv0901.1154v4, Theorem 5.2 and Corollary 6.9:
the request asks for the multiplier of the given nonzero descended map; the
independence of the resulting divisor and the restriction of test ideals are those
results' further conclusions, not requested here.

The compatible-center quotient trace is fixed by the actual epimorphic
base-change mate. The adjoint element is computed, and the target
multiplier is fixed on every local Cartier section. Canonical references
are actual dualizing modules; no boundary/different function is assumed.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FrobeniusCenterDifferent

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
open MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace

def_wanted normalizedFdifferentMultiplier
    {k : Type} [Field k] {n d : ℕ} (V : NormalVariety k n) (W : NormalVariety k d)
    (p e : ℕ) [Fact p.Prime] [CharP k p] (he : 0 < e)
    [∀ q : PrimePoint V, IsDiscreteValuationRing (LocalRing V q.val)]
    [∀ q : PrimePoint W, IsDiscreteValuationRing (LocalRing W q.val)]
    [HasDerivedPushforwards.{0}]
    (C : CanonicalWeilReference V) (CW : CanonicalWeilReference W) (D : RealWeil V)
    (hV : IsInCharacteristic V.X.left p) (hW : IsInCharacteristic W.X.left p)
    [IsFinite (iterated V.X.left p hV e)] [IsFinite (iterated W.X.left p hW e)]
    [(derivedPushforward (iterated V.X.left p hV e)).IsLeftAdjoint]
    [(derivedPushforward (iterated W.X.left p hW e)).IsLeftAdjoint]
    (F : FrobeniusIdentification V C p e hV) (FW : FrobeniusIdentification W CW p e hW)
    (I : BoundaryIndex V C p e D) (i : W.X ⟶ V.X) [IsClosedImmersion i.left]
    (comm : i.left ≫ iterated V.X.left p hV e = iterated W.X.left p hW e ≫ i.left)
    (Q : CenterDescent C D p e hV hW F I i comm) (N : CenterLine C D p e i)
    (h : CategoryTheory.IsIso
      (sheafPushforwardUnit (iterated W.X.left p hW e) N.cartier.line.val))
    (hgeneric : centerTrace C D p e hV hW F I i comm Q N ≠ 0) :
    TraceMultiplier C D p e hV hW F I i comm Q N CW FW h

end MathlibExt.AlgebraicGeometry.FrobeniusCenterDifferent
