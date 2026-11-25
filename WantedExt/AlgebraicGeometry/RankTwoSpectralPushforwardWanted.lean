/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoSpectralPushforward

/-!
# The integral rank-one spectral pushforward theorem

Only integrality is required of the spectral fibre. The domain includes
coherent torsion-free rank-one sheaves on singular curves, with the
ordinary degree needed for literal finite pushforward. The constructed
functor uses actual tautological multiplication and the native adjunction
mate; its equivalence is an independent proof request.
Source: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2, Theorem 1.3.4.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RankTwoSpectralPushforwardWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoHitchinModels
open RankTwoSpectralFamilies RankTwoSpectralPushforward

def_wanted nativeIntegralSpectralPushforward (C : ComplexScheme) [CurveSource C]
    (B : BaseChanges C) (M : ModuliModel C B) (S : SectionBases C) (H : HitchinModel C B M S)
    (F : SpectralFamily C S) (Ω : Type) [Field Ω] [Algebra ℂ Ω] [IsAlgClosed Ω]
    (s : complexField Ω ⟶ base C) [IsIntegral (baseChangedSpectral F s).left] :
    PushforwardProofs C B M S H F Ω s

theorem_wanted nativeIntegralSpectralEquivalence (C : ComplexScheme) [CurveSource C]
    (B : BaseChanges C) (M : ModuliModel C B) (S : SectionBases C) (H : HitchinModel C B M S)
    (F : SpectralFamily C S) (Ω : Type) [Field Ω] [Algebra ℂ Ω] [IsAlgClosed Ω]
    (s : complexField Ω ⟶ base C) [IsIntegral (baseChangedSpectral F s).left]
    (P : PushforwardProofs C B M S H F Ω s) :
    (pushforwardFunctor C B M S H F Ω s P).IsEquivalence

end WantedExt.AlgebraicGeometry.RankTwoSpectralPushforwardWanted
