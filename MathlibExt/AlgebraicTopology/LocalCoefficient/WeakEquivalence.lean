/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularStalkComparison
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularModuleBasis
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCertificates
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceChains
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Twisted chain invariance for the actual simplicial weak map

The native-cover pullback is weak by right properness. Its literal integer
chain map is quasi-isomorphic by the canonical ordinary weak-chain theorem,
and the original regular-cover chain square gives the regular comparison.
The focused regular/stalk detector then treats every original target local
system, including nonflat stalks. No homotopy-fiber criterion is imported.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace ActualOriginalMapCalibration

/-- The actual native-cover pullback of a weak map is weak, and its whole
original coefficient square derives the regular quasi-isomorphism. -/
private theorem originalRegularPullback_quasiIso_of_weak
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f)
    (y : Y _⦋0⦌) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f
      (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y))) := by
  let p := SSet.KanComplex.nativeCoverProjection Y y
  let A : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let L : SSet.LocalSystem ℤ Y :=
    CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)
  let m := SSet.localCoefficientPullbackChainMap f L
  let q := pullback.snd f p
  let c := SSet.chainComplexMap q A
  let : Fibration p := SSet.KanComplex.nativeCoverProjection_fibration Y y
  let : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  have hq : WeakEquivalence q :=
    IsRightProper.weakEquivalence_of_isPullback (IsPullback.of_hasPullback f p)
  have hc : QuasiIso c :=
    SSet.realizationWeakEquivalences.quasiIso_chainComplexMap
      (R := ℤ) ((weakEquivalence_iff q).mp hq) A
  let eS := SSet.KanComplex.regularLocalCoefficientPullbackCoverChainIso f y
  let eT := SSet.KanComplex.originalNativeRegularCoefficientCoverChainIso Y y
  have hs : m ≫ eT.hom = eS.hom ≫ c :=
    SSet.KanComplex.originalRegularPullbackChainMap_cover_square f y
  let e : Arrow.mk m ≅ Arrow.mk c := Arrow.isoMk eS eT hs.symm
  exact (quasiIso_iff_of_arrow_mk_iso m c e).mpr hc

/-- EVERY target system is transported along the SAME actual base map. The
native regular comparison, degree projectivity and additive stalk transport
are derived, not caller quasi-isomorphism or flatness witnesses. -/
public theorem _root_.SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f)
    (y : Y _⦋0⦌)
    (hconn : ∀ z : SSet.FundamentalGroupoid Y,
      Nonempty (SSet.FundamentalGroupoid.mk y ⟶ z))
    (L : SSet.LocalSystem ℤ Y) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f L) := by
  have hr := originalRegularPullback_quasiIso_of_weak f hf y
  exact originalAllCoefficientPullback_quasiIso_of_regular f y hconn hr L

end ActualOriginalMapCalibration

end
