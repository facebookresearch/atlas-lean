/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetWeakComponentCoefficients
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomology
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence

/-!
# The original weak topological map with every target integer system

The actual singular map is weak. Its component coefficient maps and literal
integer-module coproduct derive the original simplicial coefficient map.
The existing singular-pullback Iso then gives the actual topological map.
No connectedness, flatness, selected component, or coefficient-QI input is
required of either endpoint or its target local system.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial

universe u

namespace TopCat

/-- A weak map has the original coefficient-chain quasi-isomorphism for
every target integer local system on arbitrary ambient components. -/
public theorem weakHomotopyEquivalences.quasiIso_localCoefficientPullbackChainMap_allComponents
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f)
    (L : TopCat.LocalSystem ℤ Y) :
    QuasiIso (TopCat.localCoefficientPullbackChainMap f L) := by
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
  have hs : SSet.realizationWeakEquivalences (TopCat.toSSet.map f) :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence (TopCat.toSSet.map f)).mp
      ((TopCat.mem_weakHomotopyEquivalences_iff f).mp hf)
  let E := TopCat.LocalSystem.singularPullbackIso f L
  let e := (SSet.localCoefficientChainComplexFunctor
    (R := ℤ) (X := TopCat.toSSet.obj X)).mapIso E
  let : IsIso (SSet.localCoefficientChainMap E.inv) := by
    change IsIso e.inv
    infer_instance
  let : QuasiIso (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map f) L.toSingular) :=
    SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap_allComponents
      (TopCat.toSSet.map f) hs L.toSingular
  change QuasiIso (SSet.localCoefficientChainMap E.inv ≫
    SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map f) L.toSingular)
  infer_instance

/-- The original weak map induces every original integer-local-system
homology isomorphism; the quantifier includes nonflat systems. -/
public theorem weakHomotopyEquivalences.isLocalCoefficientHomologyEquivalence_allComponents
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) :
    TopCat.IsLocalCoefficientHomologyEquivalence f := by
  intro L n
  let : QuasiIso (TopCat.localCoefficientPullbackChainMap f L) :=
    weakHomotopyEquivalences.quasiIso_localCoefficientPullbackChainMap_allComponents f hf L
  change IsIso (HomologicalComplex.homologyMap (TopCat.localCoefficientPullbackChainMap f L) n)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

/-- The original all-topological-system property supplies EVERY system
on the actual singular groupoid, by the existing singular groupoid
equivalence. No inverse-system or flatness witness is a caller premise. -/
public theorem IsLocalCoefficientHomologyEquivalence.quasiIso_singularPullbackChainMap
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj Y)) :
    QuasiIso (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map f) L) := by
  let F := TopCat.singularFundamentalGroupoidFunctor Y
  let hFF := TopCat.singularFundamentalGroupoidFunctor_fullyFaithful Y
  let hES := TopCat.singularFundamentalGroupoidFunctor_essSurj Y
  let : F.IsEquivalence :=
    { faithful := hFF.faithful, full := hFF.full, essSurj := hES }
  let e := F.asEquivalence
  let M : TopCat.LocalSystem ℤ Y := e.inverse ⋙ L
  let E : M.toSingular ≅ L :=
    (Functor.associator F e.inverse L).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm L ≪≫ Functor.leftUnitor L
  have hTop : QuasiIso (TopCat.localCoefficientPullbackChainMap f M) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hf M n
  let ES := TopCat.LocalSystem.singularPullbackIso f M
  let c := SSet.localCoefficientChainMap ES.inv
  let ec := (SSet.localCoefficientChainComplexFunctor
    (R := ℤ) (X := TopCat.toSSet.obj X)).mapIso ES
  let : IsIso c := by
    change IsIso ec.inv
    infer_instance
  let b : SSet.localCoefficientChainComplex (M.toSingular.pullback (TopCat.toSSet.map f)) ⟶
      SSet.localCoefficientChainComplex M.toSingular :=
    SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map f) M.toSingular
  let : QuasiIso (c ≫ b) := hTop
  have hb : QuasiIso b := quasiIso_of_comp_left c b
  let EX := Functor.isoWhiskerLeft (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)) E
  let eX : SSet.localCoefficientChainComplex (M.toSingular.pullback (TopCat.toSSet.map f)) ≅
      SSet.localCoefficientChainComplex (L.pullback (TopCat.toSSet.map f)) :=
    (SSet.localCoefficientChainComplexFunctor
      (R := ℤ) (X := TopCat.toSSet.obj X)).mapIso EX
  let eY : SSet.localCoefficientChainComplex M.toSingular ≅ SSet.localCoefficientChainComplex L :=
    (SSet.localCoefficientChainComplexFunctor
      (R := ℤ) (X := TopCat.toSSet.obj Y)).mapIso E
  let bL : SSet.localCoefficientChainComplex (L.pullback (TopCat.toSSet.map f)) ⟶
      SSet.localCoefficientChainComplex L :=
    SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map f) L
  let : QuasiIso b := hb
  let : IsIso eX.hom := eX.isIso_hom
  let : IsIso eY.hom := eY.isIso_hom
  let : QuasiIso eY.hom := _root_.quasiIso_of_isIso eY.hom
  have hs : eX.hom ≫ bL = b ≫ eY.hom :=
    SSet.localCoefficientPullbackChainMap_naturality (TopCat.toSSet.map f) E.hom
  have hAfter : QuasiIso (b ≫ eY.hom) := _root_.quasiIso_comp b eY.hom
  have hComp : QuasiIso (eX.hom ≫ bL) := hs.symm ▸ hAfter
  let : QuasiIso (eX.hom ≫ bL) := hComp
  exact quasiIso_of_comp_left eX.hom bL

end TopCat

end
