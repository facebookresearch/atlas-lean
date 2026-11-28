/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomCochainComplexQuasiIso
public import MathlibExt.Algebra.Homology.HomCochainComplexShortExact
public import MathlibExt.Algebra.Homology.HomCochainComplexSingle
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public meta import Mathlib.Tactic.NormNum

/-!
# Hom cochain coordinates, exactness and single support

An integer complex with differential multiplication by two gives a nonzero Hom differential.
Precomposition with multiplication by three reverses the chain map and sends a nonzero
coordinate to eighteen. The split coefficient sequence of integers and their two-fold product
gives both orientations of Hom short exactness and a genuine six-term coefficient window.

A projective single complex in degree one has the nonidentity automorphism multiplication by
minus one. Its Hom quasi-isomorphism retains that map, and its cohomology comparison remains
natural in coefficients. Single-support and fully faithful comparisons are tested on nonzero
morphisms, together with their relevant instance inference.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace HomCochainComplexClients

private abbrev C := ModuleCat ℤ
private abbrev Z := ModuleCat.of ℤ ℤ
private abbrev ZZ := ModuleCat.of ℤ (ℤ × ℤ)

private def twice : Z ⟶ Z := ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
private def three : Z ⟶ Z := ModuleCat.ofHom ((3 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

private abbrev twoTerm : ChainComplex C ℕ :=
  ChainComplex.mk Z Z (0 : C) twice 0 (by simp)
    (fun _ => ⟨(0 : C), 0, by simp⟩)

private abbrev homTwo : CochainComplex AddCommGrpCat ℕ :=
  (homCochainComplexFunctor C Z).obj (Opposite.op twoTerm)

example : (show Z ⟶ Z from (homTwo.d 0 1).hom (𝟙 Z)).hom (3 : ℤ) = (6 : ℤ) := by
  change (twice ≫ 𝟙 Z).hom (3 : ℤ) = (6 : ℤ)
  norm_num [twice]

private def tripleChain : twoTerm ⟶ twoTerm := (3 : ℤ) • 𝟙 twoTerm

example :
    (show Z ⟶ Z from
      (((homCochainComplexFunctor C Z).map tripleChain.op).f 0).hom twice).hom (3 : ℤ) =
        (18 : ℤ) := by
  change (((3 : ℤ) • 𝟙 Z) ≫ twice).hom (3 : ℤ) = (18 : ℤ)
  norm_num [twice]

private def includeFirst : Z ⟶ ZZ :=
  ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)

private def projectSecond : ZZ ⟶ Z :=
  ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ)

private def coefficientSequence : ShortComplex C :=
  ShortComplex.mk includeFirst projectSecond (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl)

private def coefficientSplitting : coefficientSequence.Splitting where
  r := ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ)
  s := ModuleCat.ofHom (LinearMap.inr ℤ ℤ ℤ)
  f_r := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro z; rfl
  s_g := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro z; rfl
  id := by
    apply ModuleCat.hom_ext
    change (LinearMap.inl ℤ ℤ ℤ).comp (LinearMap.fst ℤ ℤ ℤ) +
      (LinearMap.inr ℤ ℤ ℤ).comp (LinearMap.snd ℤ ℤ ℤ) = LinearMap.id
    apply LinearMap.ext
    intro z
    rcases z with ⟨a, b⟩
    simp

private theorem coefficient_shortExact : coefficientSequence.ShortExact :=
  coefficientSplitting.shortExact

private abbrev singleFunctor : C ⥤ ChainComplex C ℕ :=
  HomologicalComplex.single C (ComplexShape.down ℕ) 1

private abbrev singleChain : ChainComplex C ℕ := singleFunctor.obj Z

private instance : Projective Z :=
  ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ ℤ)

private instance (n : ℕ) : Projective (singleChain.X n) := by
  by_cases hn : n = 1
  · subst n
    simpa [singleChain, singleFunctor] using (inferInstance : Projective Z)
  · exact (isZero_single_obj_X (ComplexShape.down ℕ) 1 Z n hn).projective

private def chainSequence : ShortComplex (ChainComplex C ℕ) :=
  coefficientSequence.map singleFunctor

private theorem chain_shortExact : chainSequence.ShortExact :=
  (coefficientSplitting.map singleFunctor).shortExact

private def chain_degreewise_split (n : ℕ) :
    SplitMono ((chainSequence.map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).f) :=
  ((coefficientSplitting.map singleFunctor).map
    (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).splitMono_f

-- Contravariant chain exactness reverses the three objects.
example : (homCochainShortComplex chainSequence Z).ShortExact :=
  homCochainShortComplex_shortExact_of_degreewise_splitMono
    chainSequence chain_shortExact chain_degreewise_split Z

-- Covariant coefficient exactness retains the order, using earned term projectivity.
example : (coefficientSequence.map (homCochainComplexCoefficientFunctor singleChain)).ShortExact :=
  homCochainComplexCoefficientFunctor_map_shortExact_of_projective
    singleChain coefficientSequence coefficient_shortExact

example : (homCochainComplexCoefficientFunctor singleChain).Additive := inferInstance
example : PreservesLimitsOfShape (Discrete (Fin 2)) (homCochainComplexFunctor C Z) :=
  inferInstance

private def oneIndexFamily : Discrete Unit ⥤ ChainComplex C ℕ :=
  (Functor.const (Discrete Unit)).obj singleChain

private instance (x : Discrete Unit) (n : ℕ) : Projective ((oneIndexFamily.obj x).X n) :=
  inferInstanceAs (Projective (singleChain.X n))

private def exactWindow : ComposableArrows.ExactSequences AddCommGrpCat 5 :=
  (((homCochainComplexExactSequenceBifunctor_of_projective oneIndexFamily 0).obj
    ⟨coefficientSequence, coefficient_shortExact⟩).obj (Opposite.op (Discrete.mk ())))

private abbrev coefficientHomSequence :=
  coefficientSequence.map (homCochainComplexCoefficientFunctor singleChain)

private theorem coefficientHom_shortExact : coefficientHomSequence.ShortExact :=
  homCochainComplexCoefficientFunctor_map_shortExact_of_projective
    singleChain coefficientSequence coefficient_shortExact

example : exactWindow.obj.Exact := exactWindow.property

example : exactWindow.obj =
    HomologicalComplex.HomologySequence.composableArrows₅
      coefficientHom_shortExact 0 1 (by simp) := rfl

example : exactWindow.obj.map' 2 3 = coefficientHom_shortExact.δ 0 1 (by simp) := rfl

-- The supported coefficient arrow is the literal nonzero inclusion on Hom groups.
example :
    (show singleChain.X 1 ⟶ ZZ from
      (((homCochainComplexCoefficientFunctor singleChain).map includeFirst).f 1).hom
        ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1 Z).hom ≫ three)).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1 Z).inv.hom (2 : ℤ)) =
      ((6 : ℤ), (0 : ℤ)) := by
  change includeFirst.hom (three.hom (2 : ℤ)) = ((6 : ℤ), (0 : ℤ))
  norm_num [includeFirst, three]
  exact LinearMap.inl_apply (6 : ℤ)

private def negativeIso : singleChain ≅ singleChain :=
  singleFunctor.mapIso ((LinearEquiv.neg ℤ : ℤ ≃ₗ[ℤ] ℤ).toModuleIso)

private instance : QuasiIso negativeIso.hom := inferInstance

example : QuasiIso ((homCochainComplexFunctor C Z).map negativeIso.hom.op) :=
  homCochainComplexFunctor_map_quasiIso_of_projective negativeIso.hom Z

example :
    (homCochainComplexHomologyNatIsoOfProjectiveQuasiIso negativeIso.hom 1).hom.app Z =
      homologyMap ((homCochainComplexFunctor C Z).map negativeIso.hom.op) 1 :=
  homCochainComplexHomologyNatIsoOfProjectiveQuasiIso_hom_app negativeIso.hom 1 Z

example :
    (homCochainComplexHomologyFunctor C singleChain 1).map includeFirst ≫
        (homCochainComplexHomologyNatIsoOfProjectiveQuasiIso
          negativeIso.hom 1).hom.app ZZ =
      (homCochainComplexHomologyNatIsoOfProjectiveQuasiIso
        negativeIso.hom 1).hom.app Z ≫
        (homCochainComplexHomologyFunctor C singleChain 1).map includeFirst :=
  (homCochainComplexHomologyNatIsoOfProjectiveQuasiIso negativeIso.hom 1).hom.naturality
    includeFirst

private def supportedHomologyIso :
    (homCochainComplexHomologyFunctor C singleChain 1).obj Z ≅ AddCommGrpCat.of (Z ⟶ Z) :=
  (homCochainComplexHomologyFunctorSingleIso Z 1).app Z

private def homologyValue : (homCochainComplexHomologyFunctor C singleChain 1).obj Z :=
  supportedHomologyIso.inv.hom twice

private theorem homologyValue_coordinate : supportedHomologyIso.hom.hom homologyValue = twice :=
  ConcreteCategory.congr_hom supportedHomologyIso.inv_hom_id twice

example : homologyValue ≠ 0 := by
  intro h
  have h' := congrArg supportedHomologyIso.hom.hom h
  rw [homologyValue_coordinate, map_zero] at h'
  have h'' := congrArg (fun f : Z ⟶ Z => f.hom (1 : ℤ)) h'
  norm_num [twice] at h''

-- The concrete projective quasi-isomorphism component is an actual isomorphism and maps
-- the detected nonzero cohomology class to a nonzero class.
example :
    ((homCochainComplexHomologyNatIsoOfProjectiveQuasiIso
      negativeIso.hom 1).hom.app Z).hom homologyValue ≠ 0 := by
  intro h
  have hh := congrArg
    ((homCochainComplexHomologyNatIsoOfProjectiveQuasiIso negativeIso.hom 1).inv.app Z).hom h
  have hround := ConcreteCategory.congr_hom
    ((homCochainComplexHomologyNatIsoOfProjectiveQuasiIso negativeIso.hom 1).app Z).hom_inv_id
    homologyValue
  have hzero : homologyValue = 0 := by
    simpa only [map_zero, CategoryTheory.ConcreteCategory.id_apply] using hround.symm.trans hh
  have h' := congrArg supportedHomologyIso.hom.hom hzero
  rw [homologyValue_coordinate, map_zero] at h'
  have h'' := congrArg (fun f : Z ⟶ Z => f.hom (1 : ℤ)) h'
  norm_num [twice] at h''

private def singleHomIso :
    (homCochainComplexFunctor C Z).obj (Opposite.op singleChain) ≅
      (HomologicalComplex.single AddCommGrpCat (ComplexShape.up ℕ) 1).obj
        (AddCommGrpCat.of (Z ⟶ Z)) :=
  homCochainComplexSingleIso Z Z 1

example : singleHomIso.hom.f 1 = (homCochainComplexSingleSupportedIso Z 1).hom.app Z :=
  homCochainComplexSingleIso_hom_f_self Z Z 1

example : IsZero (((homCochainComplexFunctor C Z).obj (Opposite.op singleChain)).X 0) := by
  let e := Hom.isoApp singleHomIso 0
  exact (isZero_single_obj_X (ComplexShape.up ℕ) 1 (AddCommGrpCat.of (Z ⟶ Z)) 0
    (by decide)).of_iso e

example : IsZero ((homCochainComplexHomologyFunctor C singleChain 0).obj Z) :=
  (isZero_homCochainComplexHomologyFunctorSingle Z 1 0 (by decide)).obj Z

example :
    (homCochainComplexSingle₀Iso Z Z).hom.f 0 twice = twice := by
  rw [homCochainComplexSingle₀Iso_hom_f_zero]
  rfl

private def identityFullyFaithful : (𝟭 C).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _

example :
    ((homCochainComplexFunctorIsoOfFullyFaithful (𝟭 C) identityFullyFaithful Z).hom.app
      (Opposite.op twoTerm)).f 0 twice = twice :=
  homCochainComplexFunctorIsoOfFullyFaithful_hom_app_f_apply
    (𝟭 C) identityFullyFaithful Z twoTerm 0 twice

end HomCochainComplexClients
