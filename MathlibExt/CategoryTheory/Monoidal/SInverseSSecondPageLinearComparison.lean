/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.CoefficientLinear
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationPageScalars
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedSpectralSequence
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCoefficient
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageNaturality
public import MathlibExt.CategoryTheory.Monoidal.SInverseSIteratedHomologyActionNaturality

/-!
# The actual second page as integral coefficient modules

For every native additive category, coefficient group and natural bidegree,
construct the linear isomorphism from the actual BK module second page to
whole-core coefficient homology. Its underlying forward map is the original
page-forget comparison followed by the inverse of the original kappa map.
The inverse follows the same canonical route in reverse.

Fixed-base second translation, actual second-page naturality and the generic
coefficient-functor scalar law give equivariance. Finite integral coefficient
sums prove full scalar compatibility. The actual localized model, Phi and
the final Q-plus comparison remain separate, unfinished constructions.
-/

public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂

universe u

namespace CategoryTheory.SInverseS

local instance secondPageLinearComparisonHasCoproductsAddCommGrpCat :
    HasCoproducts.{u} AddCommGrpCat.{u} := by
  let h : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

local instance secondPageLinearComparisonHasCoproductsModuleCat
    (A : Type u) [Ring A] : HasCoproducts.{u} (ModuleCat.{u} A) := by
  let h : HasColimitsOfSize.{u, u} (ModuleCat.{u} A) := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)



variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u})

local notation "Alg" => MonoidAlgebra ℤ (Multiplicative (Skeleton C))
local notation "P" => secondTranslationBKModuleSpectralSequence (C := C) R

/-- This is the existing module structure on the same forgotten carrier.
It supplies no scalar-compatibility hypothesis. -/
@[instance_reducible] private def forgottenCarrierModule (M : ModuleCat.{u} Alg) :
    Module Alg (((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).obj M) := inferInstanceAs (Module Alg M)

attribute [local instance] forgottenCarrierModule

/-- The exact additive comparison, before proving scalar compatibility. -/
private def gammaAdditiveIso (p q : ℕ) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).obj (((P).page 2 (by omega)).X (p, q)) ≅
      ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).obj (coreTranslationActionCoefficientHomology C R q p) :=
  HomologicalComplex.Hom.isoApp
      (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)) (p, q) ≪≫
    (coreTranslationActionSecondPageIso C R p q).symm

private theorem gammaAdditiveIso_hom (p q : ℕ) :
    (gammaAdditiveIso (C := C) R p q).hom =
      (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).hom.f (p, q) ≫
        (coreTranslationActionSecondPageIso C R p q).inv := rfl

private theorem gammaAdditiveIso_inv (p q : ℕ) :
    (gammaAdditiveIso (C := C) R p q).inv =
      (coreTranslationActionSecondPageIso C R p q).hom ≫
        (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).inv.f (p, q) := rfl

/-- The coefficient endomorphism is intrinsic scalar multiplication. -/
private def coreScalarNatTrans (q : ℕ) (s : Alg) :
    coreTranslationCoefficientFunctor C R q ⟶ coreTranslationCoefficientFunctor C R q :=
  s • 𝟙 _

private theorem coreScalarNatTrans_monomial_app (q : ℕ) (W : C) (B : Translation C) :
    (coreScalarNatTrans (C := C) R q
      (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ))).app B =
        coreTranslationCoefficientMap C R q (toSkeleton W) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The actual second-coordinate map intertwines the fixed-base comma/core
comparison, as a natural transformation of coefficient systems. -/
private theorem secondTranslation_coefficient_square (q : ℕ) (W : C) :
    Functor.whiskerRight (secondTranslationRightCommaNerveDiagramNatTrans W)
        (SSet.homologyFunctor R q) ≫
      (costructuredCoreTranslationCoefficientNatIso C R q).hom =
    (costructuredCoreTranslationCoefficientNatIso C R q).hom ≫
      Functor.whiskerRight (coreScalarNatTrans (C := C) R q
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ)))
        (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
          AddCommGrpCat.{u}) := by
  apply NatTrans.ext
  funext B
  change SSet.homologyMap
      (nerveMap (secondTranslationCostructuredMap W B)) R q ≫
    (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).map ((coreScalarNatTrans (C := C) R q
          (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ))).app B)
  rw [coreScalarNatTrans_monomial_app]
  exact secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison C R W B q

/-- Applying actual BK and coefficient homology functors lifts the fixed-base
square through the alternating and normalized bars. -/
private theorem secondTranslation_iterated_square (p q : ℕ) (W : C) :
    HomologicalComplex.homologyMap
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
            (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (secondTranslationBKBicomplexMap R W)) p ≫
      (translationBKIteratedHomologyCoefficientIso C R p q).hom =
    (translationBKIteratedHomologyCoefficientIso C R p q).hom ≫
      ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).map ((CategoryHomology.homologyWithCoefficientsFunctor
        (C := Translation C) (A := ModuleCat.{u} Alg) p).map
          (coreScalarNatTrans (C := C) R q
            (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ)))) := by
  let H : (Translation C ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    CategoryHomology.homologyWithCoefficientsFunctor
      (C := Translation C) (A := AddCommGrpCat.{u}) p
  let V : Translation C ⥤ AddCommGrpCat.{u} :=
    SSet.rightCommaNerveDiagram (translationProjection (C := C)) ⋙ SSet.homologyFunctor R q
  let N : Translation C ⥤ ModuleCat.{u} Alg := coreTranslationCoefficientFunctor C R q
  have hBK := SSet.bkVerticalHorizontalCoefficientHomologyIso_hom_naturality
    R (secondTranslationRightCommaNerveDiagramNatTrans W) p q
  have hCoefficient := congrArg
    (fun k : V ⟶ N ⋙ (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u}) => H.map k)
    (secondTranslation_coefficient_square (C := C) R q W)
  rw [Functor.map_comp, Functor.map_comp] at hCoefficient
  have hForget := homologyWithCoefficientsForgetIso_inv_naturality
    (coreScalarNatTrans (C := C) R q
      (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ))) p
  have hCoefficientAssoc := congrArg
    (fun k : H.obj V ⟶ H.obj (N ⋙ (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})) =>
      k ≫ (homologyWithCoefficientsForgetIso N p).inv) hCoefficient
  simp only [Category.assoc] at hCoefficientAssoc
  dsimp only [secondTranslationBKBicomplexMap]
  simp only [translationBKIteratedHomologyCoefficientIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, hBK]
  simp only [Category.assoc]
  rw [hCoefficientAssoc]
  rw [hForget]

set_option diagnostics true in
/-- Transparent specialization of the original receiver with concrete
categories and the original named cofibered projection dictionary. -/
private abbrev cachedCofiberedIteratedIso (p q : ℕ) :=
  @Functor.IsCofibered.cofiberedVerticalHorizontalHomologyIso.{u, u}
    (Translation C) (Pair C)
    (inferInstanceAs (Category.{u} (Translation C)))
    (inferInstanceAs (Category.{u} (Pair C)))
    (translationProjection (C := C))
    (translationProjection_isCofibered (C := C)) R p q

/-- The original comma comparison, with its base category fixed before
projecting its forward map. -/
private abbrev cachedCommaIteratedIso (p q : ℕ) :=
  @SSet.bkVerticalHorizontalCoefficientHomologyIso.{u, u}
    (Translation C) (inferInstanceAs (Category.{u} (Translation C))) R
    (SSet.rightCommaNerveDiagram (translationProjection (C := C))) p q

/-- The actual original coefficient comparison uses the same existing
cofibered dictionary; this transparent cache supplies no new witness. -/
private abbrev cachedCostructuredFiberIso (q : ℕ) :=
  letI : (translationProjection (C := C)).IsCofibered :=
    translationProjection_isCofibered (C := C)
  Functor.IsCofibered.costructuredFiberHomologyNatIso
    (S := Translation C) (X := Pair C)
    (p := translationProjection (C := C)) AddCommGrpCat.{u} R q

set_option diagnostics true in
/-- The actual strict-fiber route factors through the actual comma route.
Naturality of the Dold--Kan projection fixes the comparison, rather than
choosing a different second-page isomorphism. -/
private theorem cofiberedIterated_hom_factor (p q : ℕ) :
    (cachedCofiberedIteratedIso (C := C) R p q).hom =
    (cachedCommaIteratedIso (C := C) R p q).hom ≫
      (CategoryHomology.homologyWithCoefficientsFunctor
        (C := Translation C) (A := AddCommGrpCat.{u}) p).map
          (cachedCostructuredFiberIso (C := C) R q).hom := by
  let D : Translation C ⥤ SSet.{u} :=
    SSet.rightCommaNerveDiagram (translationProjection (C := C))
  let F : Translation C ⥤ AddCommGrpCat.{u} :=
    Functor.IsCofibered.costructuredHomologyFunctor
      (p := translationProjection (C := C)) AddCommGrpCat.{u} R q
  let G : Translation C ⥤ AddCommGrpCat.{u} :=
    Functor.IsCofibered.fiberHomologyFunctor
      (p := translationProjection (C := C)) AddCommGrpCat.{u} R q
  let e : F ≅ G := cachedCostructuredFiberIso (C := C) R q
  let f : CategoryHomology.coefficientBarSimplicial F ⟶
      CategoryHomology.coefficientBarSimplicial G :=
    CategoryHomology.coefficientBarSimplicialMap e.hom
  let beta : (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R D).verticalHomologyComplex q ≅
      CategoryHomology.coefficientBarComplex F :=
    SSet.bkVerticalHomologyCoefficientBarComplexIso.{u, u} R D q
  let etaF : CategoryHomology.homologyWithCoefficients F p ≅
      (CategoryHomology.coefficientBarComplex F).homology p :=
    (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := CategoryHomology.coefficientBarSimplicial F)).toHomologyIso p
  let etaG : CategoryHomology.homologyWithCoefficients G p ≅
      (CategoryHomology.coefficientBarComplex G).homology p :=
    (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := CategoryHomology.coefficientBarSimplicial G)).toHomologyIso p
  let a : ((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R D).verticalHomologyComplex q).homology p ⟶
      (CategoryHomology.coefficientBarComplex F).homology p :=
    HomologicalComplex.homologyMap beta.hom p
  let b : (CategoryHomology.coefficientBarComplex F).homology p ⟶
      (CategoryHomology.coefficientBarComplex G).homology p :=
    HomologicalComplex.homologyMap
      ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map f) p
  let n : CategoryHomology.homologyWithCoefficients F p ⟶
      CategoryHomology.homologyWithCoefficients G p :=
    HomologicalComplex.homologyMap
      ((AlgebraicTopology.normalizedMooreComplex AddCommGrpCat.{u}).map f) p
  have hDK : b ≫ etaG.inv = etaF.inv ≫ n :=
    AlgebraicTopology.DoldKan.normalizedMooreAlternatingHomologyIso_inv_naturality f p
  change HomologicalComplex.homologyMap
      (beta.hom ≫ (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map f) p ≫
      etaG.inv = (a ≫ etaF.inv) ≫ n
  have hComp : HomologicalComplex.homologyMap
      (beta.hom ≫ (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map f) p =
      a ≫ b :=
    HomologicalComplex.homologyMap_comp beta.hom
      ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map f) p
  exact (congrArg
    (fun k : ((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R D).verticalHomologyComplex q).homology p ⟶
      (CategoryHomology.coefficientBarComplex G).homology p => k ≫ etaG.inv) hComp).trans
      ((Category.assoc a b etaG.inv).trans
        ((congrArg
          (fun k : (CategoryHomology.coefficientBarComplex F).homology p ⟶
            CategoryHomology.homologyWithCoefficients G p => a ≫ k) hDK).trans
          (Category.assoc a etaF.inv n).symm))

/-- The exact pre-existing kappa inverse is the original signed second-page
comparison followed by the exact iterated comma/core route. -/
private theorem kappa_inv_eq_eta_iterated (p q : ℕ) :
    (coreTranslationActionSecondPageIso C R p q).inv =
    (horizontalSecondPageVerticalHorizontalHomologyIso
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
        (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) p q).hom ≫
      (translationBKIteratedHomologyCoefficientIso C R p q).hom := by
  simp only [coreTranslationActionSecondPageIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, translationBKSecondPageIso,
    Functor.IsCofibered.cofiberedBKSecondPageIso, Iso.trans_hom]
  rw [cofiberedIterated_hom_factor]
  simp only [translationBKIteratedHomologyCoefficientIso,
    costructuredCoreTranslationCoefficientNatIso,
    coreTranslationActionCoefficientHomologyForgetIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

/-- Naturality for the actual fixed-base second-page map, using the literal
pre-existing kappa inverse, before identifying the induced coefficient map
with the scalar action on its homology module. -/
private theorem actualSecondPage_coefficient_square (p q : ℕ) (W : C) :
    horizontalSecondPageMapOfBicomplex (secondTranslationBKBicomplexMap R W) p q ≫
      (coreTranslationActionSecondPageIso C R p q).inv =
    (coreTranslationActionSecondPageIso C R p q).inv ≫
      ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).map ((CategoryHomology.homologyWithCoefficientsFunctor
        (C := Translation C) (A := ModuleCat.{u} Alg) p).map
          (coreScalarNatTrans (C := C) R q
            (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ)))) := by
  let K : HomologicalComplex₂ AddCommGrpCat.{u}
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
      (SSet.rightCommaNerveDiagram (translationProjection (C := C)))
  let f : K ⟶ K := secondTranslationBKBicomplexMap R W
  let H : (Translation C ⥤ ModuleCat.{u} Alg) ⥤ ModuleCat.{u} Alg :=
    CategoryHomology.homologyWithCoefficientsFunctor
      (C := Translation C) (A := ModuleCat.{u} Alg) p
  let M : Translation C ⥤ ModuleCat.{u} Alg := coreTranslationCoefficientFunctor C R q
  let e : (K.verticalHomologyComplex q).homology p ≅ ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).obj (H.obj M) :=
    translationBKIteratedHomologyCoefficientIso C R p q
  let s : Alg := MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ)
  let g : ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).obj (H.obj M) ⟶ ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).obj (H.obj M) :=
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).map (H.map (coreScalarNatTrans (C := C) R q s))
  have hEta := horizontalSecondPageVerticalHorizontalHomologyIso_hom_naturality
    f p q
  have hIterated : HomologicalComplex.homologyMap (verticalHomologyComplexMap f q) p ≫
      e.hom = e.hom ≫ g :=
    secondTranslation_iterated_square (C := C) R p q W
  rw [kappa_inv_eq_eta_iterated]
  rw [← Category.assoc, hEta, Category.assoc, hIterated]
  exact (Category.assoc _ _ _).symm

/-- The genuine fixed-base second-page map corresponds to the intrinsic
monomial scalar on the actual coefficient-homology module. -/
private theorem kappa_inv_actualSecondPage_apply (p q : ℕ) (W : C)
    (y : ((translationBKHomologySpectralSequence C R).page 2).X (p, q)) :
    (coreTranslationActionSecondPageIso C R p q).inv
      (horizontalSecondPageMapOfBicomplex (secondTranslationBKBicomplexMap R W) p q y) =
    MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ) •
      (coreTranslationActionSecondPageIso C R p q).inv y := by
  have h := actualSecondPage_coefficient_square (C := C) R p q W
  dsimp only [coreScalarNatTrans] at h
  rw [Functor.map_smul, Functor.map_id] at h
  have hValue := ConcreteCategory.congr_hom h y
  exact hValue

private theorem gammaAdditiveIso_single_one_apply (p q : ℕ) (W : C)
    (x : (((P).page 2 (by omega)).X (p, q))) :
    (gammaAdditiveIso (C := C) R p q).hom
      (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ) • x) =
    MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ) •
      (gammaAdditiveIso (C := C) R p q).hom x := by
  have hScalar := secondTranslationBKModulePageForgetIso_single_apply
    (C := C) R 2 (by omega) p q W 1 x
  simp only [one_zsmul] at hScalar
  rw [gammaAdditiveIso_hom]
  change (coreTranslationActionSecondPageIso C R p q).inv
      ((secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).hom.f (p, q)
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ) • x)) = _
  rw [hScalar]
  exact kappa_inv_actualSecondPage_apply (C := C) R p q W _

private theorem gammaAdditiveIso_monomial_one_apply (p q : ℕ) (m : Multiplicative (Skeleton C))
    (x : (((P).page 2 (by omega)).X (p, q))) :
    (gammaAdditiveIso (C := C) R p q).hom (MonoidAlgebra.single m (1 : ℤ) • x) =
      MonoidAlgebra.single m (1 : ℤ) • (gammaAdditiveIso (C := C) R p q).hom x := by
  have hm : Multiplicative.ofAdd (toSkeleton m.toAdd.out) = m :=
    congrArg Multiplicative.ofAdd (toSkeleton_fromSkeleton_obj m.toAdd)
  have h := gammaAdditiveIso_single_one_apply (C := C) R p q m.toAdd.out x
  rw [hm] at h
  exact h

private theorem gammaAdditiveIso_monomial_apply (p q : ℕ) (m : Multiplicative (Skeleton C)) (z : ℤ)
    (x : (((P).page 2 (by omega)).X (p, q))) :
    (gammaAdditiveIso (C := C) R p q).hom (MonoidAlgebra.single m z • x) =
      MonoidAlgebra.single m z • (gammaAdditiveIso (C := C) R p q).hom x := by
  have hz : MonoidAlgebra.single m z = z • MonoidAlgebra.single m (1 : ℤ) := by simp
  rw [hz, smul_assoc, map_zsmul,
    gammaAdditiveIso_monomial_one_apply, smul_assoc]

/-- Every scalar is its actual finite integral coefficient sum; generator
equivariance therefore proves full A-linearity of the exact additive map. -/
private theorem gammaAdditiveIso_smul_apply (p q : ℕ) (a : Alg)
    (x : (((P).page 2 (by omega)).X (p, q))) :
    (gammaAdditiveIso (C := C) R p q).hom (a • x) =
      a • (gammaAdditiveIso (C := C) R p q).hom x := by
  let g := (gammaAdditiveIso (C := C) R p q).hom
  have ha : a = ∑ m ∈ a.coeff.support, MonoidAlgebra.single m (a.coeff m) :=
    (MonoidAlgebra.sum_coeff_single a).symm
  calc
    g (a • x) = g ((∑ m ∈ a.coeff.support, MonoidAlgebra.single m (a.coeff m)) • x) := by
      rw [← ha]
    _ = ∑ m ∈ a.coeff.support, g (MonoidAlgebra.single m (a.coeff m) • x) := by
      rw [Finset.sum_smul]
      exact map_sum g.hom _ _
    _ = ∑ m ∈ a.coeff.support, MonoidAlgebra.single m (a.coeff m) • g x := by
      apply Finset.sum_congr rfl
      intro m _
      exact gammaAdditiveIso_monomial_apply (C := C) R p q m (a.coeff m) x
    _ = a • g x := by rw [← Finset.sum_smul, ← ha]

/-- The full linear equivalence is constructed from the exact additive
bijection and the derived scalar law; its inverse is the same canonical
additive inverse, with no inverse-linearity premise. -/
private def gammaLinearEquiv (p q : ℕ) :
    (((P).page 2 (by omega)).X (p, q)) ≃ₗ[Alg]
      coreTranslationActionCoefficientHomology C R q p where
  toAddEquiv := (gammaAdditiveIso (C := C) R p q).addCommGroupIsoToAddEquiv
  map_smul' := gammaAdditiveIso_smul_apply (C := C) R p q

/-- The actual BK module second page is canonically linearly isomorphic to
whole-core coefficient homology at every bidegree, including the zero column. -/
def secondTranslationBKModuleSecondPageCoefficientIso (p q : ℕ) :
    (((P).page 2 (by omega)).X (p, q)) ≅
      coreTranslationActionCoefficientHomology C R q p :=
  (gammaLinearEquiv (C := C) R p q).toModuleIso

private theorem moduleIso_hom_forget (p q : ℕ) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).map (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).hom =
      (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).hom.f (p, q) ≫
        (coreTranslationActionSecondPageIso C R p q).inv := rfl

private theorem moduleIso_inv_forget (p q : ℕ) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).map (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).inv =
      (coreTranslationActionSecondPageIso C R p q).hom ≫
        (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).inv.f (p, q) := rfl

/-- After forgetting scalars, the forward map is exactly the original page
comparison followed by the inverse of the original kappa comparison. -/
theorem secondTranslationBKModuleSecondPageCoefficientIso_hom_forget (p q : ℕ) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).map (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).hom =
      (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).hom.f (p, q) ≫
        (coreTranslationActionSecondPageIso C R p q).inv := by
  exact moduleIso_hom_forget (C := C) R p q

/-- After forgetting scalars, the inverse is the exact reverse canonical
route through kappa and the inverse original page comparison. -/
theorem secondTranslationBKModuleSecondPageCoefficientIso_inv_forget (p q : ℕ) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C)))) AddCommGrpCat.{u})).map (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).inv =
      (coreTranslationActionSecondPageIso C R p q).hom ≫
        (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).inv.f (p, q) := by
  exact moduleIso_inv_forget (C := C) R p q

end CategoryTheory.SInverseS
