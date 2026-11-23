/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCoherence
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Tactic.NormNum

/-!
# Consumers of coherent second translations

The concrete comma arrow below adds a nonzero rank-one integral module as its
stabilizer. The translating object is a binary biproduct, and its parameter
isomorphism exchanges the two summands. This checks naturality on genuine
stabilization arrows and retains the exact second-translation provider.
The generic tests separately keep the independent category universes and the
small-universe nerve-wrapper scope visible.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject SInverseS MonoidalCategory Simplicial

namespace SInverseSSecondTranslationCoherenceTests

private abbrev Modules := ModuleCat.{0} ℤ

private def unitModule : Modules := ModuleCat.of ℤ ℤ

private def zeroPair : Pair Modules := ⟨0, 0⟩

private def stabilizedPair : Pair Modules := ⟨unitModule ⊞ 0, unitModule ⊞ 0⟩

private def rawStabilization : RawHom zeroPair stabilizedPair :=
  RawHom.diagonalAdd unitModule zeroPair

private def stabilization : zeroPair ⟶ stabilizedPair := Hom.mk rawStabilization

private def base : Translation Modules :=
  (translationProjection (C := Modules)).obj stabilizedPair

private def target : CostructuredArrow (translationProjection (C := Modules)) base :=
  CostructuredArrow.mk (𝟙 base)

private def source : CostructuredArrow (translationProjection (C := Modules)) base :=
  CostructuredArrow.mk
    ((translationProjection (C := Modules)).map stabilization ≫ 𝟙 base)

private def stabilizationComma : source ⟶ target :=
  CostructuredArrow.homMk' target stabilization

private def scalar : Modules := unitModule ⊞ unitModule

private def exchange : scalar ≅ scalar := biprod.braiding unitModule unitModule

private theorem unitModule_not_isZero : ¬ IsZero unitModule := by
  intro h
  have hs : Subsingleton ℤ := ModuleCat.subsingleton_of_isZero h
  have he : (0 : ℤ) = 1 := hs.elim _ _
  norm_num at he

-- This stabilization has a genuinely nonzero label.
example : ¬ IsZero rawStabilization.stabilizer := unitModule_not_isZero

-- The parameter isomorphism is not the identity of the translating object.
example : exchange ≠ Iso.refl scalar := by
  intro h
  have he := congrArg (fun i : scalar ≅ scalar =>
    (biprod.inl : unitModule ⟶ scalar) ≫ i.hom ≫
      (biprod.fst : scalar ⟶ unitModule)) h
  have hid : (𝟙 unitModule : unitModule ⟶ unitModule) = 0 := by
    simpa [exchange, scalar, biprod.braiding] using he.symm
  exact unitModule_not_isZero ((IsZero.iff_id_eq_zero unitModule).mpr hid)

-- The scalar comparison is natural on the actual nonzero-stabilizer comma arrow.
example :
    (secondTranslationCostructuredMap scalar base).map stabilizationComma ≫
        (secondTranslationCostructuredIsoOfIso exchange base).hom.app target =
      (secondTranslationCostructuredIsoOfIso exchange base).hom.app source ≫
        (secondTranslationCostructuredMap scalar base).map stabilizationComma :=
  (secondTranslationCostructuredIsoOfIso exchange base).hom.naturality stabilizationComma

-- The left component is the exact zero-stabilizer coordinate representative.
example :
    ((secondTranslationCostructuredIsoOfIso exchange base).hom.app source).left =
      Hom.mk (RawHom.ofCoordinateIsos
        (X := translateSecondObj scalar source.left)
        (Y := translateSecondObj scalar source.left)
        (Iso.refl source.left.fst)
        (biprod.mapIso exchange (Iso.refl source.left.snd))) := rfl

private def baseChange : base ⟶ (Translation.translateFunctor unitModule).obj base :=
  Translation.diagonalAddHom unitModule base

-- Canonical base change commutes with the nontrivial scalar comparison.
example :
    (secondTranslationCostructuredMapNaturalityIso scalar baseChange).hom.app source ≫
        (CostructuredArrow.map baseChange).map
          ((secondTranslationCostructuredIsoOfIso exchange base).hom.app source) =
      (secondTranslationCostructuredIsoOfIso exchange
          ((Translation.translateFunctor unitModule).obj base)).hom.app
        ((CostructuredArrow.map baseChange).obj source) ≫
        (secondTranslationCostructuredMapNaturalityIso scalar baseChange).hom.app source :=
  secondTranslationCostructuredIsoOfIso_baseChange exchange baseChange source

section GeneralUniverses

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

-- The full unit law is available independently of object/morphism universe equality.
example (A : C) (B : Translation C) :
    secondTranslationCostructuredBiprodIso (0 : C) A B ≪≫
        Functor.isoWhiskerLeft (secondTranslationCostructuredMap A B)
          (secondTranslationCostructuredZeroIso B) ≪≫
        Functor.rightUnitor (secondTranslationCostructuredMap A B) =
      secondTranslationCostructuredIsoOfIso
        (isoZeroBiprod (X := (0 : C)) (Y := A) (isZero_zero C)).symm B :=
  secondTranslationCostructuredBiprodIso_leftUnit A B

-- The multiplication lineator law also holds for arbitrary category universes.
example (A A' : C) {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (secondTranslationCostructuredMapNaturalityIso (A ⊞ A') g).hom.app X ≫
        (CostructuredArrow.map g).map
          ((secondTranslationCostructuredBiprodIso A A' B).hom.app X) =
      (secondTranslationCostructuredBiprodIso A A' D).hom.app
          ((CostructuredArrow.map g).obj X) ≫
        (secondTranslationCostructuredMap A D).map
          ((secondTranslationCostructuredMapNaturalityIso A' g).hom.app X) ≫
        (secondTranslationCostructuredMapNaturalityIso A g).hom.app
          ((secondTranslationCostructuredMap A' B).obj X) :=
  secondTranslationCostructuredBiprodIso_baseChange A A' g X

end GeneralUniverses

-- The inherited diagram-level nerve wrapper is used at exactly its supported scope.
example {C : Type} [Category.{0} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] {A A' : C} (e : A ≅ A')
    (B : Translation C) :
    SSet.Homotopy ((secondTranslationRightCommaNerveDiagramNatTrans A).app B)
      ((secondTranslationRightCommaNerveDiagramNatTrans A').app B) :=
  secondTranslationRightCommaScalarHomotopy e B

#print axioms CategoryTheory.SInverseS.translateSecondIsoOfIso
#print axioms CategoryTheory.SInverseS.translateSecondZeroIso
#print axioms CategoryTheory.SInverseS.translateSecondBiprodIso
#print axioms CategoryTheory.SInverseS.translateSecondIsoOfIso_refl
#print axioms CategoryTheory.SInverseS.translateSecondIsoOfIso_trans
#print axioms CategoryTheory.SInverseS.translateSecondBiprodIso_parameter_naturality
#print axioms CategoryTheory.SInverseS.translateSecondBiprodIso_leftUnit
#print axioms CategoryTheory.SInverseS.translateSecondBiprodIso_rightUnit
#print axioms CategoryTheory.SInverseS.translateSecondBiprodIso_pentagon
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredIsoOfIso
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredZeroIso
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredBiprodIso
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredIsoOfIso_refl
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredIsoOfIso_trans
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredBiprodIso_parameter_naturality
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredBiprodIso_leftUnit
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredBiprodIso_rightUnit
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredBiprodIso_pentagon
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredIsoOfIso_exchange
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredIsoOfIso_baseChange
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredZeroIso_baseChange
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredBiprodIso_baseChange
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredIsoOfIso_nerveMap_baseChange
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredZeroIso_nerveMap_baseChange
#print axioms CategoryTheory.SInverseS.secondTranslationCostructuredBiprodIso_nerveMap_baseChange
#print axioms CategoryTheory.SInverseS.secondTranslationRightCommaScalarHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationRightCommaZeroHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationRightCommaBiprodHomotopy

end SInverseSSecondTranslationCoherenceTests

end
