/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroRawMiddleMap
public import MathlibExt.KTheory.Exact.Extension.CompletedZeroRawDenominatorAgreement

/-!
# Actual ordinary numerator naturality on every completed-Core raw arrow

The two original raw numerators are transported to the exact ordinary
zero-row image objects using proved object and stabilizer values. Their
middle characteristic maps are the original canonical mapped raw middle.
The identity-coordinate zero-row component and its actual left-sum image
therefore intertwine the ordinary numerators. The extension morphism
criterion is used only in the ordinary extension category.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

universe uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

private theorem actualBinaryMapHEq
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasBinaryBiproducts D]
    {A B A' B' X Y X' Y' : D}
    (hA : A = A') (hB : B = B') (hX : X = X') (hY : Y = Y')
    {f : A ⟶ X} {f' : A' ⟶ X'} {g : B ⟶ Y} {g' : B' ⟶ Y'}
    (hf : HEq f f') (hg : HEq g g') : HEq (biprod.map f g) (biprod.map f' g') := by
  cases hA
  cases hB
  cases hX
  cases hY
  cases hf
  cases hg
  exact HEq.rfl

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualZeroGivenObject (A : Core C) :
    (zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C)).obj A =
      (zeroRow A).toExtension :=
  (givenRowFunctor_obj ((zeroRowFunctor (C := C)).obj A)).trans
    (congrArg (fun E : FixedTargetExtension C (0 : C) => E.toExtension)
      (show (zeroRowFunctor (C := C)).obj A = zeroRow A from rfl))

private theorem actualSourceNumeratorObject (a : SInverse (Core C) (Core C)) :
    (ExtensionCategory.stabilizedFunctorObject F
      (localizedObject (zeroLocalizedObject a))).of.1 =
      (zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
        ExtensionCategory.mapFunctor F).obj a.of.1 := by
  have h := congrArg Prod.fst (ExtensionCategory.stabilizedFunctorObject_of F
    (localizedObject (zeroLocalizedObject a)))
  exact h.trans (congrArg (ExtensionCategory.mapFunctor F).obj
    (actualZeroGivenObject a.of.1).symm)

omit [ExactCategory C] [F.IsExact] [F.Additive] in
private theorem actualTargetNumeratorObject (a : SInverse (Core C) (Core C)) :
    (localizedObject (zeroLocalizedObject
      (fromPairObj (⟨F.obj a.of.1.of, F.obj a.of.2.of⟩ : SInverseS.Pair D)))).of.1 =
      (F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1 :=
  (actualZeroGivenObject (C := D) (F.core.obj a.of.1)).symm

private theorem actualSourcePairObject (a : SInverse (Core C) (Core C)) :
    ExtensionCategory.stabilizedFunctorObject F
        (localizedObject (zeroLocalizedObject a)) =
      (inclusion (Core D) (ExtensionCategory D × Core D)).obj
        ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
          ExtensionCategory.mapFunctor F).obj a.of.1, F.core.obj a.of.2) := by
  have hNumerator := actualSourceNumeratorObject F a
  have hDenominator := congrArg Prod.snd (ExtensionCategory.stabilizedFunctorObject_of F
    (localizedObject (zeroLocalizedObject a)))
  exact congrArg (fun q : ExtensionCategory D × Core D =>
    (⟨q⟩ : SInverse (Core D) (ExtensionCategory D)))
      (Prod.ext hNumerator hDenominator)

/-- The whole original stabilized raw object has its exact ordinary pair presentation. -/
public theorem completedZeroSourceRawObject_value (a : SInverse (Core C) (Core C)) :
    ExtensionCategory.stabilizedFunctorObject F
        (localizedObject (zeroLocalizedObject a)) =
      (inclusion (Core D) (ExtensionCategory D × Core D)).obj
        ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
          ExtensionCategory.mapFunctor F).obj a.of.1, F.core.obj a.of.2) :=
  actualSourcePairObject F a

omit [ExactCategory C] [F.IsExact] [F.Additive] in
private theorem actualTargetPairObject (a : SInverse (Core C) (Core C)) :
    localizedObject (zeroLocalizedObject
        (fromPairObj (⟨F.obj a.of.1.of, F.obj a.of.2.of⟩ : SInverseS.Pair D))) =
      (inclusion (Core D) (ExtensionCategory D × Core D)).obj
        ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1,
          F.core.obj a.of.2) :=
  congrArg (fun q : ExtensionCategory D × Core D =>
    (⟨q⟩ : SInverse (Core D) (ExtensionCategory D)))
      (Prod.ext (actualTargetNumeratorObject F a) rfl)

omit [ExactCategory C] [F.IsExact] [F.Additive] in
/-- The whole original mapped-Core raw object has its exact ordinary pair presentation. -/
public theorem completedZeroTargetRawObject_value (a : SInverse (Core C) (Core C)) :
    localizedObject (zeroLocalizedObject
        (fromPairObj (⟨F.obj a.of.1.of, F.obj a.of.2.of⟩ : SInverseS.Pair D))) =
      (inclusion (Core D) (ExtensionCategory D × Core D)).obj
        ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1,
          F.core.obj a.of.2) :=
  actualTargetPairObject F a

private theorem actualSourceNumeratorDomain
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    ExtensionCategory.leftSumObj
        (ExtensionCategory.stabilizedFunctorRawMap F
          (localizedRawMap (zeroLocalizedRawMap r))).stabilizer
        (ExtensionCategory.stabilizedFunctorObject F
          (localizedObject (zeroLocalizedObject a))).of.1 =
      ExtensionCategory.leftSumObj (F.core.obj r.stabilizer)
        ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
          ExtensionCategory.mapFunctor F).obj a.of.1) :=
  congrArg₂ ExtensionCategory.leftSumObj
    (completedZeroRaw_stabilizer_values F r).1 (actualSourceNumeratorObject F a)

omit [ExactCategory C] [F.IsExact] in
private theorem actualTargetNumeratorDomain
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    ExtensionCategory.leftSumObj
        (localizedRawMap (zeroLocalizedRawMap
          (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).stabilizer
        (localizedObject (zeroLocalizedObject
          (fromPairObj (⟨F.obj a.of.1.of, F.obj a.of.2.of⟩ : SInverseS.Pair D)))).of.1 =
      ExtensionCategory.leftSumObj (F.core.obj r.stabilizer)
        ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1) := by
  apply congrArg₂ ExtensionCategory.leftSumObj
  · rw [localizedRawMap_stabilizer]
    rfl
  · exact actualTargetNumeratorObject F a

private def actualSourceNumeratorComputed
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    ExtensionCategory.leftSumObj (F.core.obj r.stabilizer)
        ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
          ExtensionCategory.mapFunctor F).obj a.of.1) ⟶
      (zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
        ExtensionCategory.mapFunctor F).obj b.of.1 :=
  eqToHom (actualSourceNumeratorDomain F r).symm ≫
    (ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))).hom.1 ≫
    eqToHom (actualSourceNumeratorObject F b)

/-- The original stabilized numerator at its proved ordinary zero-row image endpoints. -/
public def completedZeroSourceNumerator
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    ExtensionCategory.leftSumObj (F.core.obj r.stabilizer)
        ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
          ExtensionCategory.mapFunctor F).obj a.of.1) ⟶
      (zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
        ExtensionCategory.mapFunctor F).obj b.of.1 :=
  actualSourceNumeratorComputed F r

omit [ExactCategory C] [F.IsExact] in
private def actualTargetNumeratorComputed
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    ExtensionCategory.leftSumObj (F.core.obj r.stabilizer)
        ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1) ⟶
      (F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj b.of.1 :=
  eqToHom (actualTargetNumeratorDomain F r).symm ≫
    (localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).hom.1 ≫
    eqToHom (actualTargetNumeratorObject F b)

omit [ExactCategory C] [F.IsExact] in
/-- The original mapped-Core numerator at its proved ordinary target zero-row endpoints. -/
public def completedZeroTargetNumerator
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    ExtensionCategory.leftSumObj (F.core.obj r.stabilizer)
        ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1) ⟶
      (F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj b.of.1 :=
  actualTargetNumeratorComputed F r

private theorem actualSourceNumeratorValue
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (completedZeroSourceNumerator F r)
      (ExtensionCategory.stabilizedFunctorRawMap F
        (localizedRawMap (zeroLocalizedRawMap r))).hom.1 := by
  change HEq (eqToHom (actualSourceNumeratorDomain F r).symm ≫
    (ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))).hom.1 ≫
    eqToHom (actualSourceNumeratorObject F b)) _
  exact (eqToHom_comp_heq
    ((ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))).hom.1 ≫
        eqToHom (actualSourceNumeratorObject F b))
    (actualSourceNumeratorDomain F r).symm).trans
      (comp_eqToHom_heq _ (actualSourceNumeratorObject F b))

/-- Its whole arrow is the SAME original source numerator with proved endpoint casts. -/
public theorem completedZeroSourceNumerator_heq
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (completedZeroSourceNumerator F r)
      (ExtensionCategory.stabilizedFunctorRawMap F
        (localizedRawMap (zeroLocalizedRawMap r))).hom.1 :=
  actualSourceNumeratorValue F r

omit [ExactCategory C] [F.IsExact] in
private theorem actualTargetNumeratorValue
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (completedZeroTargetNumerator F r)
      (localizedRawMap (zeroLocalizedRawMap
        (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).hom.1 := by
  change HEq (eqToHom (actualTargetNumeratorDomain F r).symm ≫
    (localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).hom.1 ≫
    eqToHom (actualTargetNumeratorObject F b)) _
  exact (eqToHom_comp_heq
    ((localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).hom.1 ≫
        eqToHom (actualTargetNumeratorObject F b))
    (actualTargetNumeratorDomain F r).symm).trans
      (comp_eqToHom_heq _ (actualTargetNumeratorObject F b))

omit [ExactCategory C] [F.IsExact] in
/-- Its whole arrow is the SAME original target numerator with proved endpoint casts. -/
public theorem completedZeroTargetNumerator_heq
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (completedZeroTargetNumerator F r)
      (localizedRawMap (zeroLocalizedRawMap
        (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).hom.1 :=
  actualTargetNumeratorValue F r

private theorem actualSourceMiddleObject (A : Core C) :
    ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
      ExtensionCategory.mapFunctor F).obj A).row.X₂ = F.obj A.of :=
  (ExtensionCategory.mapFunctor_middle_obj F
    ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C)).obj A)).trans
      (congrArg F.obj (congrArg (fun E : ExtensionCategory C => E.row.X₂)
        (actualZeroGivenObject A)))

omit [ExactCategory C] [F.IsExact] [HasZeroObject C] [HasBinaryBiproducts C]
  [F.Additive] [Preadditive C] in
private theorem actualTargetMiddleObject (A : Core C) :
    ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj A).row.X₂ =
      F.obj A.of :=
  congrArg (fun E : ExtensionCategory D => E.row.X₂)
    (actualZeroGivenObject (C := D) (F.core.obj A))

private theorem actualSourceNumeratorMiddle
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.homNormalization (completedZeroSourceNumerator F r)).hom.2.hom
      ((F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom) :=
  (ExtensionCategory.homNormalization_middle_heq_of_objects_eq
    (actualSourceNumeratorDomain F r).symm (actualSourceNumeratorObject F b).symm
    (completedZeroSourceNumerator_heq F r)).trans
      (completedZeroSourceRaw_middle_heq F r)

omit [ExactCategory C] [F.IsExact] in
private theorem actualTargetNumeratorMiddle
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.homNormalization (completedZeroTargetNumerator F r)).hom.2.hom
      ((F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom) :=
  (ExtensionCategory.homNormalization_middle_heq_of_objects_eq
    (actualTargetNumeratorDomain F r).symm (actualTargetNumeratorObject F b).symm
    (completedZeroTargetNumerator_heq F r)).trans
      (heq_of_eq (completedZeroTargetRaw_middle F r))

private theorem actualOrdinaryMiddleComp
    {A B Z : ExtensionCategory D} (a : A ⟶ B) (b : B ⟶ Z) :
    (ExtensionCategory.homNormalization (a ≫ b)).hom.2.hom =
      (ExtensionCategory.homNormalization a).hom.2.hom ≫
        (ExtensionCategory.homNormalization b).hom.2.hom :=
  congrArg (fun k : A.subdivisionObj ⟶ Z.subdivisionObj => k.hom.2.hom)
    (ExtensionCategory.homNormalization_comp a b)

private theorem actualNumeratorIntertwining
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    completedZeroSourceNumerator F r ≫ (zeroRowIdentityCoordinateIso F b.of.1).hom =
      ExtensionCategory.leftSumMap (𝟙 (F.core.obj r.stabilizer))
        (zeroRowIdentityCoordinateIso F a.of.1).hom ≫ completedZeroTargetNumerator F r := by
  let L := zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
    ExtensionCategory.mapFunctor F
  let R := F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)
  let T := F.core.obj r.stabilizer
  let c (A : Core C) : L.obj A ≅ R.obj A := zeroRowIdentityCoordinateIso F A
  let s := completedZeroSourceNumerator F r
  let t := completedZeroTargetNumerator F r
  let h := ExtensionCategory.leftSumMap (𝟙 T) (c a.of.1).hom
  have hT : T.of = F.obj r.stabilizer.of := rfl
  have hL : (ExtensionCategory.leftSumObj T (L.obj a.of.1)).row.X₂ =
      (F.obj r.stabilizer.of ⊞ F.obj a.of.1.of) :=
    congrArg₂ (fun (U V : D) => U ⊞ V) hT (actualSourceMiddleObject F a.of.1)
  have hR : (ExtensionCategory.leftSumObj T (R.obj a.of.1)).row.X₂ =
      (F.obj r.stabilizer.of ⊞ F.obj a.of.1.of) :=
    congrArg₂ (fun (U V : D) => U ⊞ V) hT (actualTargetMiddleObject F a.of.1)
  have hBinary : HEq
      (biprod.map (𝟙 T.of) (ExtensionCategory.homNormalization (c a.of.1).hom).hom.2.hom)
      (biprod.map (𝟙 (F.obj r.stabilizer.of)) (𝟙 (F.obj a.of.1.of))) :=
    actualBinaryMapHEq hT (actualSourceMiddleObject F a.of.1) hT
      (actualTargetMiddleObject F a.of.1) (heq_of_eq rfl)
      (zeroRowIdentityCoordinateIso_middle_heq F a.of.1)
  have hId : biprod.map (𝟙 (F.obj r.stabilizer.of)) (𝟙 (F.obj a.of.1.of)) =
      𝟙 (F.obj r.stabilizer.of ⊞ F.obj a.of.1.of) := by
    apply biprod.hom_ext <;> simp
  have hAction : HEq (ExtensionCategory.homNormalization h).hom.2.hom
      (𝟙 (F.obj r.stabilizer.of ⊞ F.obj a.of.1.of)) :=
    (heq_of_eq (ExtensionCategory.leftSumMap_beta (𝟙 T) (c a.of.1).hom)).trans
      (hBinary.trans (heq_of_eq hId))
  have hLeft := heq_comp hL (actualSourceMiddleObject F b.of.1)
    (actualTargetMiddleObject F b.of.1) (actualSourceNumeratorMiddle F r)
    (zeroRowIdentityCoordinateIso_middle_heq F b.of.1)
  have hRight := heq_comp hL hR (actualTargetMiddleObject F b.of.1)
    hAction (actualTargetNumeratorMiddle F r)
  have hMiddle :
      (ExtensionCategory.homNormalization (s ≫ (c b.of.1).hom)).hom.2.hom =
      (ExtensionCategory.homNormalization (h ≫ t)).hom.2.hom :=
    eq_of_heq ((heq_of_eq (actualOrdinaryMiddleComp s (c b.of.1).hom)).trans
      (hLeft.trans ((heq_of_eq (Category.comp_id
        ((F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom))).trans
          ((heq_of_eq (Category.id_comp
            ((F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom))).symm.trans
              (hRight.symm.trans (heq_of_eq (actualOrdinaryMiddleComp h t).symm))))))
  exact ExtensionCategory.hom_ext_of_middle _ _ hMiddle

/-- The actual original zero-row component intertwines EVERY ordinary mapped raw numerator. -/
public theorem completedZeroRaw_numerator_naturality
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    completedZeroSourceNumerator F r ≫ (zeroRowIdentityCoordinateIso F b.of.1).hom =
      ExtensionCategory.leftSumMap (𝟙 (F.core.obj r.stabilizer))
        (zeroRowIdentityCoordinateIso F a.of.1).hom ≫ completedZeroTargetNumerator F r :=
  actualNumeratorIntertwining F r

end AlgebraicKTheory.FixedTargetExtension

end
