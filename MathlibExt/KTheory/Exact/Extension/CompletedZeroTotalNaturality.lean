/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroRawNumeratorNaturality
public import MathlibExt.CategoryTheory.Monoidal.ActionLocalizationOrdinaryNaturality

/-!
# Actual total-category naturality of the original completed-zero components

Every actual raw representative retains its original mapped stabilizer and
both coordinates. The proved ordinary numerator square and same denominator
square descend through the original action localization. The resulting
NatIso has precisely the original completedZeroTotalSourceComponent at every
pair, with both directions; no source square or coherence is a premise.
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

universe uC vC uD vD uA vA uB vB

namespace AlgebraicKTheory.FixedTargetExtension

private theorem actualFunctorMapHEq
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (G : A ⥤ B) {a b a' b' : A} (ha : a = a') (hb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) : HEq (G.map f) (G.map g) := by
  cases ha
  cases hb
  cases h
  exact HEq.rfl

private theorem actualRawHEqOfCoordinates
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {a b a' b' : SInverse (Core D) (ExtensionCategory D)}
    (ha : a = a') (hb : b = b') {r : RawHom a b} {s : RawHom a' b'}
    (hT : r.stabilizer = s.stabilizer)
    (h₁ : HEq r.hom.1 s.hom.1) (h₂ : HEq r.hom.2 s.hom.2) : HEq r s := by
  cases ha
  cases hb
  rcases r with ⟨T, f⟩
  rcases s with ⟨U, g⟩
  cases hT
  have hf : f = g := Prod.ext (eq_of_heq h₁) (eq_of_heq h₂)
  cases hf
  exact HEq.rfl

private theorem actualRawMkHEq
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {a b a' b' : SInverse (Core D) (ExtensionCategory D)}
    (ha : a = a') (hb : b = b') {r : RawHom a b} {s : RawHom a' b'}
    (h : HEq r s) : HEq (MonoidalActionCategory.Hom.mk r) (MonoidalActionCategory.Hom.mk s) := by
  cases ha
  cases hb
  cases h
  exact HEq.rfl

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private def actualSourcePair (a : SInverse (Core C) (Core C)) :
    ExtensionCategory D × Core D :=
  ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
    ExtensionCategory.mapFunctor F).obj a.of.1, F.core.obj a.of.2)

omit [ExactCategory C] [F.IsExact] in
private def actualTargetPair (a : SInverse (Core C) (Core C)) :
    ExtensionCategory D × Core D :=
  ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1,
    F.core.obj a.of.2)

omit [ExactCategory C] [ExactCategory D] [F.IsExact] in
private def actualMappedDenominator
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (F.core.obj r.stabilizer ⊗ F.core.obj a.of.2) ⟶ F.core.obj b.of.2 :=
  ⟨(F.mapBiprod r.stabilizer.of a.of.2.of).symm ≪≫ F.mapIso r.hom.2.iso⟩

private def actualNormalizedSourceRaw
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    RawHom ((inclusion (Core D) (ExtensionCategory D × Core D)).obj (actualSourcePair F a))
      ((inclusion (Core D) (ExtensionCategory D × Core D)).obj (actualSourcePair F b)) where
  stabilizer := F.core.obj r.stabilizer
  hom := (completedZeroSourceNumerator F r, actualMappedDenominator F r)

omit [ExactCategory C] [F.IsExact] in
private def actualNormalizedTargetRaw
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    RawHom ((inclusion (Core D) (ExtensionCategory D × Core D)).obj (actualTargetPair F a))
      ((inclusion (Core D) (ExtensionCategory D × Core D)).obj (actualTargetPair F b)) where
  stabilizer := F.core.obj r.stabilizer
  hom := (completedZeroTargetNumerator F r, actualMappedDenominator F r)

private theorem actualSourceDenominatorValue
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))).hom.2 (actualMappedDenominator F r) :=
  (ExtensionCategory.stabilizedFunctorRawMap_components F
    (localizedRawMap (zeroLocalizedRawMap r))).2.2.trans (by apply heq_of_eq; rfl)

omit [ExactCategory C] [F.IsExact] in
private theorem actualTargetDenominatorValue
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).hom.2
      (actualMappedDenominator F r) := by
  let q := fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))
  have h : (localizedRawMap (zeroLocalizedRawMap q)).hom.2.iso =
      (F.mapBiprod r.stabilizer.of a.of.2.of).symm ≪≫ F.mapIso r.hom.2.iso := by
    rw [localizedRawMap_denominator]
    change q.hom.2.iso = _
    rw [fromPairRaw_denominator]
    rfl
  apply heq_of_eq
  apply Core.hom_ext
  exact congrArg Iso.hom h

private theorem actualSourceRawValue
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))) (actualNormalizedSourceRaw F r) :=
  actualRawHEqOfCoordinates
    (completedZeroSourceRawObject_value F a) (completedZeroSourceRawObject_value F b)
    (completedZeroRaw_stabilizer_values F r).1
    (completedZeroSourceNumerator_heq F r).symm (actualSourceDenominatorValue F r)

omit [ExactCategory C] [F.IsExact] in
private theorem actualTargetRawValue
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))) (actualNormalizedTargetRaw F r) := by
  have hT : (localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).stabilizer =
      F.core.obj r.stabilizer := by
    rw [localizedRawMap_stabilizer]
    rfl
  exact actualRawHEqOfCoordinates
    (completedZeroTargetRawObject_value F a) (completedZeroTargetRawObject_value F b) hT
    (completedZeroTargetNumerator_heq F r).symm (actualTargetDenominatorValue F r)

private theorem actualLeftObjectValue (a : SInverse (Core C) (Core C)) :
    (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
      ExtensionCategory.stabilizedFunctorMap F).obj a =
      (inclusion (Core D) (ExtensionCategory D × Core D)).obj (actualSourcePair F a) :=
  (ExtensionCategory.stabilizedFunctorMap_obj F (localizedObject (zeroLocalizedObject a))).trans
    (completedZeroSourceRawObject_value F a)

omit [ExactCategory C] [F.IsExact] in
private theorem actualRightObjectValue (a : SInverse (Core C) (Core C)) :
    (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)).obj a =
      (inclusion (Core D) (ExtensionCategory D × Core D)).obj (actualTargetPair F a) :=
  (congrArg (fun x : SInverse (Core D) (Core D) =>
    (zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)).obj x)
      (completedCoreFunctor_obj F a)).trans (completedZeroTargetRawObject_value F a)

private theorem actualLeftMapValue
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq ((zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
      ExtensionCategory.stabilizedFunctorMap F).map (MonoidalActionCategory.Hom.mk r))
      (MonoidalActionCategory.Hom.mk (actualNormalizedSourceRaw F r)) := by
  have hPrefix : (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C)).map
      (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (localizedRawMap (zeroLocalizedRawMap r)) := by
    change (localizedForget (0 : C)).map (zeroLocalizedHomMap (MonoidalActionCategory.Hom.mk r)) = _
    rw [zeroLocalizedHomMap_mk, localizedForget_map_mk]
  have hMap : HEq ((ExtensionCategory.stabilizedFunctorMap F).map
      ((zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C)).map (MonoidalActionCategory.Hom.mk
          r)))
      (MonoidalActionCategory.Hom.mk (ExtensionCategory.stabilizedFunctorRawMap F
        (localizedRawMap (zeroLocalizedRawMap r)))) :=
    (heq_of_eq (congrArg (ExtensionCategory.stabilizedFunctorMap F).map hPrefix)).trans
      (ExtensionCategory.stabilizedFunctorMap_mkHom_heq F
        (localizedRawMap (zeroLocalizedRawMap r)))
  exact hMap.trans (actualRawMkHEq
    (completedZeroSourceRawObject_value F a) (completedZeroSourceRawObject_value F b)
    (actualSourceRawValue F r))

omit [ExactCategory C] [F.IsExact] in
private theorem actualRightMapValue
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq ((completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙
      localizedForget (0 : D)).map (MonoidalActionCategory.Hom.mk r))
      (MonoidalActionCategory.Hom.mk (actualNormalizedTargetRaw F r)) := by
  let G := zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)
  let q := fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))
  have hMapped := actualFunctorMapHEq G (completedCoreFunctor_obj F a)
    (completedCoreFunctor_obj F b) (completedCoreFunctor_mkHom_heq F r)
  have hPrefix : G.map (MonoidalActionCategory.Hom.mk q) = MonoidalActionCategory.Hom.mk
      (localizedRawMap (zeroLocalizedRawMap q)) := by
    change (localizedForget (0 : D)).map (zeroLocalizedHomMap (MonoidalActionCategory.Hom.mk q)) = _
    rw [zeroLocalizedHomMap_mk, localizedForget_map_mk]
  exact hMapped.trans ((heq_of_eq hPrefix).trans (actualRawMkHEq
    (completedZeroTargetRawObject_value F a) (completedZeroTargetRawObject_value F b)
    (actualTargetRawValue F r)))

private theorem actualNormalizedRawSquare
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    MonoidalActionCategory.Hom.mk (actualNormalizedSourceRaw F r) ≫
        (inclusion (Core D) (ExtensionCategory D × Core D)).map
          (completedZeroOrdinarySourceComponent F b).hom =
      (inclusion (Core D) (ExtensionCategory D × Core D)).map
          (completedZeroOrdinarySourceComponent F a).hom ≫
        MonoidalActionCategory.Hom.mk (actualNormalizedTargetRaw F r) := by
  let T := F.core.obj r.stabilizer
  let f : T ⊙ₗ actualSourcePair F a ⟶ actualSourcePair F b :=
    (completedZeroSourceNumerator F r, actualMappedDenominator F r)
  let g : T ⊙ₗ actualTargetPair F a ⟶ actualTargetPair F b :=
    (completedZeroTargetNumerator F r, actualMappedDenominator F r)
  have hOrdinary : f ≫ (completedZeroOrdinarySourceComponent F b).hom =
      (T ⊴ₗ (completedZeroOrdinarySourceComponent F a).hom) ≫ g := by
    apply Prod.ext
    · have ha : (completedZeroOrdinarySourceComponent F a).hom.1 =
          (zeroRowIdentityCoordinateIso F a.of.1).hom :=
        congrArg (fun e => e.hom.1) (completedZeroOrdinarySourceComponent_value F a)
      have hb : (completedZeroOrdinarySourceComponent F b).hom.1 =
          (zeroRowIdentityCoordinateIso F b.of.1).hom :=
        congrArg (fun e => e.hom.1) (completedZeroOrdinarySourceComponent_value F b)
      change completedZeroSourceNumerator F r ≫ (completedZeroOrdinarySourceComponent F b).hom.1 =
        ExtensionCategory.leftSumMap (𝟙 T) (completedZeroOrdinarySourceComponent F a).hom.1 ≫
          completedZeroTargetNumerator F r
      rw [ha, hb]
      exact completedZeroRaw_numerator_naturality F r
    · change actualMappedDenominator F r ≫ (completedZeroOrdinarySourceComponent F b).hom.2 =
        (T ◁ (completedZeroOrdinarySourceComponent F a).hom.2) ≫ actualMappedDenominator F r
      rw [completedZeroOrdinarySourceComponent_hom_denominator,
        completedZeroOrdinarySourceComponent_hom_denominator,
        MonoidalCategory.whiskerLeft_id, Category.comp_id, Category.id_comp]
  have hRaw := congrArg
    (fun k : T ⊙ₗ actualSourcePair F a ⟶ actualTargetPair F b =>
      MonoidalActionCategory.Hom.mk
        (⟨T, k⟩ : RawHom
          (⟨actualSourcePair F a⟩ :
            MonoidalActionCategory (Core D) (ExtensionCategory D × Core D))
          ⟨actualTargetPair F b⟩)) hOrdinary
  exact (hom_mk_postcompose_ordinary (S := Core D) (X := ExtensionCategory D × Core D)
    T f (completedZeroOrdinarySourceComponent F b).hom).trans
      (hRaw.trans (ordinary_precompose_hom_mk (S := Core D)
        (X := ExtensionCategory D × Core D)
        T (completedZeroOrdinarySourceComponent F a).hom g).symm)

private theorem actualTotalRawSquare
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.stabilizedFunctorMap F).map (MonoidalActionCategory.Hom.mk r) ≫
        (completedZeroTotalSourceComponent F b).hom =
      (completedZeroTotalSourceComponent F a).hom ≫
        (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙
          localizedForget (0 : D)).map (MonoidalActionCategory.Hom.mk r) := by
  have hLeft := heq_comp (actualLeftObjectValue F a) (actualLeftObjectValue F b)
    (actualRightObjectValue F b) (actualLeftMapValue F r)
    (completedZeroTotalSourceComponent_hom_heq F b)
  have hRight := heq_comp (actualLeftObjectValue F a) (actualRightObjectValue F a)
    (actualRightObjectValue F b) (completedZeroTotalSourceComponent_hom_heq F a)
    (actualRightMapValue F r)
  exact eq_of_heq (hLeft.trans ((heq_of_eq (actualNormalizedRawSquare F r)).trans hRight.symm))

private def actualCompletedZeroTotalNatIsoComputed :
    (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
      ExtensionCategory.stabilizedFunctorMap F) ≅
    (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)) := by
  refine NatIso.ofComponents (completedZeroTotalSourceComponent F) ?_
  intro a b f
  refine Quotient.inductionOn f ?_
  intro r
  exact actualTotalRawSquare F r

/-- The original completed-zero total components are natural on EVERY localized morphism. -/
public def completedZeroTotalNaturalityIso :
    (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
      ExtensionCategory.stabilizedFunctorMap F) ≅
    (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)) :=
  actualCompletedZeroTotalNatIsoComputed F

private theorem actualTotalNatIsoComponentValue (a : SInverse (Core C) (Core C)) :
    (completedZeroTotalNaturalityIso F).app a = completedZeroTotalSourceComponent F a := rfl

/-- Each whole component is EXACTLY the original source component, with both Iso directions. -/
public theorem completedZeroTotalNaturalityIso_app (a : SInverse (Core C) (Core C)) :
    (completedZeroTotalNaturalityIso F).app a = completedZeroTotalSourceComponent F a :=
  actualTotalNatIsoComponentValue F a

private theorem actualTotalHomNaturality
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.stabilizedFunctorMap F).map f ≫
        (completedZeroTotalSourceComponent F b).hom =
      (completedZeroTotalSourceComponent F a).hom ≫
        (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙
          localizedForget (0 : D)).map f :=
  (actualCompletedZeroTotalNatIsoComputed F).hom.naturality f

/-- The actual forward total-source square holds on every original localized arrow. -/
public theorem completedZeroTotalNaturalityIso_hom_naturality
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.stabilizedFunctorMap F).map f ≫
        (completedZeroTotalSourceComponent F b).hom =
      (completedZeroTotalSourceComponent F a).hom ≫
        (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙
          localizedForget (0 : D)).map f :=
  actualTotalHomNaturality F f

private theorem actualTotalInvNaturality
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙
        localizedForget (0 : D)).map f ≫ (completedZeroTotalSourceComponent F b).inv =
      (completedZeroTotalSourceComponent F a).inv ≫
        (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
          ExtensionCategory.stabilizedFunctorMap F).map f :=
  (actualCompletedZeroTotalNatIsoComputed F).inv.naturality f

/-- The SAME inverse components satisfy the reverse total-source square on every arrow. -/
public theorem completedZeroTotalNaturalityIso_inv_naturality
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙
        localizedForget (0 : D)).map f ≫ (completedZeroTotalSourceComponent F b).inv =
      (completedZeroTotalSourceComponent F a).inv ≫
        (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
          ExtensionCategory.stabilizedFunctorMap F).map f :=
  actualTotalInvNaturality F f

end AlgebraicKTheory.FixedTargetExtension

end
