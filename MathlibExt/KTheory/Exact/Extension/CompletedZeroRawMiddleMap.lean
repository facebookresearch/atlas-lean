/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroSourceComponent
public import MathlibExt.CategoryTheory.Preadditive.MapBiprodNaturality
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The original completed-zero raw middle maps under an exact functor

The actual mapped stabilized extension numerator and the actual mapped
completed-Core numerator have the same middle map. Both use the original
stabilizer and the canonical inverse mapBiprod followed by F.map. This
calculation applies to every original raw representative and imposes no
restriction on its denominator. The inverse middle comparison uses the
existing normalization Iso inverse calculation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts
attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalRawMiddleComposite
    {A B Z : ExtensionCategory D} (a : A ⟶ B) (b : B ⟶ Z) :
    (homNormalization (a ≫ b)).hom.2.hom =
      (homNormalization a).hom.2.hom ≫ (homNormalization b).hom.2.hom :=
  congrArg (fun k : A.subdivisionObj ⟶ Z.subdivisionObj => k.hom.2.hom)
    (homNormalization_comp a b)

private theorem originalImageSumMiddle (F : C ⥤ D) [F.Additive] [F.IsExact]
    (T : Core C) (E : ExtensionCategory C) :
    (leftSumObj (F.core.obj T) ((mapFunctor F).obj E)).row.X₂ =
      (F.obj T.of ⊞ F.obj E.row.X₂) := by
  have h : (leftSumObj (F.core.obj T) ((mapFunctor F).obj E)).row.X₂ =
      ((F.core.obj T).of ⊞ ((mapFunctor F).obj E).row.X₂) := rfl
  exact h.trans (congrArg₂ (fun (X Y : D) => X ⊞ Y)
    (show (F.core.obj T).of = F.obj T.of from rfl) (mapFunctor_middle_obj F E))

private theorem originalMappedSumMiddle (F : C ⥤ D) [F.Additive] [F.IsExact]
    (T : Core C) (E : ExtensionCategory C) :
    ((mapFunctor F).obj (leftSumObj T E)).row.X₂ = F.obj (T.of ⊞ E.row.X₂) :=
  (mapFunctor_middle_obj F (leftSumObj T E)).trans (by rfl)

private theorem originalMappedSumInverseMiddle (T : Core C) (E : ExtensionCategory C) :
    HEq (homNormalization ((mapLeftSumNaturalityIso F).app (T, E)).inv).hom.2.hom
      (F.mapBiprod T.of E.row.X₂).inv := by
  let A := (mapFunctor F).obj (leftSumObj T E)
  let B := leftSumObj (F.core.obj T) ((mapFunctor F).obj E)
  let e : A ≅ B := (mapLeftSumNaturalityIso F).app (T, E)
  let c := F.mapBiprod T.of E.row.X₂
  let hs : A.row.X₂ = F.obj (T.of ⊞ E.row.X₂) := originalMappedSumMiddle F T E
  let ht : B.row.X₂ = (F.obj T.of ⊞ F.obj E.row.X₂) := originalImageSumMiddle F T E
  let b : A.row.X₂ ≅ B.row.X₂ := eqToIso hs ≪≫ c ≪≫ (eqToIso ht).symm
  have hHom : HEq b.hom c.hom := by
    change HEq (eqToHom hs ≫ c.hom ≫ eqToHom ht.symm) c.hom
    exact (eqToHom_comp_heq (c.hom ≫ eqToHom ht.symm) hs).trans
      (comp_eqToHom_heq c.hom ht.symm)
  have hActual : (homNormalization e.hom).hom.2.hom = b.hom :=
    eq_of_heq ((mapLeftSumNaturalityIso_app_middle_hom_heq F T E).trans hHom.symm)
  have hInverse : (homNormalization e.inv).hom.2.hom = b.inv :=
    homNormalization_iso_inv_middle e b hActual
  have hInv : HEq b.inv c.inv := by
    dsimp only [b]
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
    change HEq (eqToHom ht ≫ c.inv ≫ eqToHom hs.symm) c.inv
    exact (eqToHom_comp_heq (c.inv ≫ eqToHom hs.symm) ht).trans
      (comp_eqToHom_heq c.inv hs.symm)
  exact (heq_of_eq hInverse).trans hInv

/-- The actual inverse action comparison has the inverse canonical mapBiprod middle map. -/
public theorem mapLeftSumNaturalityIso_app_middle_inv_heq
    (T : Core C) (E : ExtensionCategory C) :
    HEq (homNormalization ((mapLeftSumNaturalityIso F).app (T, E)).inv).hom.2.hom
      (F.mapBiprod T.of E.row.X₂).inv :=
  originalMappedSumInverseMiddle F T E

private theorem originalMappedStabilizedMiddleComputed
    {a b : SInverse (Core C) (ExtensionCategory C)} (r : RawHom a b) :
    HEq (homNormalization (stabilizedFunctorRawMap F r).hom.1).hom.2.hom
      ((F.mapBiprod r.stabilizer.of a.of.1.row.X₂).inv ≫
        F.map (homNormalization r.hom.1).hom.2.hom) := by
  let G := mapFunctor F
  let U := stabilizedFunctorObject F a
  let V := stabilizedFunctorObject F b
  let q := stabilizedFunctorRawMap F r
  let A := leftSumObj (F.core.obj r.stabilizer) (G.obj a.of.1)
  let B := G.obj (leftSumObj r.stabilizer a.of.1)
  let Z := G.obj b.of.1
  let e : B ≅ A := (mapLeftSumNaturalityIso F).app (r.stabilizer, a.of.1)
  let g : B ⟶ Z := G.map r.hom.1
  have hA : (q.stabilizer ⊙ₗ U.of).1 = A :=
    congrArg₂ (fun (T : Core D) (p : ExtensionCategory D × Core D) => (T ⊙ₗ p).1)
      (stabilizedFunctorRawMap_components F r).1 (stabilizedFunctorObject_of F a)
  have hZ : V.of.1 = Z := congrArg Prod.fst (stabilizedFunctorObject_of F b)
  have hRecipe : HEq q.hom.1 (e.inv ≫ g) := (stabilizedFunctorRawMap_components F r).2.1
  have hRaw : HEq (homNormalization q.hom.1).hom.2.hom
      (homNormalization (e.inv ≫ g)).hom.2.hom :=
    homNormalization_middle_heq_of_objects_eq hA hZ hRecipe
  have hDom : A.row.X₂ = (F.obj r.stabilizer.of ⊞ F.obj a.of.1.row.X₂) :=
    originalImageSumMiddle F r.stabilizer a.of.1
  have hMid : B.row.X₂ = F.obj (r.stabilizer.of ⊞ a.of.1.row.X₂) :=
    originalMappedSumMiddle F r.stabilizer a.of.1
  have hCod : Z.row.X₂ = F.obj b.of.1.row.X₂ := mapFunctor_middle_obj F b.of.1
  have hProduct := heq_comp hDom hMid hCod
    (mapLeftSumNaturalityIso_app_middle_inv_heq F r.stabilizer a.of.1)
    (mapFunctor_middle_heq F r.hom.1)
  exact hRaw.trans ((heq_of_eq (originalRawMiddleComposite e.inv g)).trans hProduct)

/-- Every original stabilized numerator retains its literal canonical image middle map. -/
public theorem stabilizedFunctorRawMap_middle_heq
    {a b : SInverse (Core C) (ExtensionCategory C)} (r : RawHom a b) :
    HEq (homNormalization (stabilizedFunctorRawMap F r).hom.1).hom.2.hom
      ((F.mapBiprod r.stabilizer.of a.of.1.row.X₂).inv ≫
        F.map (homNormalization r.hom.1).hom.2.hom) :=
  originalMappedStabilizedMiddleComputed F r

end AlgebraicKTheory.ExtensionCategory

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalCompletedZeroSourceRawMiddleComputed
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.homNormalization
      (ExtensionCategory.stabilizedFunctorRawMap F
        (localizedRawMap (zeroLocalizedRawMap r))).hom.1).hom.2.hom
      ((F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom) := by
  let q := localizedRawMap (zeroLocalizedRawMap r)
  have h := ExtensionCategory.stabilizedFunctorRawMap_middle_heq F q
  have hMiddle : (ExtensionCategory.homNormalization q.hom.1).hom.2.hom =
      r.hom.1.iso.hom :=
    (localizedRawMap_beta (zeroLocalizedRawMap r)).trans (by rfl)
  change HEq (ExtensionCategory.homNormalization
      (ExtensionCategory.stabilizedFunctorRawMap F q).hom.1).hom.2.hom
    ((F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫
      F.map (ExtensionCategory.homNormalization q.hom.1).hom.2.hom) at h
  exact h.trans (heq_of_eq (congrArg
    (fun k : r.stabilizer.of ⊞ a.of.1.of ⟶ b.of.1.of =>
      (F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map k) hMiddle))

/-- The original stabilized zero-row numerator has the canonical completed-Core middle image. -/
public theorem completedZeroSourceRaw_middle_heq
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.homNormalization
      (ExtensionCategory.stabilizedFunctorRawMap F
        (localizedRawMap (zeroLocalizedRawMap r))).hom.1).hom.2.hom
      ((F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom) :=
  originalCompletedZeroSourceRawMiddleComputed F r

omit [ExactCategory C] [F.IsExact] in
private theorem originalCompletedZeroTargetRawMiddleComputed
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (ExtensionCategory.homNormalization (localizedRawMap (zeroLocalizedRawMap
      (CategoryTheory.CoreLocalizationComparison.fromPairRaw
        (CategoryTheory.SInverseS.mapRawHom F
          (CategoryTheory.CoreLocalizationComparison.toPairRaw r))))).hom.1).hom.2.hom =
      (F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom := by
  let c := CategoryTheory.CoreLocalizationComparison.toPairRaw r
  let d := CategoryTheory.SInverseS.mapRawHom F c
  let q := CategoryTheory.CoreLocalizationComparison.fromPairRaw d
  have hGiven : q.hom.1.iso = d.hom₁ := rfl
  have hImage := (CategoryTheory.SInverseS.pairFunctor_characteristic
    F F (Iso.refl F) (𝟭 D)).2.2.2.1 c
  have hActual : q.hom.1.iso.hom =
      (F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom :=
    (congrArg Iso.hom (hGiven.trans hImage)).trans (by rfl)
  exact (localizedRawMap_beta (zeroLocalizedRawMap q)).trans
    ((show (zeroLocalizedRawMap q).hom.1.b.hom = q.hom.1.iso.hom from rfl).trans hActual)

omit [ExactCategory C] [F.IsExact] in
/-- The target completed-Core route has that same actual middle map on every raw representative. -/
public theorem completedZeroTargetRaw_middle
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (ExtensionCategory.homNormalization (localizedRawMap (zeroLocalizedRawMap
      (CategoryTheory.CoreLocalizationComparison.fromPairRaw
        (CategoryTheory.SInverseS.mapRawHom F
          (CategoryTheory.CoreLocalizationComparison.toPairRaw r))))).hom.1).hom.2.hom =
      (F.mapBiprod r.stabilizer.of a.of.1.of).inv ≫ F.map r.hom.1.iso.hom :=
  originalCompletedZeroTargetRawMiddleComputed F r

/-- The two genuine raw middle maps agree before any quotient naturality assertion. -/
public theorem completedZeroRaw_middle_agreement
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.homNormalization
      (ExtensionCategory.stabilizedFunctorRawMap F
        (localizedRawMap (zeroLocalizedRawMap r))).hom.1).hom.2.hom
      (ExtensionCategory.homNormalization (localizedRawMap (zeroLocalizedRawMap
        (CategoryTheory.CoreLocalizationComparison.fromPairRaw
          (CategoryTheory.SInverseS.mapRawHom F
            (CategoryTheory.CoreLocalizationComparison.toPairRaw r))))).hom.1).hom.2.hom :=
  (completedZeroSourceRaw_middle_heq F r).trans
    (heq_of_eq (completedZeroTargetRaw_middle F r).symm)

end AlgebraicKTheory.FixedTargetExtension

end
