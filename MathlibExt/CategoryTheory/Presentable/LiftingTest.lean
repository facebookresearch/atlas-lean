/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.LiftingTest
public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation
public import MathlibExt.CategoryTheory.Presentable.Colimits
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Preservation of the original tagged lifting test

A fixed tagged coproduct preserves the colimits preserved by each component.
The proof uses its actual Sigma coproduct cocone. Working-size normalization
retains the full original functions, and its preservation follows from an
explicit natural isomorphism and native ULift reflection.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w s t uA vA uC vC uD vD uS vS

open CategoryTheory Limits TypeCat Opposite
open CategoryTheory.MorphismProperty.LiftingTest

namespace CategoryTheory.Presentable.LiftingTest

section FixedSums

variable {A : Type uA} [Category.{vA} A] {S : Type s} (F : S → A ⥤ Type t)

/-- The literal fixed tagged family of original component elements and maps. -/
def fixedSumFunctor : A ⥤ Type (max s t) where
  obj p := Σ k : S, (F k).obj p
  map a := ofHom (fun z => ⟨z.1, (F z.1).map a z.2⟩)
  map_id p := by
    apply ConcreteCategory.hom_ext
    rintro ⟨k, z⟩
    simp
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    rintro ⟨k, z⟩
    simp

/-- The entire original map retains its tag and applies the original component map. -/
theorem fixedSumFunctor_map_function {p q : A} (a : p ⟶ q) :
    (fixedSumFunctor F).map a = ofHom (fun z => ⟨z.1, (F z.1).map a z.2⟩) := rfl

/-- The actual Discrete family places each original component in the coproduct universe. -/
def fixedFamily : A ⥤ Discrete S ⥤ Type (max s t) where
  obj p := Discrete.functor (fun k : S => ULift.{s} ((F k).obj p))
  map a := Discrete.natTrans (fun k => uliftFunctor.{s, t}.map ((F k.as).map a))
  map_id p := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    rintro ⟨z⟩
    change ULift.up ((F k.as).map (𝟙 p) z) = ULift.up z
    simp
  map_comp a b := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    rintro ⟨z⟩
    change ULift.up ((F k.as).map (a ≫ b) z) =
      ULift.up ((F k.as).map b ((F k.as).map a z))
    simp

/-- The fixed coproduct equivalence removes exactly the component universe lifts. -/
def fixedSumEquiv (p : A) :
    (Σ k : S, ULift.{s} ((F k).obj p)) ≃ (Σ k : S, (F k).obj p) where
  toFun z := ⟨z.1, z.2.down⟩
  invFun z := ⟨z.1, ⟨z.2⟩⟩
  left_inv := by rintro ⟨k, ⟨z⟩⟩; rfl
  right_inv := by rintro ⟨k, z⟩; rfl

/-- The whole forward coproduct comparison preserves the original tag and value. -/
theorem fixedSumEquiv_function (p : A) :
    (fixedSumEquiv F p).toFun = fun z => (⟨z.1, z.2.down⟩ : Σ k : S, (F k).obj p) := rfl

/-- The whole inverse comparison retains the same original tag and component value. -/
theorem fixedSumEquiv_inverse_function (p : A) :
    (fixedSumEquiv F p).symm.toFun = fun z =>
      (⟨z.1, ⟨z.2⟩⟩ : Σ k : S, ULift.{s} ((F k).obj p)) := rfl

/-- The same fixed sum is the actual native coproduct, with both comparison functions. -/
def fixedSumColimitIso :
    fixedFamily F ⋙ (colim : (Discrete S ⥤ Type (max s t)) ⥤ _) ≅ fixedSumFunctor F :=
  NatIso.ofComponents
    (fun p => Types.coproductIso (fun k : S => ULift.{s} ((F k).obj p)) ≪≫
      (fixedSumEquiv F p).toIso)
    (by
      intro p q a
      apply colimit.hom_ext
      intro k
      simp only [Functor.comp_map, colimit.ι_map_assoc]
      change ofHom (fun z : ULift.{s} ((F k.as).obj p) =>
          (ULift.up ((F k.as).map a z.down) : ULift.{s} ((F k.as).obj q))) ≫
        ((Sigma.ι (fun j : S => ULift.{s} ((F j).obj q)) k.as ≫
          (Types.coproductIso (fun j : S => ULift.{s} ((F j).obj q))).hom) ≫
          (fixedSumEquiv F q).toIso.hom) =
        (Sigma.ι (fun j : S => ULift.{s} ((F j).obj p)) k.as ≫
          (Types.coproductIso (fun j : S => ULift.{s} ((F j).obj p))).hom) ≫
          (fixedSumEquiv F p).toIso.hom ≫ (fixedSumFunctor F).map a
      rw [Types.coproductIso_ι_comp_hom, Types.coproductIso_ι_comp_hom]
      apply ConcreteCategory.hom_ext
      intro z
      rfl)

/-- Each fixed component preserves the same given filtered colimit before taking its sum. -/
theorem fixedFamily_isCardinalAccessible (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ k, (F k).IsCardinalAccessible χ] :
    (fixedFamily F).IsCardinalAccessible χ := by
  refine ⟨fun J _ _ => ?_⟩
  apply preservesColimitsOfShape_of_evaluation
  intro k
  have := (F k.as).preservesColimitsOfShape_of_isCardinalAccessible χ J
  change PreservesColimitsOfShape J (F k.as ⋙ uliftFunctor.{s, t})
  infer_instance

/-- Fixed tagged coproducts preserve these colimits without a tag bound below the rank. -/
theorem fixedSumFunctor_isCardinalAccessible (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ k, (F k).IsCardinalAccessible χ] :
    (fixedSumFunctor F).IsCardinalAccessible χ := by
  let H : Discrete S ⥤ A ⥤ Type (max s t) := (fixedFamily F).flip
  let (k : Discrete S) : (H.obj k).IsCardinalAccessible χ := by
    change (F k.as ⋙ uliftFunctor.{s, t}).IsCardinalAccessible χ
    infer_instance
  let _ : (colimit H).IsCardinalAccessible χ :=
    Functor.isCardinalAccessible_colimit χ H
  exact Functor.isCardinalAccessible_of_natIso
    (colimitIsoFlipCompColim H ≪≫ fixedSumColimitIso F) χ

end FixedSums

section Shrink

variable {A : Type uA} [Category.{vA} A] (F : A ⥤ Type t)
  [FunctorToTypes.Small.{w} F]

/-- The full working-size normalization compares with the same original functor after ULift. -/
def shrinkUliftIso :
    FunctorToTypes.shrink.{w} F ⋙ uliftFunctor.{t, w} ≅
      F ⋙ uliftFunctor.{w, t} :=
  NatIso.ofComponents
    (fun p => ((Equiv.ulift.trans (equivShrink (F.obj p)).symm).trans Equiv.ulift.symm).toIso)
    (by
      intro p q a
      apply ConcreteCategory.hom_ext
      intro z
      change ULift.up ((equivShrink (F.obj q)).symm
        (equivShrink (F.obj q) (F.map a ((equivShrink (F.obj p)).symm z.down)))) =
          ULift.up (F.map a ((equivShrink (F.obj p)).symm z.down))
      rw [Equiv.symm_apply_apply])

/-- The entire forward comparison decodes the same original element. -/
theorem shrinkUliftIso_hom_function (p : A) :
    (shrinkUliftIso F).hom.app p =
      ofHom (fun z => ULift.up ((equivShrink (F.obj p)).symm z.down)) := rfl

/-- The entire inverse comparison encodes the same original element. -/
theorem shrinkUliftIso_inv_function (p : A) :
    (shrinkUliftIso F).inv.app p =
      ofHom (fun z => ULift.up (equivShrink (F.obj p) z.down)) := rfl

/-- Normalization preservation is derived from the actual maps and native ULift reflection. -/
theorem shrink_isCardinalAccessible (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [F.IsCardinalAccessible χ] :
    (FunctorToTypes.shrink.{w} F).IsCardinalAccessible χ := by
  refine ⟨fun J _ _ => ?_⟩
  have := F.preservesColimitsOfShape_of_isCardinalAccessible χ J
  let _ : PreservesColimitsOfShape J (F ⋙ uliftFunctor.{w, t}) := inferInstance
  let _ : PreservesColimitsOfShape J
      (FunctorToTypes.shrink.{w} F ⋙ uliftFunctor.{t, w}) :=
    preservesColimitsOfShape_of_natIso (shrinkUliftIso F).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{t, w}

end Shrink

section Normalization

variable {A : Type uA} [Category.{vA} A] (T : A ⥤ Arrow (Type t))
  [∀ p, Small.{w} (T.obj p).left] [∀ p, Small.{w} (T.obj p).right]

/-- The original source projection is working-small at every original object. -/
instance normalizedLeft_small : FunctorToTypes.Small.{w} (T ⋙ Arrow.leftFunc) := by
  intro p
  change Small.{w} (T.obj p).left
  infer_instance

/-- The original target projection is working-small at every original object. -/
instance normalizedRight_small : FunctorToTypes.Small.{w} (T ⋙ Arrow.rightFunc) := by
  intro p
  change Small.{w} (T.obj p).right
  infer_instance

/-- The SAME normalized Arrow functor has its complete original two-function comparison. -/
def normalizedUliftIso :
    normalizedFunctor.{w} T ⋙ Functor.mapArrow uliftFunctor.{t, w} ≅
      T ⋙ Functor.mapArrow uliftFunctor.{w, t} :=
  NatIso.ofComponents
    (fun p => Arrow.isoMk
      ((shrinkUliftIso.{w} (T ⋙ Arrow.leftFunc)).app p)
      ((shrinkUliftIso.{w} (T ⋙ Arrow.rightFunc)).app p) (by
        apply ConcreteCategory.hom_ext
        intro z
        change ULift.up ((T.obj p).hom ((equivShrink (T.obj p).left).symm z.down)) =
          ULift.up ((equivShrink (T.obj p).right).symm
            (equivShrink (T.obj p).right
              ((T.obj p).hom ((equivShrink (T.obj p).left).symm z.down))))
        rw [Equiv.symm_apply_apply]))
    (by
      intro p q a
      apply Arrow.hom_ext
      · exact (shrinkUliftIso.{w} (T ⋙ Arrow.leftFunc)).hom.naturality a
      · exact (shrinkUliftIso.{w} (T ⋙ Arrow.rightFunc)).hom.naturality a)

/-- The entire forward source comparison decodes the original source element. -/
theorem normalizedUliftIso_hom_left_function (p : A) :
    ((normalizedUliftIso T).hom.app p).left =
      ofHom (fun z => ULift.up ((equivShrink (T.obj p).left).symm z.down)) := rfl

/-- The entire forward target comparison decodes the original target element. -/
theorem normalizedUliftIso_hom_right_function (p : A) :
    ((normalizedUliftIso T).hom.app p).right =
      ofHom (fun z => ULift.up ((equivShrink (T.obj p).right).symm z.down)) := rfl

/-- The entire inverse source comparison retains the same original source element. -/
theorem normalizedUliftIso_inv_left_function (p : A) :
    ((normalizedUliftIso T).inv.app p).left =
      ofHom (fun z => ULift.up (equivShrink (T.obj p).left z.down)) := rfl

/-- The entire inverse target comparison retains the same original target element. -/
theorem normalizedUliftIso_inv_right_function (p : A) :
    ((normalizedUliftIso T).inv.app p).right =
      ofHom (fun z => ULift.up (equivShrink (T.obj p).right z.down)) := rfl

/-- The actual normalized source functor is the same native shrinking of the original source. -/
def normalizedLeftIso :
    normalizedFunctor.{w} T ⋙ Arrow.leftFunc ≅
      FunctorToTypes.shrink.{w} (T ⋙ Arrow.leftFunc) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The actual normalized target functor is the same native shrinking of the original target. -/
def normalizedRightIso :
    normalizedFunctor.{w} T ⋙ Arrow.rightFunc ≅
      FunctorToTypes.shrink.{w} (T ⋙ Arrow.rightFunc) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Preservation of both original projections gives preservation of the SAME normalized test. -/
theorem normalized_isCardinalAccessible (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [(T ⋙ Arrow.leftFunc).IsCardinalAccessible χ]
    [(T ⋙ Arrow.rightFunc).IsCardinalAccessible χ] :
    (normalizedFunctor.{w} T).IsCardinalAccessible χ := by
  let _ : (FunctorToTypes.shrink.{w} (T ⋙ Arrow.leftFunc)).IsCardinalAccessible χ :=
    shrink_isCardinalAccessible.{w} (T ⋙ Arrow.leftFunc) χ
  let _ : (FunctorToTypes.shrink.{w} (T ⋙ Arrow.rightFunc)).IsCardinalAccessible χ :=
    shrink_isCardinalAccessible.{w} (T ⋙ Arrow.rightFunc) χ
  let _ : (normalizedFunctor.{w} T ⋙ Arrow.leftFunc).IsCardinalAccessible χ :=
    Functor.isCardinalAccessible_of_natIso (normalizedLeftIso.{w} T).symm χ
  let _ : (normalizedFunctor.{w} T ⋙ Arrow.rightFunc).IsCardinalAccessible χ :=
    Functor.isCardinalAccessible_of_natIso (normalizedRightIso.{w} T).symm χ
  exact Functor.isCardinalAccessible_toArrow (normalizedFunctor.{w} T) χ

end Normalization

section FixedCollections

variable {A : Type uA} [Category.{vA} A] {S : Type s} (T : S → A ⥤ Arrow (Type t))

/-- The whole original collected source is its literal fixed sum of original sources. -/
def collectionLeftIso :
    collectionFunctor T ⋙ Arrow.leftFunc ≅
      fixedSumFunctor (fun k => T k ⋙ Arrow.leftFunc) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The whole original collected target is its literal fixed sum of original targets. -/
def collectionRightIso :
    collectionFunctor T ⋙ Arrow.rightFunc ≅
      fixedSumFunctor (fun k => T k ⋙ Arrow.rightFunc) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The SAME fixed component collection has source preservation without a tag bound. -/
theorem collectionLeft_isCardinalAccessible (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ k, (T k ⋙ Arrow.leftFunc).IsCardinalAccessible χ] :
    (collectionFunctor T ⋙ Arrow.leftFunc).IsCardinalAccessible χ := by
  let _ : (fixedSumFunctor (fun k => T k ⋙ Arrow.leftFunc)).IsCardinalAccessible χ :=
    fixedSumFunctor_isCardinalAccessible _ χ
  exact Functor.isCardinalAccessible_of_natIso (collectionLeftIso T).symm χ

/-- The SAME fixed component collection has target preservation without a tag bound. -/
theorem collectionRight_isCardinalAccessible (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ k, (T k ⋙ Arrow.rightFunc).IsCardinalAccessible χ] :
    (collectionFunctor T ⋙ Arrow.rightFunc).IsCardinalAccessible χ := by
  let _ : (fixedSumFunctor (fun k => T k ⋙ Arrow.rightFunc)).IsCardinalAccessible χ :=
    fixedSumFunctor_isCardinalAccessible _ χ
  exact Functor.isCardinalAccessible_of_natIso (collectionRightIso T).symm χ

/-- Both original collection projections give preservation of the whole original Arrow. -/
theorem collection_isCardinalAccessible (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ k, (T k ⋙ Arrow.leftFunc).IsCardinalAccessible χ]
    [∀ k, (T k ⋙ Arrow.rightFunc).IsCardinalAccessible χ] :
    (collectionFunctor T).IsCardinalAccessible χ := by
  let _ : (collectionFunctor T ⋙ Arrow.leftFunc).IsCardinalAccessible χ :=
    collectionLeft_isCardinalAccessible T χ
  let _ : (collectionFunctor T ⋙ Arrow.rightFunc).IsCardinalAccessible χ :=
    collectionRight_isCardinalAccessible T χ
  exact Functor.isCardinalAccessible_toArrow (collectionFunctor T) χ

end FixedCollections

section ScalarFunctions

variable {C : Type uC} [Category.{vC} C] {I : Type s} (f : I → Arrow C)

/-- The original diagonal functor is exactly the fixed sum of original endpoint Hom functors. -/
def scalarLeftIso :
    rawFunctor f ⋙ Arrow.leftFunc ≅
      fixedSumFunctor (fun k => Arrow.leftFunc ⋙ coyoneda.obj (op (f k).right)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The original native square functor is exactly the fixed sum of original Arrow Hom functors. -/
def scalarRightIso :
    rawFunctor f ⋙ Arrow.rightFunc ≅
      fixedSumFunctor (fun k => coyoneda.obj (op (f k))) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end ScalarFunctions

section ScalarSmallness

variable {C : Type uC} [Category.{vC} C] [LocallySmall.{w} C]
  {I : Type s} [Small.{w} I] (f : I → Arrow C)

/-- The SAME raw test has a working-small source at each original Arrow. -/
instance rawFunctor_left_small (p : Arrow C) : Small.{w} ((rawFunctor f).obj p).left := by
  change Small.{w} (RawLifts f p)
  infer_instance

/-- The SAME raw test has a working-small target retaining each native square. -/
instance rawFunctor_right_small (p : Arrow C) : Small.{w} ((rawFunctor f).obj p).right := by
  change Small.{w} (RawSquares f p)
  infer_instance

/-- The admitted working-size test is the SAME actual normalization of its original raw test. -/
def smallNormalizedIso : smallFunctor.{w} f ≅ normalizedFunctor.{w} (rawFunctor f) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end ScalarSmallness

/-- BOTH original endpoint bounds make the same original generator Arrow presentable. -/
theorem generator_isCardinalPresentable
    {C : Type uC} [Category.{vC} C] [HasColimitsOfSize.{w, w} C]
    (g : Arrow C) (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [IsCardinalPresentable g.left χ] [IsCardinalPresentable g.right χ] :
    IsCardinalPresentable g χ := by
  change IsCardinalPresentable (Arrow.mk g.hom) χ
  exact Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C)
    (X₁ := g.left) (X₂ := g.right) (κ := χ) g.hom

/-- Both original endpoints derive preservation of the SAME original scalar lifting test. -/
theorem smallFunctor_isCardinalAccessible
    {C : Type uC} [Category.{vC} C] [LocallySmall.{w} C]
    [HasColimitsOfSize.{w, w} C] {I : Type s} [Small.{w} I] (f : I → Arrow C)
    (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ k, IsCardinalPresentable (f k).left χ]
    [∀ k, IsCardinalPresentable (f k).right χ] :
    (smallFunctor.{w} f).IsCardinalAccessible χ := by
  let _ : HasCardinalFilteredColimits C χ := inferInstance
  let _ : (Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.fst (𝟭 C) (𝟭 C)).IsCardinalAccessible χ)
  let (k : I) : IsCardinalPresentable (f k) χ := generator_isCardinalPresentable (f k) χ
  let (k : I) : (Arrow.leftFunc ⋙ coyoneda.obj (op (f k).right)).IsCardinalAccessible χ :=
    inferInstance
  let (k : I) : (coyoneda.obj (op (f k))).IsCardinalAccessible χ := inferInstance
  let _ : (fixedSumFunctor (fun k => Arrow.leftFunc ⋙
      coyoneda.obj (op (f k).right))).IsCardinalAccessible χ :=
    fixedSumFunctor_isCardinalAccessible _ χ
  let _ : (fixedSumFunctor (fun k => coyoneda.obj (op (f k)))).IsCardinalAccessible χ :=
    fixedSumFunctor_isCardinalAccessible _ χ
  let _ : (rawFunctor f ⋙ Arrow.leftFunc).IsCardinalAccessible χ :=
    Functor.isCardinalAccessible_of_natIso (scalarLeftIso f).symm χ
  let _ : (rawFunctor f ⋙ Arrow.rightFunc).IsCardinalAccessible χ :=
    Functor.isCardinalAccessible_of_natIso (scalarRightIso f).symm χ
  let _ : (normalizedFunctor.{w} (rawFunctor f)).IsCardinalAccessible χ :=
    normalized_isCardinalAccessible (rawFunctor f) χ
  exact Functor.isCardinalAccessible_of_natIso (smallNormalizedIso.{w} f).symm χ

/-- Every original evaluation Arrow functor preserves working filtered colimits. -/
theorem evaluationArrow_isCardinalAccessible
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    [HasColimitsOfSize.{w, w} C] (d : D) (χ : Cardinal.{w}) [Fact χ.IsRegular] :
    (Functor.mapArrow ((evaluation D C).obj d)).IsCardinalAccessible χ := by
  let _ : HasCardinalFilteredColimits (D ⥤ C) χ := inferInstance
  let _ : (Arrow.leftFunc : Arrow (D ⥤ C) ⥤ D ⥤ C).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.fst (𝟭 (D ⥤ C)) (𝟭 (D ⥤ C))).IsCardinalAccessible χ)
  let _ : (Arrow.rightFunc : Arrow (D ⥤ C) ⥤ D ⥤ C).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.snd (𝟭 (D ⥤ C)) (𝟭 (D ⥤ C))).IsCardinalAccessible χ)
  let _ : ((evaluation D C).obj d).IsCardinalAccessible χ := by
    refine ⟨fun J _ _ => ?_⟩
    let _ : HasColimitsOfShape J C := inferInstance
    infer_instance
  let _ : (Functor.mapArrow ((evaluation D C).obj d) ⋙ Arrow.leftFunc).IsCardinalAccessible χ := by
    change (Arrow.leftFunc ⋙ (evaluation D C).obj d).IsCardinalAccessible χ
    infer_instance
  let _ : (Functor.mapArrow ((evaluation D C).obj d) ⋙ Arrow.rightFunc).IsCardinalAccessible χ := by
    change (Arrow.rightFunc ⋙ (evaluation D C).obj d).IsCardinalAccessible χ
    infer_instance
  exact Functor.isCardinalAccessible_toArrow _ χ

section OriginalDiagrams

variable {D : Type uD} [Category.{vD} D]
  {S : Type uS} [Category.{vS} S]
  {C : Type uC} [Category.{vC} C] [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} C] {I : Type s} [Small.{w} I]
  (e : D ≌ S) (f : I → Arrow C) (χ : Cardinal.{w}) [Fact χ.IsRegular]
  [∀ k, IsCardinalPresentable (f k).left χ]
  [∀ k, IsCardinalPresentable (f k).right χ]

/-- Each SAME original representative component derives preservation from original endpoints. -/
theorem componentFunctor_isCardinalAccessible (x : S) :
    (componentFunctor.{w} e f x).IsCardinalAccessible χ := by
  let _ : (Functor.mapArrow ((evaluation D C).obj (e.inverse.obj x))).IsCardinalAccessible χ :=
    evaluationArrow_isCardinalAccessible (e.inverse.obj x) χ
  let _ : (smallFunctor.{w} f).IsCardinalAccessible χ := smallFunctor_isCardinalAccessible f χ
  change (Functor.mapArrow ((evaluation D C).obj (e.inverse.obj x)) ⋙
    smallFunctor.{w} f).IsCardinalAccessible χ
  infer_instance

/-- The entire SAME original representative collection preserves these filtered colimits. -/
theorem diagramCollection_isCardinalAccessible :
    (diagramCollection.{w} e f).IsCardinalAccessible χ := by
  let (x : S) : (componentFunctor.{w} e f x).IsCardinalAccessible χ :=
    componentFunctor_isCardinalAccessible e f χ x
  let _ : (Arrow.leftFunc : Arrow (Type w) ⥤ Type w).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.fst (𝟭 (Type w)) (𝟭 (Type w))).IsCardinalAccessible χ)
  let _ : (Arrow.rightFunc : Arrow (Type w) ⥤ Type w).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.snd (𝟭 (Type w)) (𝟭 (Type w))).IsCardinalAccessible χ)
  let (x : S) : (componentFunctor.{w} e f x ⋙ Arrow.leftFunc).IsCardinalAccessible χ :=
    inferInstance
  let (x : S) : (componentFunctor.{w} e f x ⋙ Arrow.rightFunc).IsCardinalAccessible χ :=
    inferInstance
  exact collection_isCardinalAccessible (componentFunctor.{w} e f) χ

variable [Small.{w} S]

/-- BOTH original endpoint bounds derive preservation of the SAME original diagram test. -/
theorem diagramFunctor_isCardinalAccessible :
    (diagramFunctor.{w} e f).IsCardinalAccessible χ := by
  let (x : S) : (componentFunctor.{w} e f x).IsCardinalAccessible χ :=
    componentFunctor_isCardinalAccessible e f χ x
  let _ : (Arrow.leftFunc : Arrow (Type w) ⥤ Type w).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.fst (𝟭 (Type w)) (𝟭 (Type w))).IsCardinalAccessible χ)
  let _ : (Arrow.rightFunc : Arrow (Type w) ⥤ Type w).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.snd (𝟭 (Type w)) (𝟭 (Type w))).IsCardinalAccessible χ)
  let (x : S) : (componentFunctor.{w} e f x ⋙ Arrow.leftFunc).IsCardinalAccessible χ :=
    inferInstance
  let (x : S) : (componentFunctor.{w} e f x ⋙ Arrow.rightFunc).IsCardinalAccessible χ :=
    inferInstance
  let _ : (diagramCollection.{w} e f ⋙ Arrow.leftFunc).IsCardinalAccessible χ :=
    collectionLeft_isCardinalAccessible (componentFunctor.{w} e f) χ
  let _ : (diagramCollection.{w} e f ⋙ Arrow.rightFunc).IsCardinalAccessible χ :=
    collectionRight_isCardinalAccessible (componentFunctor.{w} e f) χ
  change (normalizedFunctor.{w} (diagramCollection.{w} e f)).IsCardinalAccessible χ
  exact normalized_isCardinalAccessible (diagramCollection.{w} e f) χ

end OriginalDiagrams

end CategoryTheory.Presentable.LiftingTest
