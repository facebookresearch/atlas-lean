/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.MapLeftSumNaturality
public import MathlibExt.CategoryTheory.Monoidal.SInverseSFunctor

/-!
# The actual mapped-zero unit of the original left-sum action

The original action NaturalIso, canonical mapped-zero Iso and original
zero-addition row Iso give the square. Equality is detected by the actual
normalized middle map. The canonical biproduct projection equations prove
that middle square; no unit or equivariant-functor outcome is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

universe uC vC uD vD

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalMiddleComposite {A B Z : ExtensionCategory D}
    (a : A ⟶ B) (b : B ⟶ Z) :
    (homNormalization (a ≫ b)).hom.2.hom =
      (homNormalization a).hom.2.hom ≫ (homNormalization b).hom.2.hom :=
  congrArg (fun k : A.subdivisionObj ⟶ Z.subdivisionObj => k.hom.2.hom)
    (homNormalization_comp a b)

private theorem originalMiddleIdentity (A : ExtensionCategory D) :
    (homNormalization (𝟙 A)).hom.2.hom = 𝟙 A.row.X₂ :=
  congrArg (fun k : A.subdivisionObj ⟶ A.subdivisionObj => k.hom.2.hom)
    (homNormalization_id A)

omit [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] in
private theorem identityMiddleHEq {A B : D} (h : A = B) : HEq (𝟙 A) (𝟙 B) := by
  cases h
  exact HEq.rfl

omit [HasZeroObject D] [ExactCategory D] in
private theorem binaryMiddleHEq {A B A' B' X Y X' Y' : D}
    (hA : A = A') (hB : B = B') (hX : X = X') (hY : Y = Y')
    {a : A ⟶ X} {a' : A' ⟶ X'} {b : B ⟶ Y} {b' : B' ⟶ Y'}
    (ha : HEq a a') (hb : HEq b b') :
    HEq (biprod.map a b) (biprod.map a' b') := by
  cases hA
  cases hB
  cases hX
  cases hY
  cases ha
  cases hb
  exact HEq.rfl

omit [HasZeroObject D] [ExactCategory D] in
private theorem secondProjectionHEq {A B A' B' : D} (hA : A = A') (hB : B = B') :
    HEq (biprod.snd : A ⊞ B ⟶ B) (biprod.snd : A' ⊞ B' ⟶ B') := by
  cases hA
  cases hB
  exact HEq.rfl

private theorem originalLeftSumUnitComputed (E : ExtensionCategory C) :
    ((mapLeftSumNaturalityIso F).app (𝟙_ (Core C), E)).hom ≫
        leftSumMap
          (Core.isoMk (x := F.core.obj (𝟙_ (Core C))) (y := 𝟙_ (Core D))
            F.mapZeroObject).hom (𝟙 ((mapFunctor F).obj E)) ≫
        (leftSumUnitIso ((mapFunctor F).obj E)).hom =
      (mapFunctor F).map (leftSumUnitIso E).hom := by
  let G := mapFunctor F
  let A := G.obj (leftSumObj (𝟙_ (Core C)) E)
  let B := leftSumObj (F.core.obj (𝟙_ (Core C))) (G.obj E)
  let Z := leftSumObj (𝟙_ (Core D)) (G.obj E)
  let u : F.core.obj (𝟙_ (Core C)) ≅ 𝟙_ (Core D) := Core.isoMk F.mapZeroObject
  let a : A ⟶ B := ((mapLeftSumNaturalityIso F).app (𝟙_ (Core C), E)).hom
  let b : B ⟶ Z := leftSumMap u.hom (𝟙 (G.obj E))
  let c : Z ⟶ G.obj E := (leftSumUnitIso (G.obj E)).hom
  let d : A ⟶ G.obj E := G.map (leftSumUnitIso E).hom
  have hE : (G.obj E).row.X₂ = F.obj E.row.X₂ := mapFunctor_middle_obj F E
  have hA : A.row.X₂ = F.obj ((0 : C) ⊞ E.row.X₂) :=
    mapFunctor_middle_obj F (leftSumObj (𝟙_ (Core C)) E)
  have hB : B.row.X₂ = (F.obj (0 : C) ⊞ F.obj E.row.X₂) :=
    congrArg₂ (fun X Y : D => X ⊞ Y) rfl hE
  have hZ : Z.row.X₂ = ((0 : D) ⊞ F.obj E.row.X₂) :=
    congrArg (fun X : D => (0 : D) ⊞ X) hE
  have ha : HEq (homNormalization a).hom.2.hom
      (F.mapBiprod (0 : C) E.row.X₂).hom :=
    mapLeftSumNaturalityIso_app_middle_hom_heq F (𝟙_ (Core C)) E
  have hb₀ : (homNormalization b).hom.2.hom =
      biprod.map u.hom.iso.hom (𝟙 (G.obj E).row.X₂) :=
    (leftSumMap_beta u.hom (𝟙 (G.obj E))).trans
      (congrArg (biprod.map u.hom.iso.hom) (originalMiddleIdentity (G.obj E)))
  have hb : HEq (homNormalization b).hom.2.hom
      (biprod.map F.mapZeroObject.hom (𝟙 (F.obj E.row.X₂))) :=
    (heq_of_eq hb₀).trans
      (binaryMiddleHEq rfl hE rfl hE (heq_of_eq rfl) (identityMiddleHEq hE))
  have hc : HEq (homNormalization c).hom.2.hom
      (biprod.snd : (0 : D) ⊞ F.obj E.row.X₂ ⟶ F.obj E.row.X₂) :=
    (heq_of_eq (leftSumUnitIso_beta (G.obj E))).trans (secondProjectionHEq rfl hE)
  have hd : HEq (homNormalization d).hom.2.hom
      (F.map (biprod.snd : (0 : C) ⊞ E.row.X₂ ⟶ E.row.X₂)) :=
    (mapFunctor_middle_heq F (leftSumUnitIso E).hom).trans
      (heq_of_eq (congrArg F.map (leftSumUnitIso_beta E)))
  have hbc := heq_comp hB hZ hE hb hc
  have habc := heq_comp hA hB hE ha hbc
  have hMiddle : (homNormalization (a ≫ b ≫ c)).hom.2.hom =
      (homNormalization a).hom.2.hom ≫
        (homNormalization b).hom.2.hom ≫ (homNormalization c).hom.2.hom :=
    (originalMiddleComposite a (b ≫ c)).trans
      (congrArg (fun k : B.row.X₂ ⟶ (G.obj E).row.X₂ =>
        (homNormalization a).hom.2.hom ≫ k) (originalMiddleComposite b c))
  have hProjection :
      (F.mapBiprod (0 : C) E.row.X₂).hom ≫
          (biprod.snd : F.obj (0 : C) ⊞ F.obj E.row.X₂ ⟶ F.obj E.row.X₂) =
        F.map (biprod.snd : (0 : C) ⊞ E.row.X₂ ⟶ E.row.X₂) :=
    F.biprodComparison_snd (0 : C) E.row.X₂
  have hCanonical :
      (F.mapBiprod (0 : C) E.row.X₂).hom ≫
          biprod.map F.mapZeroObject.hom (𝟙 (F.obj E.row.X₂)) ≫
          (biprod.snd : (0 : D) ⊞ F.obj E.row.X₂ ⟶ F.obj E.row.X₂) =
        F.map (biprod.snd : (0 : C) ⊞ E.row.X₂ ⟶ E.row.X₂) := by
    rw [biprod.map_snd, Category.comp_id]
    exact hProjection
  have hActual : (homNormalization (a ≫ b ≫ c)).hom.2.hom =
      (homNormalization d).hom.2.hom :=
    eq_of_heq ((heq_of_eq hMiddle).trans
      (habc.trans ((heq_of_eq hCanonical).trans hd.symm)))
  exact hom_ext_of_middle (a ≫ b ≫ c) d hActual

/-- The actual action comparison preserves the original unit through canonical mapZeroObject. -/
public theorem mapLeftSumNaturalityIso_original_unit (E : ExtensionCategory C) :
    ((mapLeftSumNaturalityIso F).app (𝟙_ (Core C), E)).hom ≫
        leftSumMap
          (Core.isoMk (x := F.core.obj (𝟙_ (Core C))) (y := 𝟙_ (Core D))
            F.mapZeroObject).hom (𝟙 ((mapFunctor F).obj E)) ≫
        (leftSumUnitIso ((mapFunctor F).obj E)).hom =
      (mapFunctor F).map (leftSumUnitIso E).hom :=
  originalLeftSumUnitComputed F E


omit [HasZeroObject D] [ExactCategory D] in
private theorem associatorMiddleHEq {A B Z A' B' Z' : D}
    (hA : A = A') (hB : B = B') (hZ : Z = Z') :
    HEq (biprod.associator A B Z).hom (biprod.associator A' B' Z').hom := by
  cases hA
  cases hB
  cases hZ
  exact HEq.rfl

omit [HasZeroObject C] [HasZeroObject D] [ExactCategory C] [ExactCategory D]
  [F.IsExact] in
private theorem actualCanonicalMapBiprodAssociator (A B Z : C) :
    F.map (biprod.associator A B Z).hom ≫
        (F.mapBiprod A (B ⊞ Z)).hom ≫
        biprod.map (𝟙 (F.obj A)) (F.mapBiprod B Z).hom =
      (F.mapBiprod (A ⊞ B) Z).hom ≫
        biprod.map (F.mapBiprod A B).hom (𝟙 (F.obj Z)) ≫
        (biprod.associator (F.obj A) (F.obj B) (F.obj Z)).hom := by
  apply biprod.hom_ext
  · simp only [Functor.mapBiprod_hom, biprod.associator_hom,
      Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc,
      biprod.map_fst, biprod.map_fst_assoc, Category.comp_id,
      ← Functor.map_comp]
  · apply biprod.hom_ext
    · simp only [Functor.mapBiprod_hom, biprod.associator_hom,
        Category.assoc, biprod.lift_fst, biprod.lift_snd,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc,
        biprod.map_fst_assoc, biprod.map_snd_assoc,
        ← Functor.map_comp]
    · simp only [Functor.mapBiprod_hom, biprod.associator_hom,
        Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc,
        biprod.map_snd, biprod.map_snd_assoc, Category.comp_id,
        ← Functor.map_comp]

private theorem originalLeftSumAssociatorComputed
    (T U : Core C) (E : ExtensionCategory C) :
    ((mapLeftSumNaturalityIso F).app (T ⊗ U, E)).hom ≫
        leftSumMap
          (Core.isoMk (x := F.core.obj (T ⊗ U))
            (y := F.core.obj T ⊗ F.core.obj U) (F.mapBiprod T.of U.of)).hom
          (𝟙 ((mapFunctor F).obj E)) ≫
        (leftSumAssocIso (F.core.obj T) (F.core.obj U) ((mapFunctor F).obj E)).hom =
      (mapFunctor F).map (leftSumAssocIso T U E).hom ≫
        ((mapLeftSumNaturalityIso F).app (T, leftSumObj U E)).hom ≫
        leftSumMap (𝟙 (F.core.obj T)) ((mapLeftSumNaturalityIso F).app (U, E)).hom := by
  let G := mapFunctor F
  let A := G.obj (leftSumObj (T ⊗ U) E)
  let B := leftSumObj (F.core.obj (T ⊗ U)) (G.obj E)
  let Z := leftSumObj (F.core.obj T ⊗ F.core.obj U) (G.obj E)
  let V := leftSumObj (F.core.obj T) (leftSumObj (F.core.obj U) (G.obj E))
  let K := G.obj (leftSumObj T (leftSumObj U E))
  let L := leftSumObj (F.core.obj T) (G.obj (leftSumObj U E))
  let u : F.core.obj (T ⊗ U) ≅ F.core.obj T ⊗ F.core.obj U :=
    Core.isoMk (F.mapBiprod T.of U.of)
  let a : A ⟶ B := ((mapLeftSumNaturalityIso F).app (T ⊗ U, E)).hom
  let b : B ⟶ Z := leftSumMap u.hom (𝟙 (G.obj E))
  let c : Z ⟶ V := (leftSumAssocIso (F.core.obj T) (F.core.obj U) (G.obj E)).hom
  let d : A ⟶ K := G.map (leftSumAssocIso T U E).hom
  let e : K ⟶ L := ((mapLeftSumNaturalityIso F).app (T, leftSumObj U E)).hom
  let f : L ⟶ V :=
    leftSumMap (𝟙 (F.core.obj T)) ((mapLeftSumNaturalityIso F).app (U, E)).hom
  have hE : (G.obj E).row.X₂ = F.obj E.row.X₂ := mapFunctor_middle_obj F E
  have hT : (F.core.obj T).of = F.obj T.of := rfl
  have hU : (F.core.obj U).of = F.obj U.of := rfl
  have hTU : (F.core.obj (T ⊗ U)).of = F.obj (T.of ⊞ U.of) := rfl
  have hTensor : (F.core.obj T ⊗ F.core.obj U).of = (F.obj T.of ⊞ F.obj U.of) := rfl
  have hA : A.row.X₂ = F.obj ((T.of ⊞ U.of) ⊞ E.row.X₂) :=
    mapFunctor_middle_obj F (leftSumObj (T ⊗ U) E)
  have hB : B.row.X₂ = (F.obj (T.of ⊞ U.of) ⊞ F.obj E.row.X₂) :=
    congrArg₂ (fun X Y : D => X ⊞ Y) hTU hE
  have hZ : Z.row.X₂ = ((F.obj T.of ⊞ F.obj U.of) ⊞ F.obj E.row.X₂) :=
    congrArg₂ (fun X Y : D => X ⊞ Y) hTensor hE
  have hV : V.row.X₂ = (F.obj T.of ⊞ (F.obj U.of ⊞ F.obj E.row.X₂)) :=
    congrArg (fun X : D => F.obj T.of ⊞ (F.obj U.of ⊞ X)) hE
  have hK : K.row.X₂ = F.obj (T.of ⊞ (U.of ⊞ E.row.X₂)) :=
    mapFunctor_middle_obj F (leftSumObj T (leftSumObj U E))
  have hGU : (G.obj (leftSumObj U E)).row.X₂ = F.obj (U.of ⊞ E.row.X₂) :=
    mapFunctor_middle_obj F (leftSumObj U E)
  have hL : L.row.X₂ = (F.obj T.of ⊞ F.obj (U.of ⊞ E.row.X₂)) :=
    congrArg (fun X : D => F.obj T.of ⊞ X) hGU
  have hUA : (leftSumObj (F.core.obj U) (G.obj E)).row.X₂ =
      (F.obj U.of ⊞ F.obj E.row.X₂) :=
    congrArg₂ (fun X Y : D => X ⊞ Y) hU hE
  have ha : HEq (homNormalization a).hom.2.hom
      (F.mapBiprod (T.of ⊞ U.of) E.row.X₂).hom :=
    mapLeftSumNaturalityIso_app_middle_hom_heq F (T ⊗ U) E
  have hb₀ : (homNormalization b).hom.2.hom =
      biprod.map u.hom.iso.hom (𝟙 (G.obj E).row.X₂) :=
    (leftSumMap_beta u.hom (𝟙 (G.obj E))).trans
      (congrArg (biprod.map u.hom.iso.hom) (originalMiddleIdentity (G.obj E)))
  have hb : HEq (homNormalization b).hom.2.hom
      (biprod.map (F.mapBiprod T.of U.of).hom (𝟙 (F.obj E.row.X₂))) :=
    (heq_of_eq hb₀).trans
      (binaryMiddleHEq hTU hE hTensor hE (heq_of_eq rfl) (identityMiddleHEq hE))
  have hc : HEq (homNormalization c).hom.2.hom
      (biprod.associator (F.obj T.of) (F.obj U.of) (F.obj E.row.X₂)).hom :=
    (heq_of_eq (leftSumAssocIso_beta (F.core.obj T) (F.core.obj U) (G.obj E))).trans
      (associatorMiddleHEq hT hU hE)
  have hd : HEq (homNormalization d).hom.2.hom
      (F.map (biprod.associator T.of U.of E.row.X₂).hom) :=
    (mapFunctor_middle_heq F (leftSumAssocIso T U E).hom).trans
      (heq_of_eq (congrArg F.map (leftSumAssocIso_beta T U E)))
  have he : HEq (homNormalization e).hom.2.hom
      (F.mapBiprod T.of (U.of ⊞ E.row.X₂)).hom :=
    mapLeftSumNaturalityIso_app_middle_hom_heq F T (leftSumObj U E)
  have hf₀ : (homNormalization f).hom.2.hom =
      biprod.map (𝟙 (F.core.obj T) : F.core.obj T ⟶ F.core.obj T).iso.hom
        (homNormalization ((mapLeftSumNaturalityIso F).app (U, E)).hom).hom.2.hom :=
    leftSumMap_beta (𝟙 (F.core.obj T)) ((mapLeftSumNaturalityIso F).app (U, E)).hom
  have hId : HEq (𝟙 (F.core.obj T) : F.core.obj T ⟶ F.core.obj T).iso.hom (𝟙 (F.obj T.of)) :=
    (heq_of_eq ((Core.inclusion D).map_id (F.core.obj T))).trans (identityMiddleHEq hT)
  have hf : HEq (homNormalization f).hom.2.hom
      (biprod.map (𝟙 (F.obj T.of)) (F.mapBiprod U.of E.row.X₂).hom) :=
    (heq_of_eq hf₀).trans
      (binaryMiddleHEq hT hGU hT hUA hId
        (mapLeftSumNaturalityIso_app_middle_hom_heq F U E))
  have hLeft := heq_comp hA hB hV ha (heq_comp hB hZ hV hb hc)
  have hRight := heq_comp hA hK hV hd (heq_comp hK hL hV he hf)
  have hLeftMiddle : (homNormalization (a ≫ b ≫ c)).hom.2.hom =
      (homNormalization a).hom.2.hom ≫
        (homNormalization b).hom.2.hom ≫ (homNormalization c).hom.2.hom :=
    (originalMiddleComposite a (b ≫ c)).trans
      (congrArg (fun k : B.row.X₂ ⟶ V.row.X₂ => (homNormalization a).hom.2.hom ≫ k)
        (originalMiddleComposite b c))
  have hRightMiddle : (homNormalization (d ≫ e ≫ f)).hom.2.hom =
      (homNormalization d).hom.2.hom ≫
        (homNormalization e).hom.2.hom ≫ (homNormalization f).hom.2.hom :=
    (originalMiddleComposite d (e ≫ f)).trans
      (congrArg (fun k : K.row.X₂ ⟶ V.row.X₂ => (homNormalization d).hom.2.hom ≫ k)
        (originalMiddleComposite e f))
  have hCanonical := actualCanonicalMapBiprodAssociator F T.of U.of E.row.X₂
  have hActual : (homNormalization (a ≫ b ≫ c)).hom.2.hom =
      (homNormalization (d ≫ e ≫ f)).hom.2.hom :=
    eq_of_heq ((heq_of_eq hLeftMiddle).trans
      (hLeft.trans ((heq_of_eq hCanonical.symm).trans
        (hRight.symm.trans (heq_of_eq hRightMiddle.symm)))))
  exact hom_ext_of_middle (a ≫ b ≫ c) (d ≫ e ≫ f) hActual

/-- The actual action comparison preserves the original associator with canonical mapBiprod. -/
public theorem mapLeftSumNaturalityIso_original_associator
    (T U : Core C) (E : ExtensionCategory C) :
    ((mapLeftSumNaturalityIso F).app (T ⊗ U, E)).hom ≫
        leftSumMap
          (Core.isoMk (x := F.core.obj (T ⊗ U))
            (y := F.core.obj T ⊗ F.core.obj U) (F.mapBiprod T.of U.of)).hom
          (𝟙 ((mapFunctor F).obj E)) ≫
        (leftSumAssocIso (F.core.obj T) (F.core.obj U) ((mapFunctor F).obj E)).hom =
      (mapFunctor F).map (leftSumAssocIso T U E).hom ≫
        ((mapLeftSumNaturalityIso F).app (T, leftSumObj U E)).hom ≫
        leftSumMap (𝟙 (F.core.obj T)) ((mapLeftSumNaturalityIso F).app (U, E)).hom :=
  originalLeftSumAssociatorComputed F T U E


private theorem originalLeftSumAssociatorInverseComputed
    (T U : Core C) (E : ExtensionCategory C) :
    leftSumMap
        (Core.isoMk (x := F.core.obj (T ⊗ U))
          (y := F.core.obj T ⊗ F.core.obj U) (F.mapBiprod T.of U.of)).hom
        (𝟙 ((mapFunctor F).obj E)) ≫
        (leftSumAssocIso (F.core.obj T) (F.core.obj U) ((mapFunctor F).obj E)).hom ≫
        leftSumMap (𝟙 (F.core.obj T)) ((mapLeftSumNaturalityIso F).app (U, E)).inv =
      ((mapLeftSumNaturalityIso F).app (T ⊗ U, E)).inv ≫
        (mapFunctor F).map (leftSumAssocIso T U E).hom ≫
        ((mapLeftSumNaturalityIso F).app (T, leftSumObj U E)).hom := by
  let G := mapFunctor F
  let A := G.obj (leftSumObj (T ⊗ U) E)
  let B := leftSumObj (F.core.obj (T ⊗ U)) (G.obj E)
  let X := G.obj (leftSumObj T (leftSumObj U E))
  let Y := leftSumObj (F.core.obj T) (G.obj (leftSumObj U E))
  let Z := leftSumObj (F.core.obj T) (leftSumObj (F.core.obj U) (G.obj E))
  let W := leftSumObj (F.core.obj T ⊗ F.core.obj U) (G.obj E)
  let t : A ≅ B := (mapLeftSumNaturalityIso F).app (T ⊗ U, E)
  let v : X ≅ Y := (mapLeftSumNaturalityIso F).app (T, leftSumObj U E)
  let w : G.obj (leftSumObj U E) ≅ leftSumObj (F.core.obj U) (G.obj E) :=
    (mapLeftSumNaturalityIso F).app (U, E)
  let u : F.core.obj (T ⊗ U) ≅ F.core.obj T ⊗ F.core.obj U :=
    Core.isoMk (F.mapBiprod T.of U.of)
  let L : B ⟶ W := leftSumMap u.hom (𝟙 (G.obj E))
  let z : W ⟶ Z := (leftSumAssocIso (F.core.obj T) (F.core.obj U) (G.obj E)).hom
  let d : A ⟶ X := G.map (leftSumAssocIso T U E).hom
  let H : Y ⟶ Z := leftSumMap (𝟙 (F.core.obj T)) w.hom
  let I : Z ⟶ Y := leftSumMap (𝟙 (F.core.obj T)) w.inv
  have hAssoc : t.hom ≫ L ≫ z = d ≫ v.hom ≫ H :=
    mapLeftSumNaturalityIso_original_associator F T U E
  have hCancel : H ≫ I = 𝟙 Y := by
    let q : Y ≅ Z := (leftSumFunctor (C := D)).mapIso ((Iso.refl (F.core.obj T)).prod w)
    have hH : q.hom = H := rfl
    have hI : q.inv = I := rfl
    exact (congrArg₂ (fun (f : Y ⟶ Z) (g : Z ⟶ Y) => f ≫ g) hH.symm hI.symm).trans
      q.hom_inv_id
  have hPost : t.hom ≫ L ≫ z ≫ I = d ≫ v.hom := by
    have h := congrArg (fun k : A ⟶ Z => k ≫ I) hAssoc
    have hL₁ : (t.hom ≫ L ≫ z) ≫ I = ((t.hom ≫ L) ≫ z) ≫ I :=
      congrArg (fun k : A ⟶ Z => k ≫ I) (Category.assoc t.hom L z).symm
    have hL₂ : ((t.hom ≫ L) ≫ z) ≫ I = (t.hom ≫ L) ≫ (z ≫ I) :=
      Category.assoc (t.hom ≫ L) z I
    have hL₃ : (t.hom ≫ L) ≫ (z ≫ I) = t.hom ≫ L ≫ z ≫ I :=
      Category.assoc t.hom L (z ≫ I)
    have hLeft := hL₁.trans (hL₂.trans hL₃)
    have hR₁ : (d ≫ v.hom ≫ H) ≫ I = ((d ≫ v.hom) ≫ H) ≫ I :=
      congrArg (fun k : A ⟶ Z => k ≫ I) (Category.assoc d v.hom H).symm
    have hR₂ : ((d ≫ v.hom) ≫ H) ≫ I = (d ≫ v.hom) ≫ (H ≫ I) :=
      Category.assoc (d ≫ v.hom) H I
    have hR₃ : (d ≫ v.hom) ≫ (H ≫ I) = (d ≫ v.hom) ≫ 𝟙 Y :=
      congrArg (fun k : Y ⟶ Y => (d ≫ v.hom) ≫ k) hCancel
    have hRight := hR₁.trans (hR₂.trans (hR₃.trans (Category.comp_id (d ≫ v.hom))))
    exact hLeft.symm.trans (h.trans hRight)
  change L ≫ z ≫ I = t.inv ≫ d ≫ v.hom
  apply (cancel_epi t.hom).1
  have hInverse : t.hom ≫ (t.inv ≫ d ≫ v.hom) = d ≫ v.hom := by
    have h₁ : t.hom ≫ (t.inv ≫ d ≫ v.hom) = (t.hom ≫ t.inv) ≫ (d ≫ v.hom) :=
      (Category.assoc t.hom t.inv (d ≫ v.hom)).symm
    have h₂ : (t.hom ≫ t.inv) ≫ (d ≫ v.hom) = 𝟙 A ≫ (d ≫ v.hom) :=
      congrArg (fun k : A ⟶ A => k ≫ (d ≫ v.hom)) t.hom_inv_id
    exact h₁.trans (h₂.trans (Category.id_comp (d ≫ v.hom)))
  exact hPost.trans hInverse.symm

/-- The actual inverse action component retains the original associator route. -/
public theorem mapLeftSumNaturalityIso_original_associator_inv
    (T U : Core C) (E : ExtensionCategory C) :
    leftSumMap
        (Core.isoMk (x := F.core.obj (T ⊗ U))
          (y := F.core.obj T ⊗ F.core.obj U) (F.mapBiprod T.of U.of)).hom
        (𝟙 ((mapFunctor F).obj E)) ≫
        (leftSumAssocIso (F.core.obj T) (F.core.obj U) ((mapFunctor F).obj E)).hom ≫
        leftSumMap (𝟙 (F.core.obj T)) ((mapLeftSumNaturalityIso F).app (U, E)).inv =
      ((mapLeftSumNaturalityIso F).app (T ⊗ U, E)).inv ≫
        (mapFunctor F).map (leftSumAssocIso T U E).hom ≫
        ((mapLeftSumNaturalityIso F).app (T, leftSumObj U E)).hom :=
  originalLeftSumAssociatorInverseComputed F T U E

private theorem originalInverseRightNaturalityComputed
    (T : Core C) {E E' : ExtensionCategory C} (r : E ⟶ E') :
    leftSumMap (𝟙 (F.core.obj T)) ((mapFunctor F).map r) ≫
        ((mapLeftSumNaturalityIso F).app (T, E')).inv =
      ((mapLeftSumNaturalityIso F).app (T, E)).inv ≫
        (mapFunctor F).map (leftSumMap (𝟙 T) r) := by
  let G := mapFunctor F
  let A := mapLeftSumNaturalityIso F
  have hn := A.inv.naturality (X := (T, E)) (Y := (T, E')) (𝟙 T, r)
  change leftSumMap (F.core.map (𝟙 T)) (G.map r) ≫ (A.app (T, E')).inv =
    (A.app (T, E)).inv ≫ G.map (leftSumMap (𝟙 T) r) at hn
  have hId : leftSumMap (F.core.map (𝟙 T)) (G.map r) =
      leftSumMap (𝟙 (F.core.obj T)) (G.map r) :=
    congrArg (fun k : F.core.obj T ⟶ F.core.obj T => leftSumMap k (G.map r))
      (F.core.map_id T)
  exact (congrArg (fun k : leftSumObj (F.core.obj T) (G.obj E) ⟶
      leftSumObj (F.core.obj T) (G.obj E') => k ≫ (A.app (T, E')).inv) hId.symm).trans hn

/-- The actual inverse action comparison is natural for every original extension arrow. -/
public theorem mapLeftSumNaturalityIso_inv_right_naturality
    (T : Core C) {E E' : ExtensionCategory C} (r : E ⟶ E') :
    leftSumMap (𝟙 (F.core.obj T)) ((mapFunctor F).map r) ≫
        ((mapLeftSumNaturalityIso F).app (T, E')).inv =
      ((mapLeftSumNaturalityIso F).app (T, E)).inv ≫
        (mapFunctor F).map (leftSumMap (𝟙 T) r) :=
  originalInverseRightNaturalityComputed F T r

end AlgebraicKTheory.ExtensionCategory

end
