/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.MapLeftSumNaturality
public import MathlibExt.KTheory.Exact.Extension.MapLeftSumUnitCoherence
public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization
public import MathlibExt.CategoryTheory.Monoidal.SInverseSFunctor
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMonoidal

/-!
# Original stabilized extension objects and raw denominators under an exact functor

The actual numerator object is sent through the original extension functor,
and the actual denominator and stabilizer through the original core functor.
The derived left-sum comparison returns the numerator map to its original
stabilized source. The canonical mapBiprod inverse transports the denominator
Iso. No equivariant/localized functor or source agreement is a premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

universe uC vC uD vD

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The original positive numerator and denominator are mapped without exchanging coordinates. -/
public def stabilizedFunctorObject (a : SInverse (Core C) (ExtensionCategory C)) :
    SInverse (Core D) (ExtensionCategory D) :=
  ⟨((ExtensionCategory.mapFunctor F).obj a.of.1, F.core.obj a.of.2)⟩

/-- The original raw stabilizer and both given component maps have their actual images. -/
public def stabilizedFunctorRawMap
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (stabilizedFunctorObject F a) (stabilizedFunctorObject F b) where
  stabilizer := F.core.obj r.stabilizer
  hom :=
    (((ExtensionCategory.mapLeftSumNaturalityIso F).app (r.stabilizer, a.of.1)).inv ≫
      (ExtensionCategory.mapFunctor F).map r.hom.1,
      ⟨(F.mapBiprod r.stabilizer.of a.of.2.of).symm ≪≫ F.mapIso r.hom.2.iso⟩)

private theorem stabilizedFunctorObjectComputed
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (stabilizedFunctorObject F a).of =
      ((ExtensionCategory.mapFunctor F).obj a.of.1, F.core.obj a.of.2) := rfl

/-- Both original localized object coordinates retain their exact given image values. -/
public theorem stabilizedFunctorObject_of
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (stabilizedFunctorObject F a).of =
      ((ExtensionCategory.mapFunctor F).obj a.of.1, F.core.obj a.of.2) :=
  stabilizedFunctorObjectComputed F a


private theorem originalMappedStabilizerComputed
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (stabilizedFunctorRawMap F r).stabilizer = F.core.obj r.stabilizer := rfl

/-- The actual raw stabilizer retains the original core image object. -/
public theorem stabilizedFunctorRawMap_stabilizer
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (stabilizedFunctorRawMap F r).stabilizer = F.core.obj r.stabilizer :=
  originalMappedStabilizerComputed F r

/-- The same mapped source Iso, with its two exact raw endpoint presentations. -/
public def stabilizedFunctorRawMapStabilizerIso
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ≅ s.stabilizer) :
    (stabilizedFunctorRawMap F r).stabilizer ≅
      (stabilizedFunctorRawMap F s).stabilizer :=
  eqToIso (stabilizedFunctorRawMap_stabilizer F r) ≪≫ F.core.mapIso e ≪≫
    (eqToIso (stabilizedFunctorRawMap_stabilizer F s)).symm


open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

private theorem originalStabilizerNumeratorRelation
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ≅ s.stabilizer)
    (h : e.hom ⊵ₗ a.of ≫ s.hom = r.hom) :
    ExtensionCategory.leftSumMap (F.core.map e.hom)
        (𝟙 ((ExtensionCategory.mapFunctor F).obj a.of.1)) ≫
      (stabilizedFunctorRawMap F s).hom.1 = (stabilizedFunctorRawMap F r).hom.1 := by
  let G := ExtensionCategory.mapFunctor F
  let T := ExtensionCategory.mapLeftSumNaturalityIso F
  let x := a.of.1
  have hOriginal : ExtensionCategory.leftSumMap e.hom (𝟙 x) ≫ s.hom.1 = r.hom.1 := by
    have hx := congrArg (fun f : r.stabilizer ⊙ₗ a.of ⟶ b.of => f.1) h
    exact hx
  have hNatural := T.inv.naturality
    (X := (r.stabilizer, x)) (Y := (s.stabilizer, x)) (e.hom, 𝟙 x)
  change ExtensionCategory.leftSumMap (F.core.map e.hom) (G.map (𝟙 x)) ≫
      (T.app (s.stabilizer, x)).inv =
    (T.app (r.stabilizer, x)).inv ≫ G.map (ExtensionCategory.leftSumMap e.hom (𝟙 x))
    at hNatural
  have hMapIdentity : ExtensionCategory.leftSumMap (F.core.map e.hom) (G.map (𝟙 x)) =
      ExtensionCategory.leftSumMap (F.core.map e.hom) (𝟙 (G.obj x)) :=
    congrArg (fun f : G.obj x ⟶ G.obj x =>
      ExtensionCategory.leftSumMap (F.core.map e.hom) f) (G.map_id x)
  have hInverseNatural :
      ExtensionCategory.leftSumMap (F.core.map e.hom) (𝟙 (G.obj x)) ≫
          (T.app (s.stabilizer, x)).inv =
        (T.app (r.stabilizer, x)).inv ≫
          G.map (ExtensionCategory.leftSumMap e.hom (𝟙 x)) :=
    (congrArg (fun f : ExtensionCategory.leftSumObj (F.core.obj r.stabilizer) (G.obj x) ⟶
        ExtensionCategory.leftSumObj (F.core.obj s.stabilizer) (G.obj x) =>
      f ≫ (T.app (s.stabilizer, x)).inv) hMapIdentity.symm).trans hNatural
  have hMapped : G.map (ExtensionCategory.leftSumMap e.hom (𝟙 x)) ≫ G.map s.hom.1 =
      G.map r.hom.1 :=
    (G.map_comp (ExtensionCategory.leftSumMap e.hom (𝟙 x)) s.hom.1).symm.trans
      (congrArg G.map hOriginal)
  change ExtensionCategory.leftSumMap (F.core.map e.hom) (𝟙 (G.obj x)) ≫
      ((T.app (s.stabilizer, x)).inv ≫ G.map s.hom.1) =
    (T.app (r.stabilizer, x)).inv ≫ G.map r.hom.1
  exact (Category.assoc
    (ExtensionCategory.leftSumMap (F.core.map e.hom) (𝟙 (G.obj x)))
    (T.app (s.stabilizer, x)).inv (G.map s.hom.1)).symm.trans
      ((congrArg (fun f : ExtensionCategory.leftSumObj (F.core.obj r.stabilizer) (G.obj x) ⟶
          G.obj (ExtensionCategory.leftSumObj s.stabilizer x) => f ≫ G.map s.hom.1)
        hInverseNatural).trans
          ((Category.assoc (T.app (r.stabilizer, x)).inv
            (G.map (ExtensionCategory.leftSumMap e.hom (𝟙 x))) (G.map s.hom.1)).trans
              (congrArg (fun f : G.obj (ExtensionCategory.leftSumObj r.stabilizer x) ⟶
                  G.obj b.of.1 => (T.app (r.stabilizer, x)).inv ≫ f) hMapped)))


private theorem originalMappedStabilizerHomComputed
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ≅ s.stabilizer) :
    (stabilizedFunctorRawMapStabilizerIso F r s e).hom = F.core.map e.hom := by
  have hr : (eqToIso (stabilizedFunctorRawMap_stabilizer F r)).hom =
      𝟙 (F.core.obj r.stabilizer) :=
    eqToHom_refl (F.core.obj r.stabilizer) (stabilizedFunctorRawMap_stabilizer F r)
  have hs : (eqToIso (stabilizedFunctorRawMap_stabilizer F s)).inv =
      𝟙 (F.core.obj s.stabilizer) :=
    eqToHom_refl (F.core.obj s.stabilizer) (stabilizedFunctorRawMap_stabilizer F s).symm
  dsimp only [stabilizedFunctorRawMapStabilizerIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact (congrArg₂ (fun (u : F.core.obj r.stabilizer ⟶ F.core.obj r.stabilizer)
      (v : F.core.obj s.stabilizer ⟶ F.core.obj s.stabilizer) =>
    u ≫ F.core.map e.hom ≫ v) hr hs).trans
      ((Category.id_comp (F.core.map e.hom ≫ 𝟙 (F.core.obj s.stabilizer))).trans
        (Category.comp_id (F.core.map e.hom)))

private theorem originalMappedNumeratorRelationComputed
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ≅ s.stabilizer)
    (h : e.hom ⊵ₗ a.of ≫ s.hom = r.hom) :
    (((stabilizedFunctorRawMapStabilizerIso F r s e).hom ⊵ₗ
        (stabilizedFunctorObject F a).of).1) ≫
      (stabilizedFunctorRawMap F s).hom.1 = (stabilizedFunctorRawMap F r).hom.1 := by
  have ha := congrArg (fun k : F.core.obj r.stabilizer ⟶ F.core.obj s.stabilizer =>
    ((k ⊵ₗ (stabilizedFunctorObject F a).of).1) ≫ (stabilizedFunctorRawMap F s).hom.1)
      (originalMappedStabilizerHomComputed F r s e)
  exact ha.trans (originalStabilizerNumeratorRelation F r s e h)

/-- The numerator equation uses the actual raw endpoints of the same mapped stabilizer Iso. -/
public theorem stabilizedFunctorRawMap_numerator_relation
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ≅ s.stabilizer)
    (h : e.hom ⊵ₗ a.of ≫ s.hom = r.hom) :
    (((stabilizedFunctorRawMapStabilizerIso F r s e).hom ⊵ₗ
        (stabilizedFunctorObject F a).of).1) ≫
      (stabilizedFunctorRawMap F s).hom.1 = (stabilizedFunctorRawMap F r).hom.1 :=
  originalMappedNumeratorRelationComputed F r s e h


private theorem originalStabilizerDenominatorRelation
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ≅ s.stabilizer)
    (h : e.hom ⊵ₗ a.of ≫ s.hom = r.hom) :
    (F.core.map e.hom ▷ F.core.obj a.of.2) ≫
      (stabilizedFunctorRawMap F s).hom.2 = (stabilizedFunctorRawMap F r).hom.2 := by
  have hOriginalCore : (e.hom ▷ a.of.2) ≫ s.hom.2 = r.hom.2 :=
    congrArg (fun f : r.stabilizer ⊙ₗ a.of ⟶ b.of => f.2) h
  have hOriginal :
      (CategoryTheory.SInverseS.stabilizerIso e.hom.iso a.of.2.of).trans s.hom.2.iso =
        r.hom.2.iso := by
    apply Iso.ext
    exact congrArg (fun f : r.stabilizer ⊗ a.of.2 ⟶ b.of.2 => f.iso.hom)
      hOriginalCore
  apply Core.hom_ext
  change (CategoryTheory.SInverseS.stabilizerIso (F.mapIso e.hom.iso)
      (F.obj a.of.2.of)).hom ≫
      ((F.mapBiprod s.stabilizer.of a.of.2.of).symm.trans (F.mapIso s.hom.2.iso)).hom =
    ((F.mapBiprod r.stabilizer.of a.of.2.of).symm.trans (F.mapIso r.hom.2.iso)).hom
  exact CategoryTheory.SInverseS.mapBiprod_original_stabilizer_relation F
    e.hom.iso r.hom.2.iso s.hom.2.iso hOriginal

private theorem originalMappedDenominatorRelationComputed
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ≅ s.stabilizer)
    (h : e.hom ⊵ₗ a.of ≫ s.hom = r.hom) :
    (((stabilizedFunctorRawMapStabilizerIso F r s e).hom ⊵ₗ
        (stabilizedFunctorObject F a).of).2) ≫
      (stabilizedFunctorRawMap F s).hom.2 = (stabilizedFunctorRawMap F r).hom.2 := by
  have ha := congrArg (fun k : F.core.obj r.stabilizer ⟶ F.core.obj s.stabilizer =>
    ((k ⊵ₗ (stabilizedFunctorObject F a).of).2) ≫ (stabilizedFunctorRawMap F s).hom.2)
      (originalMappedStabilizerHomComputed F r s e)
  exact ha.trans (originalStabilizerDenominatorRelation F r s e h)

/-- The denominator uses the actual raw endpoints of the same mapped stabilizer Iso. -/
public theorem stabilizedFunctorRawMap_denominator_relation
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ≅ s.stabilizer)
    (h : e.hom ⊵ₗ a.of ≫ s.hom = r.hom) :
    (((stabilizedFunctorRawMapStabilizerIso F r s e).hom ⊵ₗ
        (stabilizedFunctorObject F a).of).2) ≫
      (stabilizedFunctorRawMap F s).hom.2 = (stabilizedFunctorRawMap F r).hom.2 :=
  originalMappedDenominatorRelationComputed F r s e h

/-- Every original raw stabilizer relation is preserved, in both coordinates at once. -/
public theorem stabilizedFunctorRawMap_rel
    {a b : SInverse (Core C) (ExtensionCategory C)}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (stabilizedFunctorRawMap F r).Rel (stabilizedFunctorRawMap F s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨stabilizedFunctorRawMapStabilizerIso F r s e, ?_⟩
  exact Prod.ext (stabilizedFunctorRawMap_numerator_relation F r s e he)
    (stabilizedFunctorRawMap_denominator_relation F r s e he)


private theorem originalRawIdentityComputed
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (stabilizedFunctorRawMap F (MonoidalActionCategory.RawHom.id a)).Rel
      (MonoidalActionCategory.RawHom.id (stabilizedFunctorObject F a)) := by
  dsimp only [MonoidalActionCategory.RawHom.Rel, stabilizedFunctorRawMap,
    MonoidalActionCategory.RawHom.id, stabilizedFunctorObject]
  refine ⟨Core.isoMk F.mapZeroObject, ?_⟩
  apply Prod.ext
  · let G := ExtensionCategory.mapFunctor F
    let A := G.obj (ExtensionCategory.leftSumObj (𝟙_ (Core C)) a.of.1)
    let B := ExtensionCategory.leftSumObj (F.core.obj (𝟙_ (Core C))) (G.obj a.of.1)
    let t : A ≅ B :=
      (ExtensionCategory.mapLeftSumNaturalityIso F).app (𝟙_ (Core C), a.of.1)
    let u : F.core.obj (𝟙_ (Core C)) ≅ 𝟙_ (Core D) := Core.isoMk F.mapZeroObject
    let L : B ⟶ G.obj a.of.1 := ExtensionCategory.leftSumMap u.hom (𝟙 (G.obj a.of.1)) ≫
      (ExtensionCategory.leftSumUnitIso (G.obj a.of.1)).hom
    let k : A ⟶ G.obj a.of.1 := G.map (ExtensionCategory.leftSumUnitIso a.of.1).hom
    change L = t.inv ≫ k
    have hUnit : t.hom ≫ L = k :=
      ExtensionCategory.mapLeftSumNaturalityIso_original_unit F a.of.1
    have hInverse : t.hom ≫ (t.inv ≫ k) = k := by
      have h₁ : t.hom ≫ (t.inv ≫ k) = (t.hom ≫ t.inv) ≫ k :=
        (Category.assoc t.hom t.inv k).symm
      have h₂ : (t.hom ≫ t.inv) ≫ k = 𝟙 A ≫ k :=
        congrArg (fun z : A ⟶ A => z ≫ k) t.hom_inv_id
      exact h₁.trans (h₂.trans (Category.id_comp k))
    exact (cancel_epi t.hom).1 (hUnit.trans hInverse.symm)
  · apply Core.hom_ext
    have h := congrArg Iso.hom
      (CategoryTheory.SInverseS.mapBiprod_original_zero_unit F a.of.2.of)
    change (CategoryTheory.SInverseS.stabilizerIso F.mapZeroObject (F.obj a.of.2.of)).hom ≫
        (isoZeroBiprod (X := (0 : D)) (Y := F.obj a.of.2.of) (isZero_zero D)).inv =
      ((F.mapBiprod (0 : C) a.of.2.of).symm.trans
        (F.mapIso (isoZeroBiprod (X := (0 : C)) (Y := a.of.2.of)
          (isZero_zero C)).symm)).hom
    exact h

/-- The original raw unit maps to the target unit class through canonical mapZeroObject. -/
public theorem stabilizedFunctorRawMap_id_rel
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (stabilizedFunctorRawMap F (MonoidalActionCategory.RawHom.id a)).Rel
      (MonoidalActionCategory.RawHom.id (stabilizedFunctorObject F a)) :=
  originalRawIdentityComputed F a



private theorem originalRawRegroup
    {A B X Y Z W V : ExtensionCategory D}
    (a : A ⟶ B) (b : B ⟶ X) (c : X ⟶ Y) (d : Y ⟶ Z)
    (e : Z ⟶ W) (f : W ⟶ V) :
    a ≫ b ≫ (c ≫ d) ≫ (e ≫ f) = (a ≫ b ≫ c) ≫ (d ≫ e) ≫ f := by
  simp only [Category.assoc]

private theorem originalRawCancelComponent
    {A B X Y Z W : ExtensionCategory D}
    (a : A ⟶ B) (b : B ⟶ X) (e : X ≅ Y) (c : X ⟶ Z) (d : Z ⟶ W) :
    (a ≫ b ≫ e.hom) ≫ (e.inv ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem originalRawCompositionComputed
    {a b c : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    (stabilizedFunctorRawMap F (r.comp s)).Rel
      ((stabilizedFunctorRawMap F r).comp (stabilizedFunctorRawMap F s)) := by
  dsimp only [MonoidalActionCategory.RawHom.Rel, stabilizedFunctorRawMap,
    MonoidalActionCategory.RawHom.comp, stabilizedFunctorObject]
  refine ⟨Core.isoMk (F.mapBiprod s.stabilizer.of r.stabilizer.of), ?_⟩
  apply Prod.ext
  · let G := ExtensionCategory.mapFunctor F
    let T := s.stabilizer
    let U := r.stabilizer
    let E := a.of.1
    let X := ExtensionCategory.leftSumObj U E
    let Y := b.of.1
    let Z := c.of.1
    let GX := G.obj (ExtensionCategory.leftSumObj T X)
    let GY := G.obj (ExtensionCategory.leftSumObj T Y)
    let A := G.obj (ExtensionCategory.leftSumObj (T ⊗ U) E)
    let B := ExtensionCategory.leftSumObj (F.core.obj (T ⊗ U)) (G.obj E)
    let C' := ExtensionCategory.leftSumObj (F.core.obj T ⊗ F.core.obj U) (G.obj E)
    let D' := ExtensionCategory.leftSumObj (F.core.obj T)
      (ExtensionCategory.leftSumObj (F.core.obj U) (G.obj E))
    let M := ExtensionCategory.leftSumObj (F.core.obj T) (G.obj X)
    let N := ExtensionCategory.leftSumObj (F.core.obj T) (G.obj Y)
    let u : F.core.obj (T ⊗ U) ≅ F.core.obj T ⊗ F.core.obj U :=
      Core.isoMk (F.mapBiprod T.of U.of)
    let θU : G.obj X ≅ ExtensionCategory.leftSumObj (F.core.obj U) (G.obj E) :=
      (ExtensionCategory.mapLeftSumNaturalityIso F).app (U, E)
    let θT : GY ≅ N := (ExtensionCategory.mapLeftSumNaturalityIso F).app (T, Y)
    let θTU : A ≅ B := (ExtensionCategory.mapLeftSumNaturalityIso F).app (T ⊗ U, E)
    let θUE : GX ≅ M := (ExtensionCategory.mapLeftSumNaturalityIso F).app (T, X)
    let R : G.obj X ⟶ G.obj Y := G.map r.hom.1
    let S : GY ⟶ G.obj Z := G.map s.hom.1
    let L : B ⟶ C' := ExtensionCategory.leftSumMap u.hom (𝟙 (G.obj E))
    let α : C' ⟶ D' :=
      (ExtensionCategory.leftSumAssocIso (F.core.obj T) (F.core.obj U) (G.obj E)).hom
    let BMap : A ⟶ GX := G.map (ExtensionCategory.leftSumAssocIso T U E).hom
    let CMap : GX ⟶ GY := G.map (ExtensionCategory.leftSumMap (𝟙 T) r.hom.1)
    let J : D' ⟶ M := ExtensionCategory.leftSumMap (𝟙 (F.core.obj T)) θU.inv
    let K : M ⟶ N := ExtensionCategory.leftSumMap (𝟙 (F.core.obj T)) R
    change L ≫ α ≫ ExtensionCategory.leftSumMap (𝟙 (F.core.obj T)) (θU.inv ≫ R) ≫
        (θT.inv ≫ S) =
      θTU.inv ≫ G.map ((ExtensionCategory.leftSumAssocIso T U E).hom ≫
        ExtensionCategory.leftSumMap (𝟙 T) r.hom.1 ≫ s.hom.1)
    have hSplit : ExtensionCategory.leftSumMap (𝟙 (F.core.obj T)) (θU.inv ≫ R) = J ≫ K :=
      (congrArg (fun f : F.core.obj T ⟶ F.core.obj T =>
        ExtensionCategory.leftSumMap f (θU.inv ≫ R))
          (Category.id_comp (𝟙 (F.core.obj T)))).symm.trans
        (ExtensionCategory.leftSumMap_comp (𝟙 (F.core.obj T)) (𝟙 (F.core.obj T)) θU.inv R)
    have hAssoc : L ≫ α ≫ J = θTU.inv ≫ BMap ≫ θUE.hom :=
      ExtensionCategory.mapLeftSumNaturalityIso_original_associator_inv F T U E
    have hMove : K ≫ θT.inv = θUE.inv ≫ CMap :=
      ExtensionCategory.mapLeftSumNaturalityIso_inv_right_naturality F T r.hom.1
    have h₁ : L ≫ α ≫ ExtensionCategory.leftSumMap (𝟙 (F.core.obj T)) (θU.inv ≫ R) ≫
        (θT.inv ≫ S) = L ≫ α ≫ (J ≫ K) ≫ (θT.inv ≫ S) :=
      congrArg (fun f : D' ⟶ N => L ≫ α ≫ f ≫ (θT.inv ≫ S)) hSplit
    have h₂ : L ≫ α ≫ (J ≫ K) ≫ (θT.inv ≫ S) =
        (L ≫ α ≫ J) ≫ (K ≫ θT.inv) ≫ S :=
      originalRawRegroup L α J K θT.inv S
    have h₃ : (L ≫ α ≫ J) ≫ (K ≫ θT.inv) ≫ S =
        (θTU.inv ≫ BMap ≫ θUE.hom) ≫ (θUE.inv ≫ CMap) ≫ S :=
      congrArg₂ (fun (f : B ⟶ M) (g : M ⟶ GY) => f ≫ g ≫ S) hAssoc hMove
    have h₄ : (θTU.inv ≫ BMap ≫ θUE.hom) ≫ (θUE.inv ≫ CMap) ≫ S =
        θTU.inv ≫ BMap ≫ CMap ≫ S :=
      originalRawCancelComponent θTU.inv BMap θUE CMap S
    have hMapped : G.map ((ExtensionCategory.leftSumAssocIso T U E).hom ≫
        ExtensionCategory.leftSumMap (𝟙 T) r.hom.1 ≫ s.hom.1) = BMap ≫ CMap ≫ S :=
      (G.map_comp (ExtensionCategory.leftSumAssocIso T U E).hom
        (ExtensionCategory.leftSumMap (𝟙 T) r.hom.1 ≫ s.hom.1)).trans
        (congrArg (fun f : GX ⟶ G.obj Z => BMap ≫ f)
          (G.map_comp (ExtensionCategory.leftSumMap (𝟙 T) r.hom.1) s.hom.1))
    have h₅ : θTU.inv ≫ BMap ≫ CMap ≫ S =
        θTU.inv ≫ G.map ((ExtensionCategory.leftSumAssocIso T U E).hom ≫
          ExtensionCategory.leftSumMap (𝟙 T) r.hom.1 ≫ s.hom.1) :=
      congrArg (fun f : A ⟶ G.obj Z => θTU.inv ≫ f) hMapped.symm
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  · apply Core.hom_ext
    change biprod.map (F.mapBiprod s.stabilizer.of r.stabilizer.of).hom
        (𝟙 (F.obj a.of.2.of)) ≫
        (biprod.associator (F.obj s.stabilizer.of) (F.obj r.stabilizer.of)
          (F.obj a.of.2.of)).hom ≫
        biprod.map (𝟙 (F.obj s.stabilizer.of))
          ((F.mapBiprod r.stabilizer.of a.of.2.of).inv ≫ F.map r.hom.2.iso.hom) ≫
        (F.mapBiprod s.stabilizer.of b.of.2.of).inv ≫ F.map s.hom.2.iso.hom =
      (F.mapBiprod (s.stabilizer.of ⊞ r.stabilizer.of) a.of.2.of).inv ≫ F.map
        ((biprod.associator s.stabilizer.of r.stabilizer.of a.of.2.of).hom ≫
          biprod.map (𝟙 s.stabilizer.of) r.hom.2.iso.hom ≫ s.hom.2.iso.hom)
    exact CategoryTheory.SInverseS.mapBiprod_original_composition_coordinate F
      r.hom.2.iso s.hom.2.iso

/-- The actual original stabilized composition retains its later-then-earlier stabilizer. -/
public theorem stabilizedFunctorRawMap_comp_rel
    {a b c : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    (stabilizedFunctorRawMap F (r.comp s)).Rel
      ((stabilizedFunctorRawMap F r).comp (stabilizedFunctorRawMap F s)) :=
  originalRawCompositionComputed F r s


/-- The actual image of every original stabilized quotient-diagram class. -/
public def stabilizedFunctorMap :
    SInverse (Core C) (ExtensionCategory C) ⥤ SInverse (Core D) (ExtensionCategory D) where
  obj := stabilizedFunctorObject F
  map f := Quotient.map (stabilizedFunctorRawMap F)
    (fun _ _ h => stabilizedFunctorRawMap_rel F h) f
  map_id a := by
    exact Quotient.sound (stabilizedFunctorRawMap_id_rel F a)
  map_comp f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    exact Quotient.sound (stabilizedFunctorRawMap_comp_rel F r s)

private theorem originalStabilizedFunctorObjectComputed
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (stabilizedFunctorMap F).obj a = stabilizedFunctorObject F a := rfl

/-- The localized functor retains the original positive and denominator image object. -/
public theorem stabilizedFunctorMap_obj
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (stabilizedFunctorMap F).obj a = stabilizedFunctorObject F a :=
  originalStabilizedFunctorObjectComputed F a

private theorem originalStabilizedFunctorRepresentativeComputed
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) :
    HEq ((stabilizedFunctorMap F).map (MonoidalActionCategory.Hom.mk r))
      (MonoidalActionCategory.Hom.mk (stabilizedFunctorRawMap F r)) := heq_of_eq rfl

/-- Every original raw representative keeps the exact derived map, with its endpoint views. -/
public theorem stabilizedFunctorMap_mkHom_heq
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) :
    HEq ((stabilizedFunctorMap F).map (MonoidalActionCategory.Hom.mk r))
      (MonoidalActionCategory.Hom.mk (stabilizedFunctorRawMap F r)) :=
  originalStabilizedFunctorRepresentativeComputed F r


private theorem originalMappedRawComponentsComputed
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (stabilizedFunctorRawMap F r).stabilizer = F.core.obj r.stabilizer ∧
      HEq (stabilizedFunctorRawMap F r).hom.1
        (((ExtensionCategory.mapLeftSumNaturalityIso F).app (r.stabilizer, a.of.1)).inv ≫
          (ExtensionCategory.mapFunctor F).map r.hom.1) ∧
      HEq (stabilizedFunctorRawMap F r).hom.2
        (⟨(F.mapBiprod r.stabilizer.of a.of.2.of).symm.trans (F.mapIso r.hom.2.iso)⟩ :
          (F.core.obj r.stabilizer ⊗ F.core.obj a.of.2) ⟶ F.core.obj b.of.2) :=
  ⟨rfl, heq_of_eq rfl, heq_of_eq rfl⟩

/-- Both raw coordinate maps retain their literal canonical image recipes and endpoint views. -/
public theorem stabilizedFunctorRawMap_components
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (stabilizedFunctorRawMap F r).stabilizer = F.core.obj r.stabilizer ∧
      HEq (stabilizedFunctorRawMap F r).hom.1
        (((ExtensionCategory.mapLeftSumNaturalityIso F).app (r.stabilizer, a.of.1)).inv ≫
          (ExtensionCategory.mapFunctor F).map r.hom.1) ∧
      HEq (stabilizedFunctorRawMap F r).hom.2
        (⟨(F.mapBiprod r.stabilizer.of a.of.2.of).symm.trans (F.mapIso r.hom.2.iso)⟩ :
          (F.core.obj r.stabilizer ⊗ F.core.obj a.of.2) ⟶ F.core.obj b.of.2) :=
  originalMappedRawComponentsComputed F r

end AlgebraicKTheory.ExtensionCategory

end
