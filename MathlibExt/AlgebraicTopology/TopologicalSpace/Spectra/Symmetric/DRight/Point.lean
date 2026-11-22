/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.DRight.OriginalFreePoint
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.DRight.HomComparison
import MathlibExt.CategoryTheory.Enriched.InducedPointTransport
import MathlibExt.CategoryTheory.Enriched.IndexedPointHomMap

/-!
# Points and composition in the right-module operator index

The enriched Hom comparison from the right-module index to the symmetric
operator index sends each module-map point to its free-Yoneda evaluation
after transport through the right-module presentation. The comparison
also preserves enriched identities and composition, with the two Hom
factors in their source-first order.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricDRightPoint

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

/-- The original standard RIGHT carrier of the complete source points. -/
abbrev Carrier := SymmetricModuleMappingComparison.Carrier.{u, v}
/-- The actual original whole carrier comparison to operator diagrams. -/
abbrev U := SymmetricRightModulePresentation.rightModuleToOperator.{u, v}
open SymmetricDRightHomComparison

section WholePoints
universe uW vW uC vC uJ
variable {W : Type uW} [Category.{vW} W] [MonoidalCategory W]

private theorem scalar_point_transport {X Y : W} (h : X = Y)
    (p : 𝟙_ W ⟶ X) (q : 𝟙_ W ⟶ Y) (hp : HEq p q) :
    p ≫ (eqToIso h).hom = q := by
  cases h
  cases hp
  rw [eqToIso_refl, Iso.refl_hom, Category.comp_id]

private theorem identity_point_transport {A : Type uC} [EnrichedCategory W A]
    {a b : A} (h : a = b) :
    eId W a ≫ eqToHom (congrArg₂ (fun x y : A => x ⟶[W] y) h h) = eId W b := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

private theorem composition_point_transport {A : Type uC} [EnrichedCategory W A]
    {a a' b b' c c' : A} (ha : a = a') (hb : b = b') (hc : c = c') :
    eComp W a b c ≫ eqToHom (congrArg₂ (fun x y : A => x ⟶[W] y) ha hc) =
      (eqToHom (congrArg₂ (fun x y : A => x ⟶[W] y) ha hb) ⊗ₘ
        eqToHom (congrArg₂ (fun x y : A => x ⟶[W] y) hb hc)) ≫ eComp W a' b' c' := by
  cases ha
  cases hb
  cases hc
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id]

private theorem forget_composition_point_transport {A : Type uC} [EnrichedCategory W A]
    {a a' b b' c c' : ForgetEnrichment W A} (ha : a = a') (hb : b = b') (hc : c = c') :
    eComp W (ForgetEnrichment.to W a) (ForgetEnrichment.to W b)
      (ForgetEnrichment.to W c) ≫
        eqToHom (congrArg₂ (fun x y : ForgetEnrichment W A =>
          ForgetEnrichment.to W x ⟶[W] ForgetEnrichment.to W y) ha hc) =
      (eqToHom (congrArg₂ (fun x y : ForgetEnrichment W A =>
          ForgetEnrichment.to W x ⟶[W] ForgetEnrichment.to W y) ha hb) ⊗ₘ
        eqToHom (congrArg₂ (fun x y : ForgetEnrichment W A =>
          ForgetEnrichment.to W x ⟶[W] ForgetEnrichment.to W y) hb hc)) ≫
            eComp W (ForgetEnrichment.to W a') (ForgetEnrichment.to W b')
              (ForgetEnrichment.to W c') := by
  cases ha
  cases hb
  cases hc
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id]

private theorem identity_iso_specialize {C : Type uC} [EnrichedCategory W C]
    {J : Type uJ} [EnrichedCategory W J] (x : C) (y : J)
    (i : (x ⟶[W] x) ≅ (y ⟶[W] y)) (m : (x ⟶[W] x) ⟶ (y ⟶[W] y))
    (hm : m = i.hom) (h : eId W x ≫ m = eId W y) :
    eId W x ≫ i.hom = eId W y := by
  rw [← hm]
  exact h

private theorem composition_iso_specialize {C : Type uC} [EnrichedCategory W C]
    {J : Type uJ} [EnrichedCategory W J] (x y z : C) (a b c : J)
    (i : (x ⟶[W] y) ≅ (a ⟶[W] b))
    (j : (y ⟶[W] z) ≅ (b ⟶[W] c))
    (k : (x ⟶[W] z) ≅ (a ⟶[W] c))
    (mi : (x ⟶[W] y) ⟶ (a ⟶[W] b)) (mj : (y ⟶[W] z) ⟶ (b ⟶[W] c))
    (mk : (x ⟶[W] z) ⟶ (a ⟶[W] c))
    (hi : mi = i.hom) (hj : mj = j.hom) (hk : mk = k.hom)
    (h : eComp W x y z ≫ mk = (mi ⊗ₘ mj) ≫ eComp W a b c) :
    eComp W x y z ≫ k.hom = (i.hom ⊗ₘ j.hom) ≫ eComp W a b c := by
  rw [← hi, ← hj, ← hk]
  exact h

variable {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory W C]

@[reassoc]
private theorem homCongr_point {X X' Y Y' : C} (f : X ⟶ Y) (a : X ≅ X') (b : Y ≅ Y') :
    eHomEquiv W f ≫ (Iso.eHomCongr W a b).hom = eHomEquiv W (a.inv ≫ f ≫ b.hom) := by
  change eHomEquiv W f ≫ (eHomWhiskerRight W a.inv Y ≫
    eHomWhiskerLeft W X' b.hom) = _
  rw [← Category.assoc, eHomEquiv_comp_eHomWhiskerRight, eHomEquiv_comp_eHomWhiskerLeft,
    Category.assoc]

end WholePoints

@[reassoc]
private theorem source_point (d e : Operad.SmallFinBijGroupoid)
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (sourceHomIso d e).hom =
      eHomEquiv PointedCGWH.{u, v} (SymmetricDRightOrdinary.homEquiv d e f) :=
  SymmetricDRightHomComparison.sourceHomIso_point d e f

@[reassoc]
private theorem value_point (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v})
    (f : (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj
      (𝟙_ PointedCGWH.{u, v}) ⟶ M) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (SymmetricActualRightFreeHom.valueIso e M).hom =
      EnrichedFunctorCat.Free.evaluate (symmetricOperatorObj.{u, v} e)
        (𝟙_ PointedCGWH.{u, v}) (U.obj M)
        ((OriginalStandardRightFreeLevels.originalOperatorFreeIso e).inv.app
          (𝟙_ PointedCGWH.{u, v}) ≫ U.map f) :=
  SymmetricFreeAdjunctionPoint.value_point e M f

private theorem freeValue_hom (a b : SymmetricOperatorIndex.{u, v}) (X : PointedCGWH.{u, v}) :
    (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso a b).hom.app X = 𝟙 (X ⊗ (a ⟶[
      PointedCGWH.{u, v}] b)) := by
  unfold EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
  change (eqToIso (EnrichedFunctorCat.Free.object_obj a b X)).hom = _
  rw [eqToIso.hom, eqToHom_refl]

set_option backward.isDefEq.respectTransparency false in
private theorem finish_evaluate (d e : Operad.SmallFinBijGroupoid)
    (t : EnrichedFunctorCat.Free.object (symmetricOperatorObj.{u, v} e)
      (𝟙_ PointedCGWH.{u, v}) ⟶ U.obj (SymmetricDRight.freeObject d)) :
    EnrichedFunctorCat.Free.evaluate (symmetricOperatorObj.{u, v} e)
      (𝟙_ PointedCGWH.{u, v}) (U.obj (SymmetricDRight.freeObject d)) t ≫
        (SymmetricStandardRightFreeEvaluation.literalEvaluation e).map (freeObjectIso d).hom ≫
          (OriginalStandardRightFreeLevels.levelIso d (𝟙_ PointedCGWH.{u, v}) e).hom ≫
            (λ_ (OriginalStandardRightFreeLevels.coefficient d e)).hom =
      EnrichedFunctorCat.FreeYoneda.evaluateHom
        (symmetricOperatorObj.{u, v} d) (symmetricOperatorObj.{u, v} e)
        (t ≫ U.map (freeObjectIso d).hom ≫
          (OriginalStandardRightFreeLevels.originalOperatorFreeIso d).hom.app
            (𝟙_ PointedCGWH.{u, v})) := by
  rw [EnrichedFunctorCat.FreeYoneda.evaluateHom_eq,
    OriginalStandardRightFreeLevelSource.levelIso_operator_hom, freeValue_hom]
  simp only [Category.comp_id]
  have hmap : (SymmetricStandardRightFreeEvaluation.literalEvaluation e).map
      (freeObjectIso d).hom =
        EnrichedFunctorCat.component (U.map (freeObjectIso d).hom)
          (symmetricOperatorObj e) :=
    (SymmetricRightModulePresentation.rightModuleToOperator_component (freeObjectIso d).hom e).symm
  rw [hmap, EnrichedFunctorCat.Free.evaluate_postcomp,
    (EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} e)).map_comp]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every original D_R module-space point is the full original free-evaluation coend point. -/
theorem homIso_point (d e : Operad.SmallFinBijGroupoid)
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (homIso.{u, v} d e).hom =
      EnrichedFunctorCat.FreeYoneda.evaluateHom
        (symmetricOperatorObj.{u, v} d) (symmetricOperatorObj.{u, v} e)
        ((operatorFreeIso e).inv ≫ U.map (SymmetricDRightOrdinary.homEquiv d e f) ≫
          (operatorFreeIso d).hom) := by
  unfold homIso
  simp only [Iso.trans_hom]
  rw [source_point_assoc]
  rw [homCongr_point_assoc (W := PointedCGWH.{u, v})
    (SymmetricDRightOrdinary.homEquiv d e f) (freeObjectIso e)
    (Iso.refl (SymmetricDRight.freeObject d))]
  simp only [Iso.refl_hom, Category.comp_id]
  rw [value_point_assoc]
  simp only [Functor.mapIso_hom]
  rw [finish_evaluate]
  unfold operatorFreeIso
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    U.map_comp, Category.assoc]
  rfl

private def fullHomMap (d e : SymmetricDRight.Index) :
    (d ⟶[PointedCGWH.{u, v}] e) ⟶ (objectEquiv d ⟶[PointedCGWH.{u, v}] objectEquiv e) :=
  (fullHomIso.{u, v} d e).hom

private theorem fullHomMap_original (d e : SymmetricDRight.Index) :
    fullHomMap d e = (fullHomIso.{u, v} d e).hom := rfl

private theorem homIso_point_chosen (d e : Operad.SmallFinBijGroupoid)
    (i : (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj e) ≅
      (symmetricOperatorObj.{u, v} d ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} e))
    (hi : i = homIso.{u, v} d e) (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ i.hom =
      ForgetEnrichment.homTo PointedCGWH.{u, v} (sourceFunctor.{u, v}.map f) ≫
        eqToHom (congrArg₂
          (fun P Q : ForgetEnrichment PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} =>
            (ForgetEnrichment.to PointedCGWH.{u, v} P ⟶[PointedCGWH.{u, v}]
              ForgetEnrichment.to PointedCGWH.{u, v} Q))
                (sourceFunctor_object (SymmetricDRight.obj d))
                (sourceFunctor_object (SymmetricDRight.obj e))) := by
  rw [hi]
  have hp := homIso_point d e f
  have hm := congrArg
    (fun g : SymmetricDRight.freeObject e ⟶ SymmetricDRight.freeObject d =>
      EnrichedFunctorCat.FreeYoneda.evaluateHom
        (symmetricOperatorObj.{u, v} d) (symmetricOperatorObj.{u, v} e)
        ((operatorFreeIso e).inv ≫ U.map g ≫ (operatorFreeIso d).hom))
    (SymmetricDRightOrdinary.homEquiv_apply d e f)
  have hq := SymmetricDRightHomComparison.sourceFunctor_point d e f
  exact (hp.trans hm).trans hq.symm

private theorem homIso_point_function_chosen (d e : Operad.SmallFinBijGroupoid)
    (i : (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj e) ≅
      (symmetricOperatorObj d ⟶[PointedCGWH.{u, v}] symmetricOperatorObj e))
    (hi : i = homIso d e) :
    (fun f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e =>
      eHomEquiv PointedCGWH.{u, v} f ≫ i.hom) =
    (fun f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e =>
      ForgetEnrichment.homTo PointedCGWH.{u, v} (sourceFunctor.map f) ≫
      eqToHom (congrArg₂ (fun P Q : ForgetEnrichment PointedCGWH.{u, v}
        SymmetricOperatorIndex.{u, v} =>
        (ForgetEnrichment.to PointedCGWH.{u, v} P ⟶[PointedCGWH.{u, v}]
          ForgetEnrichment.to PointedCGWH.{u, v} Q))
        (sourceFunctor_object (SymmetricDRight.obj d))
        (sourceFunctor_object (SymmetricDRight.obj e)))) := by
  funext f
  exact homIso_point_chosen d e i hi f

universe uH uF vF uT vT

/-- The actual original ordinary Hom method is fixed before reconstructed index values. -/
private abbrev originalPointInputHom :
    SymmetricDRight.Index → SymmetricDRight.Index → Type v :=
  @Quiver.Hom SymmetricDRight.Index
    (@CategoryStruct.toQuiver SymmetricDRight.Index
      (@Category.toCategoryStruct SymmetricDRight.Index
        SymmetricDRightOrdinary.ordinaryCategory.{u, v}))

private theorem native_fullHomIso_point (d e : SymmetricDRight.Index) (f : d ⟶ e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (fullHomIso.{u, v} d e).hom =
      EnrichedFunctorCat.FreeYoneda.evaluateHom
        (symmetricOperatorObj.{u, v} d.asIndex) (symmetricOperatorObj.{u, v} e.asIndex)
        ((operatorFreeIso e.asIndex).inv ≫ U.map f.hom.unop ≫
          (operatorFreeIso d.asIndex).hom) := by
  cases d with
  | mk d =>
    cases e with
    | mk e =>
      let hd : SymmetricDRight.obj d = ({asIndex := d} : SymmetricDRight.Index) := rfl
      let he : SymmetricDRight.obj e = ({asIndex := e} : SymmetricDRight.Index) := rfl
      let hfType := congrArg₂ originalPointInputHom hd he
      let f' : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e := Eq.mpr hfType f
      apply Under.UnderMorphism.ext
      apply ConcreteCategory.hom_ext
      intro x
      have hp := homIso_point.{u, v} d e f'
      have hm := SymmetricDRightOrdinary.homEquiv_apply d e f'
      have hv := congrArg
        (fun g : SymmetricDRight.freeObject e ⟶ SymmetricDRight.freeObject d =>
          EnrichedFunctorCat.FreeYoneda.evaluateHom
            (symmetricOperatorObj.{u, v} d) (symmetricOperatorObj.{u, v} e)
            ((operatorFreeIso e).inv ≫ U.map g ≫ (operatorFreeIso d).hom)) hm
      have hx := congrArg
        (fun m : 𝟙_ PointedCGWH.{u, v} ⟶
          (symmetricOperatorObj.{u, v} d ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} e) =>
            m.right x) (hp.trans hv)
      dsimp only [fullHomIso, SymmetricDRight.obj, objectEquiv,
        DFunLike.coe, EquivLike.toFunLike, Equiv.instEquivLike, EquivLike.coe,
        SymmetricDRight.freeLabel, Opposite.op, Opposite.unop,
        f', hfType, hd, he, congrArg₂, Eq.mpr, U] at hx ⊢
      simp only [Under.comp_right] at hx ⊢
      exact hx

private theorem native_sourceFunctor_point (d e : SymmetricDRight.Index) (f : d ⟶ e) :
    ForgetEnrichment.homTo PointedCGWH.{u, v} (sourceFunctor.{u, v}.map f) ≫
      eqToHom (congrArg₂
        (fun P Q : ForgetEnrichment PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} =>
          (ForgetEnrichment.to PointedCGWH.{u, v} P ⟶[PointedCGWH.{u, v}]
            ForgetEnrichment.to PointedCGWH.{u, v} Q))
        (sourceFunctor_object d) (sourceFunctor_object e)) =
      EnrichedFunctorCat.FreeYoneda.evaluateHom
        (symmetricOperatorObj.{u, v} d.asIndex) (symmetricOperatorObj.{u, v} e.asIndex)
        ((operatorFreeIso e.asIndex).inv ≫ U.map f.hom.unop ≫
          (operatorFreeIso d.asIndex).hom) := by
  exact EnrichedFunctorCat.FreeMappingSource.functor_point_rebased
    (fun d : SymmetricDRight.Index => symmetricOperatorObj.{u, v} d.asIndex)
    (fun d : SymmetricDRight.Index => SymmetricDRight.freeObject.{u, v} d.asIndex)
    SymmetricRightModulePresentation.rightModuleToOperator
    (fun d => operatorFreeIso d.asIndex) f

private theorem homIso_point_function (d e : SymmetricDRight.Index) :
    (fun f : d ⟶ e => eHomEquiv PointedCGWH.{u, v} f ≫
      fullHomMap d e) =
        (fun f : d ⟶ e => ForgetEnrichment.homTo PointedCGWH.{u, v}
          (sourceFunctor.{u, v}.map f) ≫
            eqToHom (congrArg₂
              (fun P Q : ForgetEnrichment PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} =>
                (ForgetEnrichment.to PointedCGWH.{u, v} P ⟶[PointedCGWH.{u, v}]
                  ForgetEnrichment.to PointedCGWH.{u, v} Q))
                    (sourceFunctor_object d) (sourceFunctor_object e))) := by
  rw [fullHomMap_original]
  funext f
  exact (native_fullHomIso_point d e f).trans (native_sourceFunctor_point d e f).symm

private theorem equation_transport {P Q : Prop} (h : P = Q) (p : P) : Q :=
  h ▸ p

private theorem homIso_identity_whole (d : SymmetricDRight.Index) :
    eId PointedCGWH.{u, v} d ≫ fullHomMap d d =
      eId PointedCGWH.{u, v} (objectEquiv.{u, v} d) := by
  have hp := congrFun (homIso_point_function d d) (𝟙 d)
  rw [eHomEquiv_id, sourceFunctor.map_id, ForgetEnrichment.homTo_id] at hp
  have hid := identity_point_transport (W := PointedCGWH.{u, v})
    (A := ForgetEnrichment PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})
    (sourceFunctor_object d)
  exact hp.trans hid

private theorem homIso_composition_whole (d e k : SymmetricDRight.Index) :
    eComp PointedCGWH.{u, v} d e k ≫ fullHomMap d k =
      (fullHomMap d e ⊗ₘ fullHomMap e k) ≫
        eComp PointedCGWH.{u, v} (objectEquiv.{u, v} d)
          (objectEquiv.{u, v} e) (objectEquiv.{u, v} k) := by
  have h := UnitGeneratedEnrichment.map_comp_of_index_point_function
    (J := SymmetricOperatorIndex.{u, v})
    sourceFunctor objectEquiv sourceFunctor_object isSeparator_tensorUnit
    fullHomMap
    homIso_point_function d e k
  exact equation_transport (by rfl) h

/-- The entire original D_R identity is the full original coend operator identity. -/
theorem homIso_identity (d : Operad.SmallFinBijGroupoid) :
    eId PointedCGWH.{u, v} (SymmetricDRight.obj d) ≫ (homIso.{u, v} d d).hom =
      eId PointedCGWH.{u, v} (symmetricOperatorObj.{u, v} d) := by
  have hi := congrArg
    (fun i : (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj d) ≅
      (symmetricOperatorObj.{u, v} d ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} d) =>
        eId PointedCGWH.{u, v} (SymmetricDRight.obj d) ≫ i.hom =
          eId PointedCGWH.{u, v} (symmetricOperatorObj.{u, v} d))
    (fullHomIso_obj.{u, v} d d)
  exact equation_transport hi (homIso_identity_whole.{u, v} (SymmetricDRight.obj d))

/-- Both entire original module Hom factors map to actual source-first coend composition. -/
theorem homIso_composition (d e k : Operad.SmallFinBijGroupoid) :
    eComp PointedCGWH.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e)
      (SymmetricDRight.obj k) ≫ (homIso.{u, v} d k).hom =
        ((homIso.{u, v} d e).hom ⊗ₘ (homIso.{u, v} e k).hom) ≫
          eComp PointedCGWH.{u, v} (symmetricOperatorObj.{u, v} d)
            (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} k) := by
  have hi := congrArg
    (fun i : (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj k) ≅
      (symmetricOperatorObj.{u, v} d ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} k) =>
        eComp PointedCGWH.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e)
          (SymmetricDRight.obj k) ≫ i.hom =
            ((fullHomIso.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e)).hom ⊗ₘ
              (fullHomIso.{u, v} (SymmetricDRight.obj e) (SymmetricDRight.obj k)).hom) ≫
                eComp PointedCGWH.{u, v} (symmetricOperatorObj.{u, v} d)
                  (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} k))
    (fullHomIso_obj.{u, v} d k)
  have hj := congrArg
    (fun i : (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj e) ≅
      (symmetricOperatorObj.{u, v} d ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} e) =>
        eComp PointedCGWH.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e)
          (SymmetricDRight.obj k) ≫ (homIso.{u, v} d k).hom =
            (i.hom ⊗ₘ
              (fullHomIso.{u, v} (SymmetricDRight.obj e) (SymmetricDRight.obj k)).hom) ≫
                eComp PointedCGWH.{u, v} (symmetricOperatorObj.{u, v} d)
                  (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} k))
    (fullHomIso_obj.{u, v} d e)
  have hk := congrArg
    (fun i : (SymmetricDRight.obj e ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj k) ≅
      (symmetricOperatorObj.{u, v} e ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} k) =>
        eComp PointedCGWH.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e)
          (SymmetricDRight.obj k) ≫ (homIso.{u, v} d k).hom =
            ((homIso.{u, v} d e).hom ⊗ₘ i.hom) ≫
              eComp PointedCGWH.{u, v} (symmetricOperatorObj.{u, v} d)
                (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} k))
    (fullHomIso_obj.{u, v} e k)
  exact equation_transport (hi.trans (hj.trans hk))
    (homIso_composition_whole.{u, v} (SymmetricDRight.obj d)
      (SymmetricDRight.obj e) (SymmetricDRight.obj k))

end PointedCGWH.SymmetricDRightPoint
