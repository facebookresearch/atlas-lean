/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.TotalComparisonBoxDivision
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalWhitehead
import MathlibExt.AlgebraicTopology.SimplicialSpace.TotalRightLocality
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexQuillenAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalCartesianModel
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFibrantCriterion

/-!
# The actual total complete-Segal to Joyal Quillen pair

The original box generators, whole-arrow total/product comparisons and genuine
k Quillen pair first give the global Reedy Quillen pair. Its fibrant-object
preservation and the full original locality theorem make the literal right
image complete Segal. A factorization and retract on the original arrow then
give the Rezk Quillen pair through the native fibrant-object criterion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory MorphismProperty
open scoped Simplicial SimplicialSpace.Inner MonoidalCategory

namespace SimplicialSpace.TotalSpace

private def mappedProductSquare
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : (curriedTensor SSet.{u}).PushoutObjObj a b) :
    (curriedTensor SSet.{u} ⋙
      (Functor.whiskeringRight SSet.{u} SSet.{u} JoyalSSet.{u}).obj
        JoyalSSet.ofSSet).PushoutObjObj a b where
  pt := JoyalSSet.ofSSet.obj sq.pt
  inl := JoyalSSet.ofSSet.map sq.inl
  inr := JoyalSSet.ofSSet.map sq.inr
  isPushout := sq.isPushout.map JoyalSSet.ofSSet
  ι := JoyalSSet.ofSSet.map sq.ι
  inl_ι := by rw [← CategoryTheory.Functor.map_comp, sq.inl_ι]; rfl
  inr_ι := by rw [← CategoryTheory.Functor.map_comp, sq.inr_ι]; rfl

private def joyalProductSquare
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : (curriedTensor SSet.{u}).PushoutObjObj a b) :
    (curriedTensor JoyalSSet.{u}).PushoutObjObj
      (JoyalSSet.ofSSet.map a) (JoyalSSet.ofSSet.map b) := by
  let t := (mappedProductSquare sq).ofNatIso
    (CartesianMonoidalCategory.prodComparisonBifunctorNatIso JoyalSSet.ofSSet.{u})
  exact {
    pt := t.pt
    inl := t.inl
    inr := t.inr
    isPushout := t.isPushout
    ι := t.ι
    inl_ι := t.inl_ι
    inr_ι := t.inr_ι }

private def productArrowIso
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : (curriedTensor SSet.{u}).PushoutObjObj a b) :
    Arrow.mk (JoyalSSet.ofSSet.map sq.ι) ≅
      Arrow.mk ((Arrow.mk (JoyalSSet.ofSSet.map a) □
        Arrow.mk (JoyalSSet.ofSSet.map b)).hom) := by
  let e := CartesianMonoidalCategory.prodComparisonBifunctorNatIso JoyalSSet.ofSSet.{u}
  let t := joyalProductSquare sq
  let α : Arrow.mk (JoyalSSet.ofSSet.map sq.ι) ≅ Arrow.mk t.ι :=
    Arrow.isoMk (Iso.refl _) ((e.app A').app B') (by
      change 𝟙 _ ≫ (JoyalSSet.ofSSet.map sq.ι ≫ (e.hom.app A').app B') = _
      rw [Category.id_comp]
      rfl)
  let canonical := Functor.PushoutObjObj.ofHasPushout (curriedTensor JoyalSSet.{u})
    (JoyalSSet.ofSSet.map a) (JoyalSSet.ofSSet.map b)
  let β : Arrow.mk t.ι ≅ Arrow.mk canonical.ι :=
    Functor.PushoutObjObj.ι_iso_of_iso_left
      (F := curriedTensor JoyalSSet.{u})
      (f₁ := Arrow.mk (JoyalSSet.ofSSet.map a))
      (f₁' := Arrow.mk (JoyalSSet.ofSSet.map a))
      (f₂ := Arrow.mk (JoyalSSet.ofSSet.map b)) t canonical (Iso.refl _)
  change Arrow.mk (JoyalSSet.ofSSet.map sq.ι) ≅ Arrow.mk canonical.ι
  exact α ≪≫ β

private def asBoxSquare
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : innerTensorBifunctor.PushoutObjObj (discreteInnerFunctor.map a) b) :
    boxProduct.PushoutObjObj a b where
  pt := sq.pt
  inl := sq.inl
  inr := sq.inr
  isPushout := sq.isPushout
  ι := sq.ι
  inl_ι := sq.inl_ι
  inr_ι := sq.inr_ι

private theorem box_image_property
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : boxProduct.PushoutObjObj a b) (P : MorphismProperty JoyalSSet.{u})
    [P.RespectsIso]
    (h : P ((Arrow.mk (JoyalSSet.ofSSet.map a) □
      Arrow.mk (SSet.FreeGroupoidSimplex.kLeft.map b)).hom)) :
    P (left.map sq.ι) := by
  let t := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    a (SSet.FreeGroupoidSimplex.kFunctor.map b)
  exact (P.arrow_mk_iso_iff (boxPushoutArrowIso sq t ≪≫ productArrowIso t)).2 h

private theorem boundary_image_cofibration (m n : ℕ) :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    cofibrations JoyalSSet.{u} (left.map (ReedyGeneratingFamilies.boundaryPushout.{u} m n).ι) := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : IsClosedSymmetricMonoidalModelCategory JoyalSSet.{u} :=
    JoyalSSet.isClosedSymmetricMonoidalModelCategory
  apply box_image_property
    (asBoxSquare (ReedyGeneratingFamilies.boundaryPushout.{u} m n))
  apply IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
  · change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations
      (JoyalSSet.ofSSet.map (SSet.boundary.{u} m).ι)
    rw [JoyalSSet.modelCategory_cofibrations]
    change Mono (JoyalSSet.ofSSet.map (SSet.boundary.{u} m).ι)
    infer_instance
  · apply SSet.FreeGroupoidSimplex.kWrappedAdjunction_isQuillenAdjunction.preservesCofibrations
    change Mono (SSet.boundary.{u} n).ι
    infer_instance

private theorem horn_image_trivialCofibration (m : ℕ)
    (n : {n : ℕ // 1 ≤ n}) (i : Fin (n.val + 1)) :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    trivialCofibrations JoyalSSet.{u}
      (left.map (ReedyGeneratingFamilies.hornPushout.{u} m n i).ι) := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : IsClosedSymmetricMonoidalModelCategory JoyalSSet.{u} :=
    JoyalSSet.isClosedSymmetricMonoidalModelCategory
  let _ : NeZero n.val := ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one n.property)⟩
  have hb : trivialCofibrations SSet.{u} (SSet.horn.{u} n.val i).ι := by
    rw [← llp_eq_of_wfs (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
    intro X Y p hp
    let _ : Fibration p := (HomotopicalAlgebra.fibration_iff p).2 hp
    exact ((SSet.modelCategoryQuillen.fibration_iff p).1 inferInstance)
      _ (SSet.modelCategoryQuillen.horn_ι_mem_J n.val i)
  apply box_image_property
    (asBoxSquare (ReedyGeneratingFamilies.hornPushout.{u} m n i))
  apply IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
  · change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations
      (JoyalSSet.ofSSet.map (SSet.boundary.{u} m).ι)
    rw [JoyalSSet.modelCategory_cofibrations]
    change Mono (JoyalSSet.ofSSet.map (SSet.boundary.{u} m).ι)
    infer_instance
  · exact
      SSet.FreeGroupoidSimplex.kWrappedAdjunction_isQuillenAdjunction.preservesTrivialCofibrations
      _ hb

private theorem reedy_adjunction_isQuillen :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    adjunction.{u}.IsQuillenAdjunction := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro Q Q' p hp
    rw [← ReedyGeneratingFamilies.J_rlp_eq_fibrations]
    rintro A B j ⟨h⟩
    let j := (ReedyGeneratingFamilies.hornFamily.{u} h).hom
    have hj := horn_image_trivialCofibration.{u} h.1 h.2.1 h.2.2
    exact (adjunction.hasLiftingProperty_iff j p).1
      (hasLiftingProperty_of_wfs (left.map j) p hj hp)
  · intro Q Q' p hp
    rw [← ReedyGeneratingFamilies.I_rlp_eq_trivialFibrations]
    rintro A B j ⟨b⟩
    let j := (ReedyGeneratingFamilies.boundaryFamily.{u} b).hom
    have hj := boundary_image_cofibration.{u} b.1 b.2
    exact (adjunction.hasLiftingProperty_iff j p).1
      (hasLiftingProperty_of_wfs (left.map j) p hj hp)


/-- The literal total right image has every original Reedy matching condition,
including degree zero, when its original target is a quasicategory. -/
theorem right_reedyFibrant_of_quasicategory (Q : JoyalSSet.{u})
    [SSet.Quasicategory Q.toSSet] :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant (right.obj Q) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : adjunction.{u}.IsQuillenAdjunction := reedy_adjunction_isQuillen
  exact (Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := adjunction)).isFibrant ((JoyalSSet.isFibrant_iff_quasicategory Q).2 inferInstance)

/-- The same literal total right image satisfies all original spine and full-E
locality conditions in addition to global Reedy fibrancy. -/
theorem right_completeSegalSpaces_of_quasicategory (Q : JoyalSSet.{u})
    [SSet.Quasicategory Q.toSSet] : completeSegalSpaces (right.obj Q) :=
  ⟨right_reedyFibrant_of_quasicategory Q, right_localizingMap_realizationWeak Q⟩

private theorem reedyFibration_between_css
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
    (hX : completeSegalSpaces X) (hY : completeSegalSpaces Y)
    (hp : ReedyModel.modelCategory.categoryWithFibrations.fibrations p) :
    RezkModel.modelCategory.categoryWithFibrations.fibrations p := by
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let d := factorizationData (trivialCofibrations SimplicialSpace.{u})
    (fibrations SimplicialSpace.{u}) p
  let _ : IsFibrant Y := (RezkModel.isFibrant_iff_completeSegalSpaces Y).2 hY
  let _ : Fibration d.p := (HomotopicalAlgebra.fibration_iff d.p).2 d.hp
  have hZ : completeSegalSpaces d.Z :=
    (RezkModel.isFibrant_iff_completeSegalSpaces d.Z).1 (isFibrant_of_fibration d.p)
  have hmono : Mono d.i := by
    have h := d.hi.1
    change RezkModel.modelCategory.categoryWithCofibrations.cofibrations d.i at h
    rw [RezkModel.modelCategory_cofibrations] at h
    exact h
  have hweak : rezkWeakEquivalences d.i := by
    have h := d.hi.2
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences d.i at h
    rw [RezkModel.modelCategory_weakEquivalences] at h
    exact h
  have hlp : HasLiftingProperty d.i p := by
    let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    have hiC : cofibrations SimplicialSpace.{u} d.i :=
      (HomotopicalAlgebra.cofibration_iff d.i).1
        ((ReedyModel.cofibration_iff d.i).2 hmono)
    have hiW : WeakEquivalence d.i :=
      (rezkWeak_iff_reedyWeak_of_completeSegalSpaces d.i hX hZ).1 hweak
    have hiTC : trivialCofibrations SimplicialSpace.{u} d.i :=
      ⟨hiC, (HomotopicalAlgebra.weakEquivalence_iff d.i).1 hiW⟩
    have hpR : fibrations SimplicialSpace.{u} p := hp
    exact hasLiftingProperty_of_wfs d.i p hiTC hpR
  let _ : HasLiftingProperty d.i p := hlp
  let sq : CommSq (𝟙 X) d.i p d.p :=
    ⟨by simpa only [Category.id_comp] using d.fac.symm⟩
  let retract : RetractArrow p d.p := {
    i := Arrow.homMk d.i (𝟙 Y) (by
      change d.i ≫ d.p = p ≫ 𝟙 Y
      rw [Category.comp_id]
      exact d.fac)
    r := Arrow.homMk sq.lift (𝟙 Y) (by
      change sq.lift ≫ p = d.p ≫ 𝟙 Y
      rw [Category.comp_id]
      exact sq.fac_right)
    retract := by
      ext
      · exact sq.fac_left
      · simp }
  exact (fibrations SimplicialSpace.{u}).of_retract retract d.hp

/-- The original total adjunction is Quillen for the actual Rezk and Joyal
models, without a caller model or preservation/completeness outcome. -/
theorem adjunction_isQuillen :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    adjunction.{u}.IsQuillenAdjunction := by
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  have hL : PreservesCofibrations left.{u} := by
    intro X Y f hf
    have hm : Mono f := by
      change RezkModel.modelCategory.categoryWithCofibrations.cofibrations f at hf
      rw [RezkModel.modelCategory_cofibrations] at hf
      exact hf
    have hReedy : ReedyModel.modelCategory.categoryWithCofibrations.cofibrations f := by
      let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
      exact (HomotopicalAlgebra.cofibration_iff f).1 ((ReedyModel.cofibration_iff f).2 hm)
    have hImage : cofibrations JoyalSSet.{u} (left.map f) := by
      let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
      exact reedy_adjunction_isQuillen.preservesCofibrations f hReedy
    exact hImage
  have hR : PreservesFibrationsBetweenFibrantObjects right.{u} := by
    intro Q Q' p hp
    let _ : SSet.Quasicategory Q.toSSet := (JoyalSSet.isFibrant_iff_quasicategory Q).1 hp.2.1
    let _ : SSet.Quasicategory Q'.toSSet := (JoyalSSet.isFibrant_iff_quasicategory Q').1 hp.2.2
    have hReedy : ReedyModel.modelCategory.categoryWithFibrations.fibrations (right.map p) := by
      let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
      let _ : adjunction.{u}.IsQuillenAdjunction := reedy_adjunction_isQuillen
      exact (Adjunction.IsQuillenAdjunction.preservesFibrations
        (adj := adjunction)).map_fibration hp.1
    exact reedyFibration_between_css (right.map p)
      (right_completeSegalSpaces_of_quasicategory Q)
      (right_completeSegalSpaces_of_quasicategory Q') hReedy
  exact
      Adjunction.IsQuillenAdjunction.mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects hL
      hR

end SimplicialSpace.TotalSpace
