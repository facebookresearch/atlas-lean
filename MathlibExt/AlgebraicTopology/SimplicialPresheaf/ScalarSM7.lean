/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanModel
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarTensorEndLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Scalar SM7 for the original injective Kan model

The supplied scalar tensor pushouts are evaluated at each original site
object. Their dual end pullbacks use the actual global injective lifting
classes and the original heterogeneous tensor/end adjunction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.MonoidalCategory HomotopicalAlgebra Opposite
open scoped MonoidalCategory SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def scalarCornerIso {A B K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    Arrow.mk sq.ι ≅ (Arrow.mk i □ Arrow.mk j) := by
  let c := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  change Arrow.mk sq.ι ≅ Arrow.mk c.ι
  let e : sq.pt ≅ c.pt := sq.isPushout.isoPushout
  have h : e.hom ≫ c.ι = sq.ι := by
    apply sq.hom_ext
    · dsimp only [e]
      rw [← Category.assoc, sq.isPushout.inl_isoPushout_hom]
      exact c.inl_ι.trans sq.inl_ι.symm
    · dsimp only [e]
      rw [← Category.assoc, sq.isPushout.inr_isoPushout_hom]
      exact c.inr_ι.trans sq.inr_ι.symm
  exact Arrow.isoMk e (Iso.refl _) (by
    change e.hom ≫ c.ι = sq.ι ≫ 𝟙 _
    simpa only [Category.comp_id] using h)

private theorem scalarCorner_cofibration {A B K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j)
    (hi : cofibrations SSet.{u} i) (hj : cofibrations SSet.{u} j) :
    cofibrations SSet.{u} sq.ι := by
  let : Cofibration i := (cofibration_iff i).mpr hi
  let : Cofibration j := (cofibration_iff j).mpr hj
  have hc : cofibrations SSet.{u} (Arrow.mk i □ Arrow.mk j).hom :=
    (cofibration_iff _).mp (SSet.cofibration_pushoutProduct i j)
  exact ((cofibrations SSet.{u}).arrow_mk_iso_iff (scalarCornerIso i j sq)).mpr hc

private theorem scalarCorner_trivial_left {A B K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j)
    (hi : trivialCofibrations SSet.{u} i) (hj : cofibrations SSet.{u} j) :
    trivialCofibrations SSet.{u} sq.ι := by
  let : Cofibration i := (cofibration_iff i).mpr hi.1
  let : WeakEquivalence i := (weakEquivalence_iff i).mpr hi.2
  let : Cofibration j := (cofibration_iff j).mpr hj
  have hc := SSet.pushoutProduct_mem_trivialCofibrations_of_left i j
  exact ((trivialCofibrations SSet.{u}).arrow_mk_iso_iff (scalarCornerIso i j sq)).mpr hc

private theorem scalarCorner_trivial_right {A B K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j)
    (hi : cofibrations SSet.{u} i) (hj : trivialCofibrations SSet.{u} j) :
    trivialCofibrations SSet.{u} sq.ι := by
  let : Cofibration i := (cofibration_iff i).mpr hi
  let : Cofibration j := (cofibration_iff j).mpr hj.1
  let : WeakEquivalence j := (weakEquivalence_iff j).mpr hj.2
  have hc := SSet.pushoutProduct_mem_trivialCofibrations_of_right i j
  exact ((trivialCofibrations SSet.{u}).arrow_mk_iso_iff (scalarCornerIso i j sq)).mpr hc

variable {D : Type w} [Category.{v} D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def evaluatedPushout {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j) (d : Dᵒᵖ) :
    (curriedTensor SSet.{u}).PushoutObjObj (i.app d) j where
  pt := pp.pt.obj d
  inl := pp.inl.app d
  inr := pp.inr.app d
  isPushout := by
    let ev := (evaluation Dᵒᵖ SSet.{u}).obj d
    have h := pp.isPushout.map ev
    change IsPushout (((scalarTensor.map i).app K).app d)
      (((scalarTensor.obj A).map j).app d) (pp.inl.app d) (pp.inr.app d) at h
    change IsPushout (i.app d ▷ K) (A.obj d ◁ j) (pp.inl.app d) (pp.inr.app d)
    simpa only [scalarTensor_presheaf_map, scalarTensor_scalar_map] using h
  ι := pp.ι.app d
  inl_ι := by
    have h := congrArg (fun f => f.app d) pp.inl_ι
    change pp.inl.app d ≫ pp.ι.app d = B.obj d ◁ j
    simpa only [NatTrans.comp_app, scalarTensor_scalar_map] using h
  inr_ι := by
    have h := congrArg (fun f => f.app d) pp.inr_ι
    change pp.inr.app d ≫ pp.ι.app d = i.app d ▷ L
    simpa only [NatTrans.comp_app, scalarTensor_presheaf_map] using h

variable [Small.{u} D] [LocallySmall.{u} D]

private theorem original_mono_of_cofibration {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (hi : cofibrations (SimplicialPresheaf.{u} D) i) : Mono i := by
  change (data D).model.categoryWithCofibrations.cofibrations i at hi
  rw [(data D).cofibrations_eq] at hi
  exact hi

private theorem original_cofibration_of_mono {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (hi : Mono i) : cofibrations (SimplicialPresheaf.{u} D) i := by
  change (data D).model.categoryWithCofibrations.cofibrations i
  rw [(data D).cofibrations_eq]
  exact hi

private theorem original_weak_iff {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) :
    weakEquivalences (SimplicialPresheaf.{u} D) i ↔
      ∀ d : Dᵒᵖ, SSet.realizationWeakEquivalences (i.app d) := by
  change (data D).model.categoryWithWeakEquivalences.weakEquivalences i ↔ _
  rw [(data D).weakEquivalences_eq]
  rfl

/-- Every supplied scalar tensor pushout of selected cofibrations is a
cofibration in the same original injective Kan model. -/
theorem scalar_pushoutObjObj_cofibration
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i)
    (hj : cofibrations SSet.{u} j) :
    cofibrations (SimplicialPresheaf.{u} D) pp.ι := by
  let : Mono i := original_mono_of_cofibration i hi
  have hm : Mono pp.ι := (NatTrans.mono_iff_mono_app pp.ι).mpr (by
    intro d
    let : Cofibration (i.app d) := SSet.modelCategoryQuillen.cofibration_of_mono _
    have hd : cofibrations SSet.{u} (pp.ι.app d) :=
      scalarCorner_cofibration (i.app d) j (evaluatedPushout i j pp d)
        (mem_cofibrations _) hj
    let : Cofibration (pp.ι.app d) := (cofibration_iff _).mpr hd
    exact SSet.modelCategoryQuillen.mono_of_cofibration _)
  exact original_cofibration_of_mono pp.ι hm

/-- The same supplied scalar tensor pushout is trivial when its original
presheaf map is a selected trivial cofibration. -/
theorem scalar_pushoutObjObj_trivialCofibration_of_left
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j)
    (hi : trivialCofibrations (SimplicialPresheaf.{u} D) i)
    (hj : cofibrations SSet.{u} j) :
    trivialCofibrations (SimplicialPresheaf.{u} D) pp.ι := by
  refine ⟨scalar_pushoutObjObj_cofibration i j pp hi.1 hj, ?_⟩
  apply (original_weak_iff pp.ι).mpr
  intro d
  let : Mono i := original_mono_of_cofibration i hi.1
  let : Cofibration (i.app d) := SSet.modelCategoryQuillen.cofibration_of_mono _
  have hid : trivialCofibrations SSet.{u} (i.app d) :=
    ⟨mem_cofibrations _, (original_weak_iff i).mp hi.2 d⟩
  have hd : trivialCofibrations SSet.{u} (pp.ι.app d) :=
    scalarCorner_trivial_left (i.app d) j (evaluatedPushout i j pp d) hid hj
  exact hd.2

/-- The same supplied scalar tensor pushout is trivial when its scalar
map is a selected Kan trivial cofibration. -/
theorem scalar_pushoutObjObj_trivialCofibration_of_right
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i)
    (hj : trivialCofibrations SSet.{u} j) :
    trivialCofibrations (SimplicialPresheaf.{u} D) pp.ι := by
  refine ⟨scalar_pushoutObjObj_cofibration i j pp hi hj.1, ?_⟩
  apply (original_weak_iff pp.ι).mpr
  intro d
  let : Mono i := original_mono_of_cofibration i hi
  let : Cofibration (i.app d) := SSet.modelCategoryQuillen.cofibration_of_mono _
  have hd : trivialCofibrations SSet.{u} (pp.ι.app d) :=
    scalarCorner_trivial_right (i.app d) j (evaluatedPushout i j pp d)
      (mem_cofibrations _) hj
  exact hd.2

/-- Every supplied original end pullback of a selected cofibration and
global injective fibration is a scalar Kan fibration. -/
theorem scalar_pullbackObjObj_fibration
    {A B X Y : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (p : X ⟶ Y) (pb : innerHomFunctor.PullbackObjObj i p)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i)
    (hp : fibrations (SimplicialPresheaf.{u} D) p) :
    fibrations SSet.{u} pb.π := by
  rw [← trivialCofibrations_rlp]
  intro K L j hj
  let pp := Functor.PushoutObjObj.ofHasPushout (scalarTensor (D := D)) i j
  have hpp := scalar_pushoutObjObj_trivialCofibration_of_right i j pp hi hj
  have hpRLP : (trivialCofibrations (SimplicialPresheaf.{u} D)).rlp p := by
    rwa [trivialCofibrations_rlp]
  exact ((scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff pp pb).mp
    (hpRLP pp.ι hpp)

/-- A trivial original cofibration gives a scalar trivial fibration in
the same supplied end pullback against any global injective fibration. -/
theorem scalar_pullbackObjObj_trivialFibration_of_left
    {A B X Y : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (p : X ⟶ Y) (pb : innerHomFunctor.PullbackObjObj i p)
    (hi : trivialCofibrations (SimplicialPresheaf.{u} D) i)
    (hp : fibrations (SimplicialPresheaf.{u} D) p) :
    trivialFibrations SSet.{u} pb.π := by
  rw [← cofibrations_rlp]
  intro K L j hj
  let pp := Functor.PushoutObjObj.ofHasPushout (scalarTensor (D := D)) i j
  have hpp := scalar_pushoutObjObj_trivialCofibration_of_left i j pp hi hj
  have hpRLP : (trivialCofibrations (SimplicialPresheaf.{u} D)).rlp p := by
    rwa [trivialCofibrations_rlp]
  exact ((scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff pp pb).mp
    (hpRLP pp.ι hpp)

/-- A global injective trivial fibration gives a scalar trivial
fibration in the same supplied end pullback against any cofibration. -/
theorem scalar_pullbackObjObj_trivialFibration_of_right
    {A B X Y : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (p : X ⟶ Y) (pb : innerHomFunctor.PullbackObjObj i p)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i)
    (hp : trivialFibrations (SimplicialPresheaf.{u} D) p) :
    trivialFibrations SSet.{u} pb.π := by
  rw [← cofibrations_rlp]
  intro K L j hj
  let pp := Functor.PushoutObjObj.ofHasPushout (scalarTensor (D := D)) i j
  have hpp := scalar_pushoutObjObj_cofibration i j pp hi hj
  have hpRLP : (cofibrations (SimplicialPresheaf.{u} D)).rlp p := by
    rwa [cofibrations_rlp]
  exact ((scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff pp pb).mp
    (hpRLP pp.ι hpp)

end SimplicialPresheaf.InjectiveKan
