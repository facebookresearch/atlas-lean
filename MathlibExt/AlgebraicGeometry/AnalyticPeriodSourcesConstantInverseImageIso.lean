/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticProEtaleCoefficientSources
public import MathlibExt.CategoryTheory.NativeRingInverseImages

import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Final

/-!
# Constant inverse images on the analytic pro-étale site

The canonical inverse-image map for constant ring sheaves is an isomorphism.

Sources: Scholze, arXiv:1205.3463v2, Definitions 3.9, 6.1, 6.8 and 8.1;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticPeriodSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry AnalyticTateAdicModels AnalyticProObjectSites
open AnalyticProEtaleCoefficientSources MathlibExt.CategoryTheory

private noncomputable def constantWhiskerEquiv
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {A : Type*} [Category* A] (G : C ⥤ D) [G.Initial]
    (R : A) (F : D ⥤ A) :
    ((Functor.const D).obj R ⟶ F) ≃ ((Functor.const C).obj R ⟶ G ⋙ F) where
  toFun η := Functor.whiskerLeft G η
  invFun η := (Functor.Initial.extendCone.obj (Cone.mk R η)).π
  left_inv η := by
    ext Y
    change η.app (G.obj (Functor.Initial.lift G Y)) ≫
      F.map (Functor.Initial.homToLift G Y) = η.app Y
    simpa using (η.naturality (Functor.Initial.homToLift G Y)).symm
  right_inv η := by
    ext X
    exact Functor.Initial.limit_cone_comp_aux (Cone.mk R η) X

private theorem constantInverseMap_isIso
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D}
    (G : C ⥤ D) [G.IsContinuous J T] [G.op.Initial]
    [(G.sheafPushforwardContinuous CommRingCat.{1} J T).IsRightAdjoint]
    [HasSheafify J CommRingCat.{1}] [HasSheafify T CommRingCat.{1}]
    (R : Type) [CommRing R] :
    IsIso (NativeRingInverseImages.constantInverseMap (J := J) (T := T) G R) := by
  apply isIso_of_coyoneda_map_bijective
  intro O
  let A := CommRingCat.of (ULift.{1} R)
  let eT := (sheafificationAdjunction T CommRingCat.{1}).homEquiv
    ((Functor.const Dᵒᵖ).obj A) O
  let eJ := (sheafificationAdjunction J CommRingCat.{1}).homEquiv
    ((Functor.const Cᵒᵖ).obj A) ((G.sheafPushforwardContinuous CommRingCat.{1} J T).obj O)
  let eG := (G.sheafAdjunctionContinuous CommRingCat.{1} J T).homEquiv
    (SheafScalarQuotients.constantRing (J := J) R) O
  let e := ((eT.trans (constantWhiskerEquiv G.op A O.obj)).trans eJ.symm).trans eG.symm
  have he :
      (fun f => NativeRingInverseImages.constantInverseMap (J := J) (T := T) G R ≫ f) = e := by
    funext f
    apply eG.injective
    apply eJ.injective
    change eJ (eG (NativeRingInverseImages.constantInverseMap (J := J) (T := T) G R ≫ f)) =
      eJ (eG (eG.symm (eJ.symm (constantWhiskerEquiv G.op A O.obj (eT f)))))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change eJ (eG (NativeRingInverseImages.constantInverseMap (J := J) (T := T) G R ≫ f)) =
      Functor.whiskerLeft G.op (eT f)
    dsimp only [eG]
    rw [Adjunction.homEquiv_naturality_right]
    change eJ (((G.sheafAdjunctionContinuous CommRingCat.{1} J T).homEquiv _ _)
      (((G.sheafAdjunctionContinuous CommRingCat.{1} J T).homEquiv _ _).symm
        (NativeRingInverseImages.constantPush (J := J) (T := T) G R)) ≫ _) = _
    rw [Equiv.apply_symm_apply]
    dsimp only [eJ]
    rw [Adjunction.homEquiv_naturality_right]
    dsimp only [NativeRingInverseImages.constantPush, A]
    rw [Equiv.apply_symm_apply]
    dsimp only [eT]
    rw [Adjunction.homEquiv_unit]
    ext U
    rfl
  rw [he]
  exact e.bijective

private theorem etaleInclusion_op_initial (p : ℕ) [Fact p.Prime] (X : AnalyticAdicSpace p) :
    (AnalyticProEtaleCoefficientSources.etaleInclusion p X).op.Initial := by
  let Y := ObjectProperty.lift (IsProEtaleObject p X) yoneda
    (fun U ↦ ⟨etalePresentation p X U.unop⟩)
  have : Y.Initial := by
    constructor
    intro U
    have : IsFiltered (CostructuredArrow yoneda U.obj) :=
      (IsIndObject.mk (Classical.choice U.property).ind).isFiltered
    have : IsConnected (CostructuredArrow
        (Y ⋙ ObjectProperty.ι (IsProEtaleObject p X))
        ((ObjectProperty.ι (IsProEtaleObject p X)).obj U)) := by
      change IsConnected (CostructuredArrow yoneda U.obj)
      exact IsFiltered.isConnected _
    exact isConnected_of_equivalent
      (CostructuredArrow.post Y (ObjectProperty.ι (IsProEtaleObject p X)) U).asEquivalence.symm
  change ((opOpEquivalence (AnalyticProObjectSites.Etale p X)).inverse.op ⋙ Y.op.op).Initial
  infer_instance

variable (p : ℕ) [Fact p.Prime]

section AnalyticSpace

variable (X : AnalyticAdicSpace p) (hX : AnalyticProObjectSites.IsLocallyNoetherian p X)

include hX

variable (P : AnalyticProObjectSites.PointRealization p X)

section RingSources

variable [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) CommRingCat.{1}]
  [HasSheafify (proTopology p X P) CommRingCat.{1}]
  [(etaleInclusion p X).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)]
  [((etaleInclusion p X).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)).IsRightAdjoint]

/-- The native constant inverse-image map; its construction already lives in MathlibExt. -/
public theorem constantInverseImageIso
    (hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X) (R : Type) [CommRing R] :
  IsIso (NativeRingInverseImages.constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (T := proTopology p X P)
      (etaleInclusion p X) R)
    := by
  cases Subsingleton.elim hX hNoeth
  have := etaleInclusion_op_initial p X
  exact constantInverseMap_isIso (etaleInclusion p X) R

end RingSources

end AnalyticSpace

end WantedExt.AlgebraicGeometry.AnalyticPeriodSources
