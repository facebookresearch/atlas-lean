/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.InternalHomSourceWeakEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedSuspensionLoop
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedAdjunction
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHProper
import MathlibExt.Topology.Category.CGWH.PathLanding
import MathlibExt.Topology.Category.PointedCGWH.LoopComparison

/-!
# Native based paths and chosen derived loops in pointed CGWH spaces

The native based-path cospan provides a functorial common homotopy-pullback
target for the chosen homotopy-fiber loop and the strict sphere-one loop.
Both point-set legs are weak equivalences.  They are inverted only after
formal localization.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open CategoryTheory.MonoidalCategory
open scoped CGWH.modelCategory MonoidalCategory ZeroObject

namespace PointedCGWH

set_option backward.isDefEq.respectTransparency false in
private noncomputable def diskBoundarySourceIsoSphereZero :
    PointedCGWH.sphereZero.{u, v} ≅
      (CategoryTheory.Arrow.mk
        PointedCGWH.diskBoundary.{u, v}).left := by
  change PointedCGWH.sphereZero.{u, v} ≅
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
  exact Under.isoMk (Iso.refl _) (by
    dsimp [PointedCGWH.sphereZero,
      CategoryTheory.Pointed.smashUnit]
    simp [Under.costar_obj_hom])

set_option backward.isDefEq.respectTransparency false in
private noncomputable def preNatIsoOfIso
    {A B : PointedCGWH.{u, v}} (e : A ≅ B) :
    PointedCGWH.power B ≅ PointedCGWH.power A :=
  NatIso.ofComponents
    (fun X =>
      { hom := (MonoidalClosed.pre e.hom).app X
        inv := (MonoidalClosed.pre e.inv).app X
        hom_inv_id := by
          change (MonoidalClosed.pre e.hom).app X ≫
              (MonoidalClosed.pre e.inv).app X =
            𝟙 ((ihom B).obj X)
          rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map,
            e.inv_hom_id, MonoidalClosed.pre_id, NatTrans.id_app]
        inv_hom_id := by
          change (MonoidalClosed.pre e.inv).app X ≫
              (MonoidalClosed.pre e.hom).app X =
            𝟙 ((ihom A).obj X)
          rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map,
            e.hom_inv_id, MonoidalClosed.pre_id, NatTrans.id_app] })
    (fun f => (MonoidalClosed.pre e.hom).naturality f)

private noncomputable def endpointPowerIso :
    PointedCGWH.power
        (CategoryTheory.Arrow.mk
          PointedCGWH.diskBoundary.{u, v}).left ≅
      𝟭 PointedCGWH.{u, v} :=
  preNatIsoOfIso diskBoundarySourceIsoSphereZero ≪≫
    (MonoidalClosed.unitNatIso
      (C := PointedCGWH.{u, v})).symm

private noncomputable def smashZeroLeftIsInitial (A : PointedCGWH.{u, v}) :
    IsInitial
      (((PointedCGWH.smash).obj
        (0 : PointedCGWH.{u, v})).obj A) := by
  let adj := PointedCGWH.smashBasedHomAdjunction A
  have h : IsInitial
      (((PointedCGWH.smash).obj A).obj
        (0 : PointedCGWH.{u, v})) :=
    IsInitial.ofUniqueHom
      (fun X => (adj.homEquiv _ _).symm
        (HasZeroObject.zeroIsInitial.to _))
      (fun X f => by
        apply (adj.homEquiv _ _).injective
        apply HasZeroObject.zeroIsInitial.hom_ext)
  exact h.ofIso (β_ (0 : PointedCGWH.{u, v}) A).symm

private noncomputable def powerZeroIsTerminal
    (X : PointedCGWH.{u, v}) :
    IsTerminal
      ((PointedCGWH.power (0 : PointedCGWH.{u, v})).obj X) := by
  let adj := PointedCGWH.smashBasedHomAdjunction
    (0 : PointedCGWH.{u, v})
  exact IsTerminal.ofUniqueHom
    (fun A => adj.homEquiv A X ((smashZeroLeftIsInitial A).to X))
    (fun A f => by
      apply (adj.homEquiv A X).symm.injective
      apply (smashZeroLeftIsInitial A).hom_ext)

private noncomputable def zeroPowerIso :
    (Functor.const PointedCGWH.{u, v}).obj
        (0 : PointedCGWH.{u, v}) ≅
      PointedCGWH.power (0 : PointedCGWH.{u, v}) :=
  NatIso.ofComponents
    (fun X => (isZero_zero PointedCGWH.{u, v}).isTerminal.uniqueUpToIso
      (powerZeroIsTerminal X))
    (fun _f => (powerZeroIsTerminal _).hom_ext _ _)

private noncomputable def terminalPowerIso :
    (Functor.const PointedCGWH.{u, v}).obj
        (0 : PointedCGWH.{u, v}) ≅
      PointedCGWH.power (⊤_ PointedCGWH.{u, v}) :=
  zeroPowerIso ≪≫
    preNatIsoOfIso
      (HasZeroObject.zeroIsoTerminal
        (C := PointedCGWH.{u, v})).symm

/-- Native based paths are based internal Homs from the native one-disk. -/
noncomputable def basedPath :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.power PointedCGWH.diskOne

/-- Evaluate a native based path at its free endpoint. -/
noncomputable def basedPathEndpoint :
    PointedCGWH.basedPath.{u, v} ⟶ 𝟭 PointedCGWH.{u, v} :=
  MonoidalClosed.pre PointedCGWH.diskBoundary ≫
    endpointPowerIso.hom

/-- The constant native based path at the selected point. -/
noncomputable def basedPathPoint :
    (Functor.const PointedCGWH.{u, v}).obj
        (0 : PointedCGWH.{u, v}) ⟶
      PointedCGWH.basedPath.{u, v} :=
  terminalPowerIso.hom ≫
    MonoidalClosed.pre PointedCGWH.diskAugmentation

private theorem basedPathEndpoint_eq :
    PointedCGWH.basedPathEndpoint.{u, v} =
      MonoidalClosed.pre PointedCGWH.diskBoundary ≫
        endpointPowerIso.hom :=
  rfl

private theorem basedPathPoint_eq :
    PointedCGWH.basedPathPoint.{u, v} =
      terminalPowerIso.hom ≫
        MonoidalClosed.pre PointedCGWH.diskAugmentation :=
  rfl

private noncomputable def basedPathEvBase
    (X : PointedCGWH.{u, v}) :
    (ihom PointedCGWH.diskOne.{u, v}.right).obj X.right ⟶ X.right :=
  (λ_ _).inv ≫
    ((CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
      CGWH.point_isTerminal).hom ▷ _) ≫
    (PointedCGWH.diskOne.{u, v}.hom ▷ _) ≫
    (ihom.ev PointedCGWH.diskOne.{u, v}.right).app X.right

set_option backward.isDefEq.respectTransparency false in
private theorem basedPathEvBase_eq_pathEvalOne
    (X : PointedCGWH.{u, v}) :
    basedPathEvBase X = CGWH.pathEvalOne.app X.right := by
  unfold basedPathEvBase CGWH.pathEvalOne
  have hUnit :
      (CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
          CGWH.point_isTerminal).hom =
        CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) :=
    CGWH.point_isTerminal.hom_ext _ _
  rw [hUnit]
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  rfl

/-- Forgetting the based condition turns a native based path into the
underlying native path. -/
noncomputable def basedPathToPath :
    PointedCGWH.basedPath.{u, v} ⋙
        PointedCGWH.pointedToCGWH.{u, v} ⟶
      PointedCGWH.pointedToCGWH.{u, v} ⋙ CGWH.path.{u, v} where
  app X := pullback.fst (basedPathEvBase X) X.hom
  naturality X Y f := by
    have hEv : basedPathEvBase X ≫ f.right =
        (ihom PointedCGWH.diskOne.right).map f.right ≫
          basedPathEvBase Y := by
      rw [basedPathEvBase_eq_pathEvalOne,
        basedPathEvBase_eq_pathEvalOne]
      exact (CGWH.pathEvalOne.naturality f.right).symm
    have hPoint : X.hom ≫ f.right =
        𝟙 CGWH.point ≫ Y.hom := by
      rw [Category.id_comp]
      exact Under.w f
    set_option backward.isDefEq.respectTransparency false in
      change (pullback.map (basedPathEvBase X) X.hom
          (basedPathEvBase Y) Y.hom
          ((ihom PointedCGWH.diskOne.right).map f.right)
          (𝟙 CGWH.point) f.right hEv hPoint) ≫
          pullback.fst (basedPathEvBase Y) Y.hom =
        pullback.fst (basedPathEvBase X) X.hom ≫
          (ihom PointedCGWH.diskOne.right).map f.right
    simp only [pullback.map, pullback.lift_fst]

/-- Forgetting a native based path and evaluating at time zero gives its
free endpoint. -/
theorem basedPathToPath_evalZero (X : PointedCGWH.{u, v}) :
    PointedCGWH.basedPathToPath.app X ≫
      CGWH.pathEvalZero.app X.right =
      (PointedCGWH.basedPathEndpoint.app X).right := by
  let f : PointedCGWH.sphereZero.{u, v} ⟶
      PointedCGWH.diskOne.{u, v} :=
    diskBoundarySourceIsoSphereZero.hom ≫ PointedCGWH.diskBoundary
  have hEndpoint : PointedCGWH.basedPathEndpoint.{u, v} =
      MonoidalClosed.pre f ≫ MonoidalClosed.unitNatIso.inv := by
    rw [basedPathEndpoint_eq]
    unfold endpointPowerIso preNatIsoOfIso
    change MonoidalClosed.pre PointedCGWH.diskBoundary ≫
        (MonoidalClosed.pre diskBoundarySourceIsoSphereZero.hom ≫
          MonoidalClosed.unitNatIso.inv) =
      MonoidalClosed.pre f ≫ MonoidalClosed.unitNatIso.inv
    rw [← Category.assoc, ← MonoidalClosed.pre_map]
  rw [hEndpoint]
  simp only [Functor.comp_obj, Under.forget_obj, NatTrans.comp_app,
    Under.comp_right]
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : HasPullbacks CGWH.{u, v} := by
    let _ : HasLimitsOfSize.{v, v} CompactlyGenerated.{u, v} :=
      CategoryTheory.hasLimits_of_coreflective
        CompactlyGenerated.compactlyGeneratedToTop
    let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} :=
      CategoryTheory.hasLimits_of_reflective
        CGWH.cgwhToCompactlyGenerated
    infer_instance
  have hSourceIso : diskBoundarySourceIsoSphereZero.hom.right =
      𝟙 (CategoryTheory.Arrow.mk
        PointedCGWH.diskBoundary.{u, v}).left.right := by
    unfold diskBoundarySourceIsoSphereZero
    rfl
  have hFreeSource :
      (coprod.inr : CGWH.point.{u, v} ⟶
          (CategoryTheory.Arrow.mk
            PointedCGWH.diskBoundary.{u, v}).left.right) ≫
          diskBoundarySourceIsoSphereZero.hom.right =
        (coprod.inr : CGWH.point.{u, v} ⟶
          (CategoryTheory.Arrow.mk
            PointedCGWH.diskBoundary.{u, v}).left.right) := by
    rw [hSourceIso]
    exact Category.comp_id _
  have hFree :
      (coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ f.right =
        CGWH.intervalZero.{u, v} := by
    dsimp only [f, Under.comp_right]
    calc
      _ = ((coprod.inr : CGWH.point.{u, v} ⟶
              (CategoryTheory.Arrow.mk
                PointedCGWH.diskBoundary.{u, v}).left.right) ≫
            diskBoundarySourceIsoSphereZero.hom.right) ≫
          PointedCGWH.diskBoundary.right :=
        (Category.assoc _ _ _).symm
      _ = (coprod.inr : CGWH.point.{u, v} ⟶
            (CategoryTheory.Arrow.mk
              PointedCGWH.diskBoundary.{u, v}).left.right) ≫
          PointedCGWH.diskBoundary.right := congrArg
          (fun k => k ≫ PointedCGWH.diskBoundary.right) hFreeSource
      _ = _ := by
        simp [PointedCGWH.diskBoundary, CGWH.intervalZero]
        rfl
  have hCarrierMap : PointedCGWH.basedPathToPath.app X =
      (CategoryTheory.Pointed.basedInternalHomToInternalHom
        CGWH.point CGWH.point_isTerminal PointedCGWH.diskOne).app X := by
    rfl
  have hPathZero : CGWH.pathEvalZero.app X.right =
      (λ_ (CGWH.path.obj X.right)).inv ≫
        (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ▷
          CGWH.path.obj X.right) ≫
        (CGWH.intervalZero ▷ CGWH.path.obj X.right) ≫
        (ihom.ev CGWH.interval).app X.right := by
    unfold CGWH.pathEvalZero
    rw [← MonoidalCategory.comp_whiskerRight_assoc]
  have hCarrier :=
    CategoryTheory.Pointed.basedInternalHom_pre_unit_carrier
      CGWH.point CGWH.point_isTerminal PointedCGWH.diskOne X f
  rw [← Under.comp_right]
  rw [hCarrier]
  rw [hFree]
  have hUnit :
      (CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
          CGWH.point_isTerminal).hom =
        CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) :=
    CGWH.point_isTerminal.hom_ext _ _
  rw [hUnit]
  rw [← hCarrierMap]
  rw [hPathZero]
  rfl

/-- Forgetting a native based path and evaluating at time one gives its
selected endpoint. -/
theorem basedPathToPath_evalOne (X : PointedCGWH.{u, v}) :
    PointedCGWH.basedPathToPath.app X ≫
        CGWH.pathEvalOne.app X.right =
      CGWH.point_isTerminal.from
          (PointedCGWH.basedPath.obj X).right ≫ X.hom := by
  rw [← basedPathEvBase_eq_pathEvalOne]
  change pullback.fst (basedPathEvBase X) X.hom ≫ basedPathEvBase X = _
  rw [pullback.condition]
  exact congrArg (fun k => k ≫ X.hom)
    (CGWH.point_isTerminal.hom_ext _ _)

/-- The public native based-path projections exhibit their carrier as the
pullback of endpoint evaluation along the selected point. -/
noncomputable def basedPathToPathIsLimit
    (X : PointedCGWH.{u, v}) :
    IsLimit
      (PullbackCone.mk
        (PointedCGWH.basedPathToPath.app X)
        (CGWH.point_isTerminal.from
          (PointedCGWH.basedPath.obj X).right)
        (PointedCGWH.basedPathToPath_evalOne X)) := by
  let hOld := pullbackIsPullback (basedPathEvBase X) X.hom
  let oldCone
      (s : PullbackCone (CGWH.pathEvalOne.app X.right) X.hom) :
      PullbackCone (basedPathEvBase X) X.hom :=
    PullbackCone.mk s.fst s.snd (by
      rw [basedPathEvBase_eq_pathEvalOne]
      exact s.condition)
  let lift (s : PullbackCone (CGWH.pathEvalOne.app X.right) X.hom) :
      s.pt ⟶ (PointedCGWH.basedPath.obj X).right :=
    hOld.lift (oldCone s)
  apply PullbackCone.IsLimit.mk
      (PointedCGWH.basedPathToPath_evalOne X) lift
  · intro s
    dsimp only [lift]
    change hOld.lift (oldCone s) ≫
      pullback.fst (basedPathEvBase X) X.hom = s.fst
    have hfac := hOld.fac (oldCone s) WalkingCospan.left
    change hOld.lift (oldCone s) ≫
      pullback.fst (basedPathEvBase X) X.hom = s.fst at hfac
    exact hfac
  · intro s
    exact CGWH.point_isTerminal.hom_ext _ _
  · intro s m hm1 hm2
    dsimp only [lift]
    apply PullbackCone.IsLimit.hom_ext hOld
    · have hm1' :
          m ≫ pullback.fst (basedPathEvBase X) X.hom = s.fst := by
        change m ≫ PointedCGWH.basedPathToPath.app X = s.fst
        exact hm1
      have hfac := hOld.fac (oldCone s) WalkingCospan.left
      change hOld.lift (oldCone s) ≫
        pullback.fst (basedPathEvBase X) X.hom = s.fst at hfac
      exact hm1'.trans hfac.symm
    · exact CGWH.point_isTerminal.hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
/-- The selected point of native based paths becomes the constant native
path at the selected point. -/
theorem basedPathToPath_point (X : PointedCGWH.{u, v}) :
    (PointedCGWH.basedPath.obj X).hom ≫
        PointedCGWH.basedPathToPath.app X =
      X.hom ≫ CGWH.pathConstant.app X.right := by
  let constBase : CGWH.point.{u, v} ⟶
      (ihom PointedCGWH.diskOne.right).obj X.right :=
    MonoidalClosed.curry
      (CartesianMonoidalCategory.snd
        PointedCGWH.diskOne.right CGWH.point ≫ X.hom)
  have hConst : constBase =
      X.hom ≫ CGWH.pathConstant.app X.right := by
    dsimp only [constBase, CGWH.pathConstant]
    rw [← MonoidalClosed.curry_natural_left]
    congr 1
    rw [CartesianMonoidalCategory.whiskerLeft_snd]
    rfl
  have hProbe : constBase ≫ basedPathEvBase X =
      𝟙 CGWH.point ≫ X.hom := by
    rw [hConst, basedPathEvBase_eq_pathEvalOne,
      Category.assoc, CGWH.pathConstant_evalOne,
      Category.comp_id, Category.id_comp]
  have hPointFst : (PointedCGWH.basedPath.obj X).hom ≫
      PointedCGWH.basedPathToPath.app X = constBase := by
    change pullback.lift constBase (𝟙 CGWH.point) _ ≫
        pullback.fst (basedPathEvBase X) X.hom = _
    exact pullback.lift_fst constBase (𝟙 CGWH.point) hProbe
  exact hPointFst.trans hConst

/-- A constant native based path has the selected endpoint. -/
@[reassoc]
theorem basedPathPoint_endpoint (X : PointedCGWH.{u, v}) :
    PointedCGWH.basedPathPoint.app X ≫
        PointedCGWH.basedPathEndpoint.app X =
      HasZeroObject.zeroIsInitial.to X :=
  HasZeroObject.zeroIsInitial.hom_ext _ _

/-- The native based-path cospan `basedPath X ⟶ X ⟵ 0`. -/
noncomputable def basedPathCospan :
    PointedCGWH.{u, v} ⥤
      (WalkingCospan ⥤ PointedCGWH.{u, v}) where
  obj X := cospan (PointedCGWH.basedPathEndpoint.app X)
    (HasZeroObject.zeroIsInitial.to X)
  map {X Y} f := cospanHomMk f
    (PointedCGWH.basedPath.map f) (𝟙 _)
    (PointedCGWH.basedPathEndpoint.naturality f).symm (by simp)
  map_id X := by
    ext j
    rcases j with (_ | _ | _) <;> simp
  map_comp f g := by
    ext j
    rcases j with (_ | _ | _) <;> simp

private noncomputable def zeroFiberCospan :
    PointedCGWH.{u, v} ⥤
      (WalkingCospan ⥤ PointedCGWH.{u, v}) where
  obj X := cospan (HasZeroObject.zeroIsInitial.to X)
    (HasZeroObject.zeroIsInitial.to X)
  map {X Y} f := cospanHomMk f (𝟙 _) (𝟙 _) (by simp) (by simp)
  map_id X := by
    ext j
    rcases j with (_ | _ | _) <;> simp
  map_comp f g := by
    ext j
    rcases j with (_ | _ | _) <;> simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def basedPathCospanUnit :
    zeroFiberCospan.{u, v} ⟶
      PointedCGWH.basedPathCospan.{u, v} where
  app X := cospanHomMk (𝟙 X)
    (PointedCGWH.basedPathPoint.app X)
    (𝟙 (0 : PointedCGWH.{u, v}))
    (by
      change HasZeroObject.zeroIsInitial.to X ≫ 𝟙 X =
        PointedCGWH.basedPathPoint.app X ≫
          PointedCGWH.basedPathEndpoint.app X
      simpa using (PointedCGWH.basedPathPoint_endpoint X).symm)
    (by
      change HasZeroObject.zeroIsInitial.to X ≫ 𝟙 X =
        𝟙 (0 : PointedCGWH.{u, v}) ≫
          HasZeroObject.zeroIsInitial.to X
      simp)
  naturality X Y f := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · change f ≫ 𝟙 Y = 𝟙 X ≫ f
      simp
    · change 𝟙 (0 : PointedCGWH.{u, v}) ≫
          PointedCGWH.basedPathPoint.app Y =
        PointedCGWH.basedPathPoint.app X ≫
          PointedCGWH.basedPath.map f
      simpa using PointedCGWH.basedPathPoint.naturality f
    · change 𝟙 (0 : PointedCGWH.{u, v}) ≫ 𝟙 _ =
          𝟙 (0 : PointedCGWH.{u, v}) ≫ 𝟙 _
      simp

private theorem diskBoundarySource_isCofibrant :
    IsCofibrant
      (CategoryTheory.Arrow.mk
        PointedCGWH.diskBoundary.{u, v}).left := by
  rw [isCofibrant_iff_of_isInitial
    (initial.to PointedCGWH.sphereZero.{u, v} ≫
      diskBoundarySourceIsoSphereZero.hom)
    initialIsInitial]
  apply (HomotopicalAlgebra.cofibration_iff _).mpr
  have hS0 : cofibrations PointedCGWH.{u, v}
      (initial.to PointedCGWH.sphereZero.{u, v}) :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant.mem
  exact (cofibrations PointedCGWH.{u, v}).comp_mem _ _ hS0
    (mem_cofibrations diskBoundarySourceIsoSphereZero.hom)

private theorem diskOne_isCofibrant :
    IsCofibrant PointedCGWH.diskOne.{u, v} := by
  rw [isCofibrant_iff_of_isInitial
    (initial.to
        (CategoryTheory.Arrow.mk
          PointedCGWH.diskBoundary.{u, v}).left ≫
      PointedCGWH.diskBoundary)
    initialIsInitial]
  exact (HomotopicalAlgebra.cofibration_iff _).mpr
    ((cofibrations PointedCGWH.{u, v}).comp_mem _ _
      diskBoundarySource_isCofibrant.mem
      PointedCGWH.modelCategory.diskBoundary_cofibration.mem)

private theorem terminal_isCofibrant :
    IsCofibrant (⊤_ PointedCGWH.{u, v}) := by
  rw [isCofibrant_iff_of_isInitial
    (HasZeroObject.zeroIsoTerminal
      (C := PointedCGWH.{u, v})).hom
    (isZero_zero PointedCGWH.{u, v}).isInitial]
  infer_instance

private theorem pointedPullbackHomFibrationClause :
    PullbackHomLe
      (cofibrations PointedCGWH.{u, v})
      (fibrations PointedCGWH.{u, v})
      (fibrations PointedCGWH.{u, v}) := by
  have hpp : PushoutProductLe
      (cofibrations PointedCGWH.{u, v})
      (trivialCofibrations PointedCGWH.{u, v})
      (fibrations PointedCGWH.{u, v}).llp := by
    rw [fibrations_llp (C := PointedCGWH.{u, v})]
    exact
      IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
        (C := PointedCGWH.{u, v})
  have h := (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
    (cofibrations PointedCGWH.{u, v})
    (trivialCofibrations PointedCGWH.{u, v})
    (fibrations PointedCGWH.{u, v})).mp hpp
  rwa [trivialCofibrations_rlp
    (C := PointedCGWH.{u, v})] at h

/-- Evaluation of a native based path at its free endpoint is a fibration. -/
theorem modelCategory.basedPathEndpoint_fibration
    (X : PointedCGWH.{u, v}) :
    Fibration (PointedCGWH.basedPathEndpoint.app X) := by
  let _ : IsFibrant X :=
    (PointedCGWH.isFibrant_iff X).2
      (CGWH.modelCategory.allObjectsFibrant X.right)
  have hpb := pointedPullbackHomFibrationClause
    PointedCGWH.diskBoundary (terminal.from X)
    PointedCGWH.modelCategory.diskBoundary_cofibration.mem
    ((HomotopicalAlgebra.fibration_iff _).mp
      (show IsFibrant X from inferInstance))
  let e := MonoidalCategory.Arrow.PullbackHom.isTerminalIso
    (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary)
    terminalIsTerminal (W := X)
  have hpre : fibrations PointedCGWH.{u, v}
      ((MonoidalClosed.pre PointedCGWH.diskBoundary).app X) :=
    ((fibrations PointedCGWH.{u, v}).arrow_mk_iso_iff e).mp hpb
  rw [HomotopicalAlgebra.fibration_iff, basedPathEndpoint_eq]
  set_option backward.isDefEq.respectTransparency false in
    change fibrations PointedCGWH.{u, v}
      ((MonoidalClosed.pre PointedCGWH.diskBoundary).app X ≫
        endpointPowerIso.hom.app X)
    exact RespectsIso.postcomp (fibrations PointedCGWH.{u, v})
      (endpointPowerIso.hom.app X)
      ((MonoidalClosed.pre PointedCGWH.diskBoundary).app X) hpre

/-- The constant native based path is a weak equivalence. -/
theorem modelCategory.basedPathPoint_weakEquivalence
    (X : PointedCGWH.{u, v}) :
    WeakEquivalence (PointedCGWH.basedPathPoint.app X) := by
  let _ : IsCofibrant PointedCGWH.diskOne.{u, v} :=
    diskOne_isCofibrant
  let _ : IsCofibrant (⊤_ PointedCGWH.{u, v}) :=
    terminal_isCofibrant
  let _ : IsFibrant X :=
    (PointedCGWH.isFibrant_iff X).2
      (CGWH.modelCategory.allObjectsFibrant X.right)
  have hpre : WeakEquivalence
      ((MonoidalClosed.pre
        PointedCGWH.diskAugmentation).app X) :=
    weakEquivalence_pre_app_of_cofibrant
      PointedCGWH.diskAugmentation
      PointedCGWH.modelCategory.diskAugmentation_weakEquivalence
  rw [HomotopicalAlgebra.weakEquivalence_iff, basedPathPoint_eq]
  set_option backward.isDefEq.respectTransparency false in
    change weakEquivalences PointedCGWH.{u, v}
      (terminalPowerIso.hom.app X ≫
        (MonoidalClosed.pre PointedCGWH.diskAugmentation).app X)
    exact RespectsIso.precomp (weakEquivalences PointedCGWH.{u, v})
      (terminalPowerIso.hom.app X)
      ((MonoidalClosed.pre PointedCGWH.diskAugmentation).app X)
      hpre.mem

private noncomputable def loopBasedPathLimitCone
    (X : PointedCGWH.{u, v}) :
    LimitCone (PointedCGWH.basedPathCospan.obj X) := by
  let S0 : PointedCGWH.{u, v} :=
    (CategoryTheory.Arrow.mk
      PointedCGWH.diskBoundary.{u, v}).left
  let F : WalkingSpan ⥤ PointedCGWH.{u, v} :=
    HomotopicalAlgebra.cofiberSpan.obj
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v})
  let hPush : IsPushout
      PointedCGWH.diskBoundary
      (terminal.from S0)
      (colimit.ι F WalkingSpan.left)
      (colimit.ι F WalkingSpan.right) := by
    set_option backward.isDefEq.respectTransparency false in
      exact IsPushout.of_isColimit_cocone (colimit.isColimit F)
  let cPush : PushoutCocone
      PointedCGWH.diskBoundary (terminal.from S0) :=
    hPush.cocone
  let hcPush : IsColimit cPush := hPush.isColimit
  let cOpp : PullbackCone
      PointedCGWH.diskBoundary.op (terminal.from S0).op :=
    cPush.op
  let hOpp : IsLimit cOpp :=
    (PushoutCocone.isColimitEquivIsLimitOp cPush).toFun hcPush
  let H_X : PointedCGWH.{u, v}ᵒᵖ ⥤ PointedCGWH.{u, v} :=
    MonoidalClosed.internalHom.flip.obj X
  let _ : PreservesLimits H_X :=
    (MonoidalClosed.internalHomSourceAdjunction X).rightAdjoint_preservesLimits
  let cMapped : Cone
      (cospan PointedCGWH.diskBoundary.op
        (terminal.from S0).op ⋙ H_X) :=
    set_option backward.isDefEq.respectTransparency false in
      H_X.mapCone cOpp
  let hMapped : IsLimit cMapped :=
    set_option backward.isDefEq.respectTransparency false in
      isLimitOfPreserves H_X hOpp
  let eDiag :
      (cospan PointedCGWH.diskBoundary.op
          (terminal.from S0).op ⋙ H_X) ≅
        PointedCGWH.basedPathCospan.obj X :=
    set_option backward.isDefEq.respectTransparency false in cospanIsoMk
      (endpointPowerIso.app X)
      (Iso.refl (PointedCGWH.basedPath.obj X))
      (terminalPowerIso.symm.app X)
      (by
        change (MonoidalClosed.pre
              PointedCGWH.diskBoundary).app X ≫
            endpointPowerIso.hom.app X =
          𝟙 (PointedCGWH.basedPath.obj X) ≫
            PointedCGWH.basedPathEndpoint.app X
        have hEndpointX :
            (MonoidalClosed.pre
                PointedCGWH.diskBoundary).app X ≫
              endpointPowerIso.hom.app X =
            PointedCGWH.basedPathEndpoint.app X := by
          simpa only [NatTrans.comp_app] using
            (congrArg (fun k => k.app X)
              basedPathEndpoint_eq).symm
        simpa only [Category.id_comp] using hEndpointX)
      (by
        change (MonoidalClosed.pre
              (terminal.from S0)).app X ≫
            endpointPowerIso.hom.app X =
          terminalPowerIso.inv.app X ≫
            HasZeroObject.zeroIsInitial.to X
        have hTerminal :
            PointedCGWH.diskBoundary ≫
                PointedCGWH.diskAugmentation =
              terminal.from S0 :=
          terminalIsTerminal.hom_ext _ _
        have hPointX :
            terminalPowerIso.hom.app X ≫
                (MonoidalClosed.pre
                  PointedCGWH.diskAugmentation).app X =
              PointedCGWH.basedPathPoint.app X := by
          simpa only [NatTrans.comp_app] using
            (congrArg (fun k => k.app X)
              basedPathPoint_eq).symm
        have hEndpointX :
            (MonoidalClosed.pre
                PointedCGWH.diskBoundary).app X ≫
              endpointPowerIso.hom.app X =
            PointedCGWH.basedPathEndpoint.app X := by
          simpa only [NatTrans.comp_app] using
            (congrArg (fun k => k.app X)
              basedPathEndpoint_eq).symm
        apply (cancel_epi (terminalPowerIso.hom.app X)).1
        change terminalPowerIso.hom.app X ≫
              (MonoidalClosed.pre (terminal.from S0)).app X ≫
              endpointPowerIso.hom.app X =
            terminalPowerIso.hom.app X ≫
              terminalPowerIso.inv.app X ≫
              HasZeroObject.zeroIsInitial.to X
        calc
          _ = (terminalPowerIso.hom.app X ≫
                  (MonoidalClosed.pre
                    PointedCGWH.diskAugmentation).app X) ≫
                ((MonoidalClosed.pre
                    PointedCGWH.diskBoundary).app X ≫
                  endpointPowerIso.hom.app X) := by
              rw [← hTerminal, MonoidalClosed.pre_map,
                NatTrans.comp_app]
              simp only [Category.assoc]
          _ = PointedCGWH.basedPathPoint.app X ≫
                PointedCGWH.basedPathEndpoint.app X := by
              rw [hPointX, hEndpointX]
          _ = HasZeroObject.zeroIsInitial.to X :=
              PointedCGWH.basedPathPoint_endpoint X
          _ = terminalPowerIso.hom.app X ≫
                terminalPowerIso.inv.app X ≫
                HasZeroObject.zeroIsInitial.to X := by simp)
  let cTransported : Cone
      (PointedCGWH.basedPathCospan.obj X) :=
    (Cone.postcompose eDiag.hom).obj cMapped
  let hTransported : IsLimit cTransported :=
    (IsLimit.postcomposeHomEquiv eDiag cMapped).invFun hMapped
  let i : PointedCGWH.loop.obj X ⟶ cTransported.pt :=
    set_option backward.isDefEq.respectTransparency false in
      (MonoidalClosed.pre
        PointedCGWH.diskCofiberIsoSphereOne.hom).app X
  let _ : IsIso i := by
    set_option backward.isDefEq.respectTransparency false in
      change IsIso ((preNatIsoOfIso
        PointedCGWH.diskCofiberIsoSphereOne).hom.app X)
      infer_instance
  let cLoop : Cone (PointedCGWH.basedPathCospan.obj X) :=
    cTransported.extend i
  let hLoop : IsLimit cLoop :=
    IsLimit.extendIso i hTransported
  exact ⟨cLoop, hLoop⟩

private noncomputable def loopBasedPathPullbackIso_app
    (X : PointedCGWH.{u, v}) :
    PointedCGWH.loop.obj X ≅
      limit (PointedCGWH.basedPathCospan.obj X) := by
  set_option backward.isDefEq.respectTransparency false in
    exact (loopBasedPathLimitCone X).isLimit.conePointUniqueUpToIso
      (limit.isLimit _)

private theorem loopBasedPathPullbackIso_naturality
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    PointedCGWH.loop.map f ≫
        (loopBasedPathPullbackIso_app Y).hom =
      (loopBasedPathPullbackIso_app X).hom ≫
        lim.map (PointedCGWH.basedPathCospan.map f) := by
  let F : WalkingSpan ⥤ PointedCGWH.{u, v} :=
    HomotopicalAlgebra.cofiberSpan.obj
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v})
  have hLeft :
      PointedCGWH.loop.map f ≫
          (loopBasedPathLimitCone Y).cone.π.app
            WalkingCospan.left =
        (loopBasedPathLimitCone X).cone.π.app
            WalkingCospan.left ≫
          (PointedCGWH.basedPathCospan.map f).app
            WalkingCospan.left := by
    set_option backward.isDefEq.respectTransparency false in
      change (ihom PointedCGWH.sphereOne).map f ≫
            ((MonoidalClosed.pre
                PointedCGWH.diskCofiberIsoSphereOne.hom).app Y ≫
              (MonoidalClosed.pre
                (colimit.ι F WalkingSpan.left)).app Y) =
          ((MonoidalClosed.pre
                PointedCGWH.diskCofiberIsoSphereOne.hom).app X ≫
              (MonoidalClosed.pre
                (colimit.ι F WalkingSpan.left)).app X) ≫
            (ihom PointedCGWH.diskOne).map f
      rw [← Category.assoc,
        ← MonoidalClosed.pre_comm_ihom_map
          PointedCGWH.diskCofiberIsoSphereOne.hom f]
      change
        ((MonoidalClosed.pre
            PointedCGWH.diskCofiberIsoSphereOne.hom).app X ≫
            (ihom (colimit F)).map f) ≫
            (MonoidalClosed.pre
              (colimit.ι F WalkingSpan.left)).app Y =
          ((MonoidalClosed.pre
              PointedCGWH.diskCofiberIsoSphereOne.hom).app X ≫
            (MonoidalClosed.pre
              (colimit.ι F WalkingSpan.left)).app X) ≫
            (ihom PointedCGWH.diskOne).map f
      rw [Category.assoc,
        ← MonoidalClosed.pre_comm_ihom_map
          (colimit.ι F WalkingSpan.left) f]
      rw [← Category.assoc]
      change
        ((MonoidalClosed.pre
            PointedCGWH.diskCofiberIsoSphereOne.hom).app X ≫
          (MonoidalClosed.pre
            (colimit.ι F WalkingSpan.left)).app X) ≫
            (ihom PointedCGWH.diskOne).map f =
          ((MonoidalClosed.pre
              PointedCGWH.diskCofiberIsoSphereOne.hom).app X ≫
            (MonoidalClosed.pre
              (colimit.ι F WalkingSpan.left)).app X) ≫
            (ihom PointedCGWH.diskOne).map f
      rfl
  have hIso (Z : PointedCGWH.{u, v}) (j : WalkingCospan) :
      (loopBasedPathPullbackIso_app Z).hom ≫
          limit.π (PointedCGWH.basedPathCospan.obj Z) j =
        (loopBasedPathLimitCone Z).cone.π.app j := by
    set_option backward.isDefEq.respectTransparency false in
      exact IsLimit.conePointUniqueUpToIso_hom_comp
        (loopBasedPathLimitCone Z).isLimit (limit.isLimit _) j
  have hCone (j : WalkingCospan) :
      PointedCGWH.loop.map f ≫
          (loopBasedPathLimitCone Y).cone.π.app j =
        (loopBasedPathLimitCone X).cone.π.app j ≫
          (PointedCGWH.basedPathCospan.map f).app j := by
    rcases j with (_ | _ | _)
    · set_option backward.isDefEq.respectTransparency false in calc
        PointedCGWH.loop.map f ≫
            (loopBasedPathLimitCone Y).cone.π.app
              WalkingCospan.one =
          PointedCGWH.loop.map f ≫
            (loopBasedPathLimitCone Y).cone.π.app
                WalkingCospan.left ≫
              (PointedCGWH.basedPathCospan.obj Y).map
                WalkingCospan.Hom.inl := by
            rw [(loopBasedPathLimitCone Y).cone.w]
        _ = (loopBasedPathLimitCone X).cone.π.app
                WalkingCospan.left ≫
              (PointedCGWH.basedPathCospan.map f).app
                  WalkingCospan.left ≫
                (PointedCGWH.basedPathCospan.obj Y).map
                  WalkingCospan.Hom.inl := by
            rw [← Category.assoc, hLeft, Category.assoc]
        _ = (loopBasedPathLimitCone X).cone.π.app
                WalkingCospan.left ≫
              (PointedCGWH.basedPathCospan.obj X).map
                  WalkingCospan.Hom.inl ≫
                (PointedCGWH.basedPathCospan.map f).app
                  WalkingCospan.one := by
            rw [(PointedCGWH.basedPathCospan.map f).naturality]
        _ = (loopBasedPathLimitCone X).cone.π.app
                WalkingCospan.one ≫
              (PointedCGWH.basedPathCospan.map f).app
                WalkingCospan.one := by
            rw [← Category.assoc,
              (loopBasedPathLimitCone X).cone.w]
    · exact hLeft
    · apply HasZeroObject.zeroIsTerminal.hom_ext
  apply limit.hom_ext
  intro j
  set_option backward.isDefEq.respectTransparency false in calc
    (PointedCGWH.loop.map f ≫
        (loopBasedPathPullbackIso_app Y).hom) ≫
        limit.π (PointedCGWH.basedPathCospan.obj Y) j =
      PointedCGWH.loop.map f ≫
        (loopBasedPathLimitCone Y).cone.π.app j := by
          rw [Category.assoc, hIso Y j]
    _ = (loopBasedPathLimitCone X).cone.π.app j ≫
          (PointedCGWH.basedPathCospan.map f).app j := hCone j
    _ = ((loopBasedPathPullbackIso_app X).hom ≫
            limit.π (PointedCGWH.basedPathCospan.obj X) j) ≫
          (PointedCGWH.basedPathCospan.map f).app j := by
          rw [hIso X j]
    _ = (loopBasedPathPullbackIso_app X).hom ≫
          (limit.π (PointedCGWH.basedPathCospan.obj X) j ≫
            (PointedCGWH.basedPathCospan.map f).app j) := by
          rw [Category.assoc]
    _ = (loopBasedPathPullbackIso_app X).hom ≫
          (lim.map (PointedCGWH.basedPathCospan.map f) ≫
            limit.π (PointedCGWH.basedPathCospan.obj Y) j) := by
          exact congrArg
            (fun k => (loopBasedPathPullbackIso_app X).hom ≫ k)
            (limMap_π
              (PointedCGWH.basedPathCospan.map f) j).symm
    _ = ((loopBasedPathPullbackIso_app X).hom ≫
            lim.map (PointedCGWH.basedPathCospan.map f)) ≫
          limit.π (PointedCGWH.basedPathCospan.obj Y) j := by
          rw [Category.assoc]

/-- Strict native loops are the ordinary pullback of the based-path
cospan. -/
noncomputable def loopBasedPathPullbackIso :
    PointedCGWH.loop.{u, v} ≅
      PointedCGWH.basedPathCospan.{u, v} ⋙ lim :=
  NatIso.ofComponents
    (fun X => loopBasedPathPullbackIso_app X)
    (fun f => loopBasedPathPullbackIso_naturality f)

/-- The path coordinate of the strict-loop pullback comparison evaluates at
every parameter as the native strict loop does. -/
theorem loopBasedPathPullbackIso_pathLanding
    (X : PointedCGWH.{u, v})
    (gamma : (PointedCGWH.loop.obj X).right)
    (t : TopCat.I.{v}) :
    CGWH.pathLanding X.right
        (PointedCGWH.basedPathToPath.app X
          ((limit.π (PointedCGWH.basedPathCospan.obj X)
              WalkingCospan.left).right
            ((PointedCGWH.loopBasedPathPullbackIso.hom.app X).right
              gamma))) t =
      (PointedCGWH.loopEvalAt X t).right gamma := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : HasPullbacks CGWH.{u, v} := by
    let _ : HasLimitsOfSize.{v, v} CompactlyGenerated.{u, v} :=
      CategoryTheory.hasLimits_of_coreflective
        CompactlyGenerated.compactlyGeneratedToTop
    let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} :=
      CategoryTheory.hasLimits_of_reflective
        CGWH.cgwhToCompactlyGenerated
    infer_instance
  let F : WalkingSpan ⥤ PointedCGWH.{u, v} :=
    HomotopicalAlgebra.cofiberSpan.obj
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v})
  let d : PointedCGWH.diskOne.{u, v} ⟶
      PointedCGWH.sphereOne.{u, v} :=
    colimit.ι F WalkingSpan.left ≫
      PointedCGWH.diskCofiberIsoSphereOne.hom
  have hLeftProjection :
      PointedCGWH.loopBasedPathPullbackIso.hom.app X ≫
          limit.π (PointedCGWH.basedPathCospan.obj X)
            WalkingCospan.left =
        (MonoidalClosed.pre
          (colimit.ι F WalkingSpan.left ≫
            PointedCGWH.diskCofiberIsoSphereOne.hom)).app X := by
    have hIso :
        PointedCGWH.loopBasedPathPullbackIso.hom.app X ≫
            limit.π (PointedCGWH.basedPathCospan.obj X)
              WalkingCospan.left =
          (loopBasedPathLimitCone X).cone.π.app
            WalkingCospan.left := by
      change (loopBasedPathPullbackIso_app X).hom ≫
          limit.π (PointedCGWH.basedPathCospan.obj X)
            WalkingCospan.left = _
      exact IsLimit.conePointUniqueUpToIso_hom_comp
        (loopBasedPathLimitCone X).isLimit (limit.isLimit _)
        WalkingCospan.left
    rw [hIso]
    change ((MonoidalClosed.pre
        PointedCGWH.diskCofiberIsoSphereOne.hom).app X ≫
          (MonoidalClosed.pre
            (colimit.ι F WalkingSpan.left)).app X) =
      (MonoidalClosed.pre
        (colimit.ι F WalkingSpan.left ≫
          PointedCGWH.diskCofiberIsoSphereOne.hom)).app X
    exact (congrArg (fun k => k.app X)
      (MonoidalClosed.pre_map (colimit.ι F WalkingSpan.left)
        PointedCGWH.diskCofiberIsoSphereOne.hom)).symm
  let jSphere : (PointedCGWH.loop.obj X).right ⟶
      (ihom PointedCGWH.sphereOne.right).obj X.right :=
    (CategoryTheory.Pointed.basedInternalHomToInternalHom
      CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne).app X
  have hDiskCarrier : PointedCGWH.basedPathToPath.app X =
      (CategoryTheory.Pointed.basedInternalHomToInternalHom
        CGWH.point CGWH.point_isTerminal PointedCGWH.diskOne).app X := by
    rfl
  have hPre :=
    CategoryTheory.Pointed.basedInternalHomToInternalHom_pre
      CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
        PointedCGWH.diskOne X d
  have hRawPre :
      (PointedCGWH.loopBasedPathPullbackIso.hom.app X ≫
          limit.π (PointedCGWH.basedPathCospan.obj X)
            WalkingCospan.left).right ≫
          PointedCGWH.basedPathToPath.app X =
        jSphere ≫ (MonoidalClosed.pre d.right).app X.right := by
    have hLeftRight := congrArg Under.Hom.right hLeftProjection
    rw [hLeftRight]
    change ((MonoidalClosed.pre d).app X).right ≫
        PointedCGWH.basedPathToPath.app X = _
    rw [hDiskCarrier]
    exact hPre
  let etaSphere : (ihom PointedCGWH.sphereOne.right).obj X.right :=
    jSphere gamma
  let etaDisk : CGWH.path.obj X.right :=
    (MonoidalClosed.pre d.right).app X.right etaSphere
  have hEta :
      PointedCGWH.basedPathToPath.app X
          ((limit.π (PointedCGWH.basedPathCospan.obj X)
              WalkingCospan.left).right
            ((PointedCGWH.loopBasedPathPullbackIso.hom.app X).right
              gamma)) =
        etaDisk := by
    have h := ConcreteCategory.congr_hom hRawPre gamma
    change _ = etaDisk at h
    exact h
  let aDisk : CGWH.point.{u, v} ⟶
      PointedCGWH.diskOne.{u, v}.right :=
    ConcreteCategory.ofHom
      (ContinuousMap.const _ (CGWH.intervalToTopIso.{u, v}.inv t))
  let bDisk : CGWH.point.{u, v} ⟶
      (ihom PointedCGWH.diskOne.{u, v}.right).obj X.right :=
    (CGWH.pointHomEquiv _).symm etaDisk
  have hLanding : CGWH.pathLanding X.right etaDisk t =
      (ihom.ev PointedCGWH.diskOne.{u, v}.right).app X.right
        (CartesianMonoidalCategory.lift aDisk bDisk PUnit.unit) := by
    let rawEta := (Topology.WithGeneratedByTopology.equiv
      (X := CompactlyGenerated.compactHausProbes.{u})
      (Y := Topology.ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u}
          CGWH.interval.{u, v} X.right) etaDisk :
      Topology.ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u}
          CGWH.interval.{u, v} X.right)
    let e : CompactlyGenerated.compactHausProbes
        (CompHaus.of (ULift.{u} unitInterval)) ≃ₜ TopCat.I.{v} :=
      Homeomorph.ulift.{u, 0}.trans TopCat.I.homeomorph.{v}.symm
    change rawEta (CGWH.intervalToTopIso.{u, v}.inv (e (e.symm t))) =
      (ihom.ev PointedCGWH.diskOne.{u, v}.right).app X.right
        (CartesianMonoidalCategory.lift aDisk bDisk PUnit.unit)
    rw [e.apply_symm_apply]
    let z := CartesianMonoidalCategory.lift aDisk bDisk PUnit.unit
    have hFst : ConcreteCategory.hom (C := CGWH.{u, v})
        (CartesianMonoidalCategory.fst PointedCGWH.diskOne.{u, v}.right
          ((ihom PointedCGWH.diskOne.{u, v}.right).obj X.right)) z =
        CGWH.intervalToTopIso.{u, v}.inv t := by
      dsimp only [z]
      change ConcreteCategory.hom
        (CartesianMonoidalCategory.lift aDisk bDisk ≫
          CartesianMonoidalCategory.fst PointedCGWH.diskOne.{u, v}.right
            ((ihom PointedCGWH.diskOne.{u, v}.right).obj X.right))
          PUnit.unit = _
      rw [CartesianMonoidalCategory.lift_fst]
      rfl
    have hSnd : ConcreteCategory.hom (C := CGWH.{u, v})
        (CartesianMonoidalCategory.snd PointedCGWH.diskOne.{u, v}.right
          ((ihom PointedCGWH.diskOne.{u, v}.right).obj X.right)) z =
        etaDisk := by
      dsimp only [z]
      change ConcreteCategory.hom
        (CartesianMonoidalCategory.lift aDisk bDisk ≫
          CartesianMonoidalCategory.snd PointedCGWH.diskOne.{u, v}.right
            ((ihom PointedCGWH.diskOne.{u, v}.right).obj X.right))
          PUnit.unit = _
      rw [CartesianMonoidalCategory.lift_snd]
      rfl
    have hEv := CGWH.internalHom_ev_apply
      PointedCGWH.diskOne.{u, v}.right X.right z
    change (ihom.ev PointedCGWH.diskOne.{u, v}.right).app X.right z =
      (Topology.WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{u})
        (Y := Topology.ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u}
            PointedCGWH.diskOne.{u, v}.right X.right)
        (CartesianMonoidalCategory.snd PointedCGWH.diskOne.{u, v}.right
          ((ihom PointedCGWH.diskOne.{u, v}.right).obj X.right) z))
        (CartesianMonoidalCategory.fst PointedCGWH.diskOne.{u, v}.right
          ((ihom PointedCGWH.diskOne.{u, v}.right).obj X.right) z) at hEv
    rw [hFst, hSnd] at hEv
    exact hEv.symm
  let aSphere : CGWH.point.{u, v} ⟶
      PointedCGWH.sphereOne.{u, v}.right :=
    ConcreteCategory.ofHom
      (ContinuousMap.const _ (PointedCGWH.sphereOneParam.{u, v} t))
  let bSphere : CGWH.point.{u, v} ⟶
      (ihom PointedCGWH.sphereOne.right).obj X.right :=
    (CGWH.pointHomEquiv _).symm etaSphere
  have hParam : aDisk ≫ d.right = aSphere := by
    apply ConcreteCategory.hom_ext
    intro p
    change d.right (CGWH.intervalToTopIso.{u, v}.inv t) =
      PointedCGWH.sphereOneParam t
    exact PointedCGWH.diskCofiberIsoSphereOne_param t
  have hPrePoint : bSphere ≫
      (MonoidalClosed.pre d.right).app X.right = bDisk := by
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    rfl
  have hDiskPair :
      CartesianMonoidalCategory.lift aDisk bSphere ≫
          (PointedCGWH.diskOne.right ◁
            (MonoidalClosed.pre d.right).app X.right) =
        CartesianMonoidalCategory.lift aDisk bDisk := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc,
        CartesianMonoidalCategory.whiskerLeft_fst,
        CartesianMonoidalCategory.lift_fst]
    · simp only [Category.assoc,
        CartesianMonoidalCategory.whiskerLeft_snd,
        CartesianMonoidalCategory.lift_snd]
      rw [← Category.assoc, CartesianMonoidalCategory.lift_snd,
        hPrePoint]
  have hSpherePair :
      CartesianMonoidalCategory.lift aDisk bSphere ≫
          (d.right ▷ (ihom PointedCGWH.sphereOne.right).obj X.right) =
        CartesianMonoidalCategory.lift aSphere bSphere := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc,
        CartesianMonoidalCategory.whiskerRight_fst,
        CartesianMonoidalCategory.lift_fst]
      rw [← Category.assoc, CartesianMonoidalCategory.lift_fst,
        hParam]
    · simp only [Category.assoc,
        CartesianMonoidalCategory.whiskerRight_snd,
        CartesianMonoidalCategory.lift_snd]
  have hRawMaps :
      CartesianMonoidalCategory.lift aDisk bDisk ≫
          (ihom.ev PointedCGWH.diskOne.right).app X.right =
        CartesianMonoidalCategory.lift aSphere bSphere ≫
          (ihom.ev PointedCGWH.sphereOne.right).app X.right := by
    calc
      _ = (CartesianMonoidalCategory.lift aDisk bSphere ≫
              (PointedCGWH.diskOne.right ◁
                (MonoidalClosed.pre d.right).app X.right)) ≫
            (ihom.ev PointedCGWH.diskOne.right).app X.right := by
          rw [hDiskPair]
      _ = CartesianMonoidalCategory.lift aDisk bSphere ≫
            ((PointedCGWH.diskOne.right ◁
                (MonoidalClosed.pre d.right).app X.right) ≫
              (ihom.ev PointedCGWH.diskOne.right).app X.right) := by
          rw [Category.assoc]
      _ = CartesianMonoidalCategory.lift aDisk bSphere ≫
            ((d.right ▷
                (ihom PointedCGWH.sphereOne.right).obj X.right) ≫
              (ihom.ev PointedCGWH.sphereOne.right).app X.right) := by
          rw [MonoidalClosed.id_tensor_pre_app_comp_ev]
      _ = (CartesianMonoidalCategory.lift aDisk bSphere ≫
              (d.right ▷
                (ihom PointedCGWH.sphereOne.right).obj X.right)) ≫
            (ihom.ev PointedCGWH.sphereOne.right).app X.right := by
          rw [Category.assoc]
      _ = _ := by rw [hSpherePair]
  have hRawPoint := ConcreteCategory.congr_hom hRawMaps PUnit.unit
  let L := PointedCGWH.loop.obj X
  let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
    ConcreteCategory.ofHom
      (ContinuousMap.const _ (PointedCGWH.sphereOneParam.{u, v} t))
  let b : CGWH.point.{u, v} ⟶ L.right :=
    ConcreteCategory.ofHom (ContinuousMap.const _ gamma)
  let constParam : L.right ⟶ PointedCGWH.sphereOne.{u, v}.right :=
    CGWH.point_isTerminal.from L.right ≫ a
  let pairProd : L.right ⟶
      PointedCGWH.sphereOne.{u, v}.right ⨯ L.right :=
    Limits.prod.lift constParam (𝟙 L.right)
  let eTensor : PointedCGWH.sphereOne.{u, v}.right ⊗ L.right ≅
      PointedCGWH.sphereOne.{u, v}.right ⨯ L.right :=
    (CartesianMonoidalCategory.tensorLeftIsoProd
      PointedCGWH.sphereOne.{u, v}.right).app L.right
  let pairTensor : L.right ⟶
      PointedCGWH.sphereOne.{u, v}.right ⊗ L.right :=
    pairProd ≫ eTensor.inv
  have eTensor_fst : eTensor.hom ≫
      (Limits.prod.fst : PointedCGWH.sphereOne.right ⨯ L.right ⟶
        PointedCGWH.sphereOne.right) =
      CartesianMonoidalCategory.fst PointedCGWH.sphereOne.right L.right :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct
        PointedCGWH.sphereOne.right L.right)
      (limit.isLimit _) ⟨WalkingPair.left⟩
  have eTensor_snd : eTensor.hom ≫
      (Limits.prod.snd : PointedCGWH.sphereOne.right ⨯ L.right ⟶
        L.right) =
      CartesianMonoidalCategory.snd PointedCGWH.sphereOne.right L.right :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct
        PointedCGWH.sphereOne.right L.right)
      (limit.isLimit _) ⟨WalkingPair.right⟩
  have hPairTensor : pairTensor =
      CartesianMonoidalCategory.lift constParam (𝟙 L.right) := by
    apply (cancel_mono eTensor.hom).1
    dsimp only [pairTensor]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Limits.prod.hom_ext
    · dsimp only [pairProd]
      rw [Limits.prod.lift_fst, Category.assoc, eTensor_fst,
        CartesianMonoidalCategory.lift_fst]
    · dsimp only [pairProd]
      rw [Limits.prod.lift_snd, Category.assoc, eTensor_snd,
        CartesianMonoidalCategory.lift_snd]
  have hConst : b ≫ constParam = a := by
    dsimp only [constParam]
    rw [← Category.assoc]
    have hTerm : b ≫ CGWH.point_isTerminal.from L.right =
        𝟙 CGWH.point.{u, v} := CGWH.point_isTerminal.hom_ext _ _
    rw [hTerm, Category.id_comp]
  have hPairMap : b ≫
      CartesianMonoidalCategory.lift constParam (𝟙 L.right) =
        CartesianMonoidalCategory.lift a b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, CartesianMonoidalCategory.lift_fst,
        hConst, CartesianMonoidalCategory.lift_fst]
    · rw [Category.assoc, CartesianMonoidalCategory.lift_snd,
        Category.comp_id, CartesianMonoidalCategory.lift_snd]
  have hPairPoint :
      CartesianMonoidalCategory.lift constParam (𝟙 L.right) gamma =
        CartesianMonoidalCategory.lift a b PUnit.unit := by
    have h := ConcreteCategory.congr_hom hPairMap PUnit.unit
    exact h
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne L
  let q : PointedCGWH.sphereOne.{u, v}.right ⊗ L.right ⟶
      ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).right :=
    p.2.1.inl
  let ev : (PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L ⟶ X :=
    (PointedCGWH.basedEval PointedCGWH.sphereOne).app X
  have hEvalAt : (PointedCGWH.loopEvalAt X t).right gamma =
      ev.right (q (CartesianMonoidalCategory.lift a b PUnit.unit)) := by
    change ev.right (q (pairTensor gamma)) = _
    rw [hPairTensor, hPairPoint]
  have hLoopCarrier : jSphere =
      (CategoryTheory.Pointed.basedInternalHomToInternalHom
        CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne).app X :=
    rfl
  have hBSphere : b ≫ jSphere = bSphere := by
    apply ConcreteCategory.hom_ext
    intro point
    cases point
    rfl
  have hSmashPair :
      CartesianMonoidalCategory.lift a b ≫
          (PointedCGWH.sphereOne.right ◁ jSphere) =
        CartesianMonoidalCategory.lift aSphere bSphere := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc,
        CartesianMonoidalCategory.whiskerLeft_fst,
        CartesianMonoidalCategory.lift_fst]
      rfl
    · simp only [Category.assoc,
        CartesianMonoidalCategory.whiskerLeft_snd,
        CartesianMonoidalCategory.lift_snd]
      rw [← Category.assoc, CartesianMonoidalCategory.lift_snd,
        hBSphere]
  have hQuotient :=
    CategoryTheory.Pointed.smashQuotient_basedEval
      CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne X
  have hQuotientPoint := ConcreteCategory.congr_hom hQuotient
    (CartesianMonoidalCategory.lift a b PUnit.unit)
  have hSmashPoint := ConcreteCategory.congr_hom hSmashPair PUnit.unit
  have hLoopRaw : (PointedCGWH.loopEvalAt X t).right gamma =
      (ihom.ev PointedCGWH.sphereOne.right).app X.right
        (CartesianMonoidalCategory.lift aSphere bSphere PUnit.unit) := by
    rw [hEvalAt]
    rw [← hLoopCarrier] at hQuotientPoint
    exact hQuotientPoint.trans (congrArg
      (fun z => (ihom.ev PointedCGWH.sphereOne.right).app X.right z)
      hSmashPoint)
  rw [hEta, hLanding]
  exact hRawPoint.trans hLoopRaw.symm

/-- Homotopy pullback of the native based-path cospan. -/
noncomputable def nativePathHomotopyLoop :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.basedPathCospan.{u, v} ⋙
    HomotopicalAlgebra.homotopyPullback

set_option backward.isDefEq.respectTransparency false in
private noncomputable def derivedLoopZeroFiberIso :
    HomotopicalAlgebra.derivedLoop
        (C := PointedCGWH.{u, v}) ≅
      zeroFiberCospan.{u, v} ⋙
        HomotopicalAlgebra.homotopyPullback := by
  let eDiag (X : PointedCGWH.{u, v}) :
      (HomotopicalAlgebra.fiberCospan
        (C := PointedCGWH.{u, v})).obj
          (CategoryTheory.Arrow.mk
            (HasZeroObject.zeroIsInitial.to X)) ≅
        zeroFiberCospan.obj X :=
    cospanIsoMk (Iso.refl X)
      (Iso.refl (0 : PointedCGWH.{u, v}))
      (HasZeroObject.zeroIsoInitial
        (C := PointedCGWH.{u, v})).symm
      (by
        change HasZeroObject.zeroIsInitial.to X ≫ 𝟙 X =
          𝟙 (0 : PointedCGWH.{u, v}) ≫
            HasZeroObject.zeroIsInitial.to X
        simp)
      (by apply initialIsInitial.hom_ext)
  refine NatIso.ofComponents
    (fun X => by
      dsimp only [HomotopicalAlgebra.derivedLoop,
        HomotopicalAlgebra.homotopyFiber, Functor.comp_obj]
      exact HomotopicalAlgebra.homotopyPullback.mapIso
        (eDiag X)) ?_
  intro X Y f
  let sq : CategoryTheory.Arrow.mk
        (HasZeroObject.zeroIsInitial.to X) ⟶
      CategoryTheory.Arrow.mk
        (HasZeroObject.zeroIsInitial.to Y) :=
    CategoryTheory.Arrow.homMk
      (𝟙 (0 : PointedCGWH.{u, v})) f
      (by apply HasZeroObject.zeroIsInitial.hom_ext)
  have hDiag :
      (HomotopicalAlgebra.fiberCospan
          (C := PointedCGWH.{u, v})).map sq ≫
            (eDiag Y).hom =
        (eDiag X).hom ≫ zeroFiberCospan.map f := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _) <;>
      simp [eDiag, sq, HomotopicalAlgebra.fiberCospan,
        zeroFiberCospan]
  dsimp only [HomotopicalAlgebra.derivedLoop,
    HomotopicalAlgebra.homotopyFiber, Functor.comp_map]
  change HomotopicalAlgebra.homotopyPullback.map
        ((HomotopicalAlgebra.fiberCospan
          (C := PointedCGWH.{u, v})).map sq) ≫
        HomotopicalAlgebra.homotopyPullback.map (eDiag Y).hom =
    HomotopicalAlgebra.homotopyPullback.map (eDiag X).hom ≫
      HomotopicalAlgebra.homotopyPullback.map
        (zeroFiberCospan.map f)
  simpa only [Functor.map_comp] using
    congrArg
      (fun k => HomotopicalAlgebra.homotopyPullback.map k)
      hDiag

/-- The chosen derived loop maps naturally to the native based-path
homotopy pullback. -/
noncomputable def derivedLoopToNativePathHomotopyLoop :
    HomotopicalAlgebra.derivedLoop
        (C := PointedCGWH.{u, v}) ⟶
      PointedCGWH.nativePathHomotopyLoop.{u, v} :=
  derivedLoopZeroFiberIso.hom ≫
    Functor.whiskerRight basedPathCospanUnit
      HomotopicalAlgebra.homotopyPullback

/-- Strict native loops map naturally to the native based-path homotopy
pullback. -/
noncomputable def loopToNativePathHomotopyLoop :
    PointedCGWH.loop.{u, v} ⟶
      PointedCGWH.nativePathHomotopyLoop.{u, v} :=
  PointedCGWH.loopBasedPathPullbackIso.hom ≫
    Functor.whiskerLeft PointedCGWH.basedPathCospan
      HomotopicalAlgebra.homotopyPullbackComparison

/-- The chosen-derived leg to the native based-path homotopy pullback is a
weak equivalence objectwise. -/
theorem derivedLoopToNativePathHomotopyLoop_weakEquivalence
    (X : PointedCGWH.{u, v}) :
    WeakEquivalence
      (PointedCGWH.derivedLoopToNativePathHomotopyLoop.app X) := by
  have hMap : WeakEquivalence
      (HomotopicalAlgebra.homotopyPullback.map
        (basedPathCospanUnit.app X)) := by
    apply HomotopicalAlgebra.homotopyPullback_map_weakEquivalence
      (basedPathCospanUnit.app X)
    intro j
    rcases j with (_ | _ | _)
    · change WeakEquivalence (𝟙 X)
      infer_instance
    · change WeakEquivalence
        (PointedCGWH.basedPathPoint.app X)
      exact PointedCGWH.modelCategory.basedPathPoint_weakEquivalence X
    · change WeakEquivalence (𝟙 (0 : PointedCGWH.{u, v}))
      infer_instance
  set_option backward.isDefEq.respectTransparency false in
    change WeakEquivalence
      (derivedLoopZeroFiberIso.hom.app X ≫
        HomotopicalAlgebra.homotopyPullback.map
          (basedPathCospanUnit.app X))
    rw [HomotopicalAlgebra.weakEquivalence_iff]
    exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _
      (mem_weakEquivalences (derivedLoopZeroFiberIso.hom.app X))
      hMap.mem

/-- The strict-loop leg to the native based-path homotopy pullback is a
weak equivalence objectwise. -/
theorem loopToNativePathHomotopyLoop_weakEquivalence
    (X : PointedCGWH.{u, v}) :
    WeakEquivalence
      (PointedCGWH.loopToNativePathHomotopyLoop.app X) := by
  let _ : IsFibrant X :=
    (PointedCGWH.isFibrant_iff X).2
      (CGWH.modelCategory.allObjectsFibrant X.right)
  let _ : IsFibrant (0 : PointedCGWH.{u, v}) :=
    (PointedCGWH.isFibrant_iff
      (0 : PointedCGWH.{u, v})).2
        (CGWH.modelCategory.allObjectsFibrant
          (0 : PointedCGWH.{u, v}).right)
  let _ : Fibration
      (PointedCGWH.basedPathEndpoint.app X) :=
    PointedCGWH.modelCategory.basedPathEndpoint_fibration X
  let _ : IsFibrant
      ((PointedCGWH.basedPathCospan.obj X).obj
        WalkingCospan.one) := by
    change IsFibrant X
    infer_instance
  let _ : IsFibrant
      ((PointedCGWH.basedPathCospan.obj X).obj
        WalkingCospan.right) := by
    change IsFibrant (0 : PointedCGWH.{u, v})
    infer_instance
  let _ : Fibration
      ((PointedCGWH.basedPathCospan.obj X).map
        WalkingCospan.Hom.inl) := by
    change Fibration (PointedCGWH.basedPathEndpoint.app X)
    infer_instance
  have hComparison : WeakEquivalence
      (HomotopicalAlgebra.homotopyPullbackComparison.app
        (PointedCGWH.basedPathCospan.obj X)) :=
    HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_inl
      (PointedCGWH.basedPathCospan.obj X)
  set_option backward.isDefEq.respectTransparency false in
    change WeakEquivalence
      (PointedCGWH.loopBasedPathPullbackIso.hom.app X ≫
        HomotopicalAlgebra.homotopyPullbackComparison.app
          (PointedCGWH.basedPathCospan.obj X))
    rw [HomotopicalAlgebra.weakEquivalence_iff]
    exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _
      (mem_weakEquivalences
        (PointedCGWH.loopBasedPathPullbackIso.hom.app X))
      hComparison.mem

private theorem strictLoopDerives :
    (FibrantObject.localizerMorphism PointedCGWH.{u, v}).Derives
      (PointedCGWH.loop.{u, v} ⋙
        (weakEquivalences PointedCGWH.{u, v}).Q) := by
  intro X Y f hf
  let _ : WeakEquivalence f.hom := by
    rw [← weakEquivalence_iff_of_objectProperty,
      HomotopicalAlgebra.weakEquivalence_iff]
    exact hf
  let _ : WeakEquivalence (PointedCGWH.loop.map f.hom) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := PointedCGWH.suspensionLoopAdjunction.{u, v}) f.hom
  apply Localization.inverts
    (weakEquivalences PointedCGWH.{u, v}).Q
    (weakEquivalences PointedCGWH.{u, v})
  change weakEquivalences PointedCGWH.{u, v}
    (PointedCGWH.loop.map f.hom)
  rw [← HomotopicalAlgebra.weakEquivalence_iff]
  exact inferInstanceAs
    (WeakEquivalence (PointedCGWH.loop.map f.hom))

private theorem rightComparison_isIso_app
    (X : PointedCGWH.{u, v}) :
    IsIso
      ((HomotopicalAlgebra.quillenDerivedAdjunctionData
        PointedCGWH.suspensionLoopAdjunction.{u, v}).rightComparison.app X) := by
  let _ : IsFibrant X :=
    (PointedCGWH.isFibrant_iff X).2
      (CGWH.modelCategory.allObjectsFibrant X.right)
  let data := HomotopicalAlgebra.quillenDerivedAdjunctionData
    PointedCGWH.suspensionLoopAdjunction.{u, v}
  let _ : data.rightDerived.IsRightDerivedFunctor
      data.rightComparison
      (weakEquivalences PointedCGWH.{u, v}) :=
    data.rightIsDerived
  exact strictLoopDerives.isIso_of_isRightDerivedFunctor
    data.rightComparison (FibrantObject.mk X)

private theorem derivedWhiskeredLeg_isIso :
    let Q := (weakEquivalences PointedCGWH.{u, v}).Q
    IsIso (Functor.whiskerRight
      PointedCGWH.derivedLoopToNativePathHomotopyLoop Q) := by
  let Q := (weakEquivalences PointedCGWH.{u, v}).Q
  let α := Functor.whiskerRight
    PointedCGWH.derivedLoopToNativePathHomotopyLoop Q
  let _ (X : PointedCGWH.{u, v}) : IsIso (α.app X) := by
    change IsIso
      (Q.map
        (PointedCGWH.derivedLoopToNativePathHomotopyLoop.app X))
    rw [← HomotopicalAlgebra.weakEquivalence_iff_isIso_toHomotopyCategory_map]
    exact
      (PointedCGWH.derivedLoopToNativePathHomotopyLoop_weakEquivalence X).mem
  exact NatIso.isIso_of_isIso_app α

private theorem strictWhiskeredLeg_isIso :
    let Q := (weakEquivalences PointedCGWH.{u, v}).Q
    IsIso (Functor.whiskerRight
      PointedCGWH.loopToNativePathHomotopyLoop Q) := by
  let Q := (weakEquivalences PointedCGWH.{u, v}).Q
  let β := Functor.whiskerRight
    PointedCGWH.loopToNativePathHomotopyLoop Q
  let _ (X : PointedCGWH.{u, v}) : IsIso (β.app X) := by
    change IsIso
      (Q.map (PointedCGWH.loopToNativePathHomotopyLoop.app X))
    rw [← HomotopicalAlgebra.weakEquivalence_iff_isIso_toHomotopyCategory_map]
    exact
      (PointedCGWH.loopToNativePathHomotopyLoop_weakEquivalence X).mem
  exact NatIso.isIso_of_isIso_app β

private theorem rightComparison_isIso :
    IsIso
      (HomotopicalAlgebra.quillenDerivedAdjunctionData
        PointedCGWH.suspensionLoopAdjunction.{u, v}).rightComparison := by
  let data := HomotopicalAlgebra.quillenDerivedAdjunctionData
    PointedCGWH.suspensionLoopAdjunction.{u, v}
  let _ (X : PointedCGWH.{u, v}) :
      IsIso (data.rightComparison.app X) :=
    rightComparison_isIso_app X
  exact NatIso.isIso_of_isIso_app data.rightComparison

/-- In the homotopy category, the chosen derived loop is canonically
isomorphic to the localized strict native loop. -/
noncomputable def modelCategory.derivedLoopLocalizationIsoLoop :
    let Q := (weakEquivalences PointedCGWH.{u, v}).Q
    HomotopicalAlgebra.derivedLoop
        (C := PointedCGWH.{u, v}) ⋙ Q ≅
      PointedCGWH.loop.{u, v} ⋙ Q := by
  let Q := (weakEquivalences PointedCGWH.{u, v}).Q
  let αQ := Functor.whiskerRight
    PointedCGWH.derivedLoopToNativePathHomotopyLoop Q
  let βQ := Functor.whiskerRight
    PointedCGWH.loopToNativePathHomotopyLoop Q
  let _ : IsIso αQ := derivedWhiskeredLeg_isIso
  let _ : IsIso βQ := strictWhiskeredLeg_isIso
  exact (asIso αQ).trans (asIso βQ).symm

/-- The localized chosen derived loop agrees with the canonical total
right-derived functor of strict native loops. -/
noncomputable def modelCategory.derivedLoopLocalizationIsoRightDerived :
    let Q := (weakEquivalences PointedCGWH.{u, v}).Q
    let data := HomotopicalAlgebra.quillenDerivedAdjunctionData
      PointedCGWH.suspensionLoopAdjunction.{u, v}
    HomotopicalAlgebra.derivedLoop
        (C := PointedCGWH.{u, v}) ⋙ Q ≅
      Q ⋙ data.rightDerived := by
  let data := HomotopicalAlgebra.quillenDerivedAdjunctionData
    PointedCGWH.suspensionLoopAdjunction.{u, v}
  let _ : IsIso data.rightComparison := rightComparison_isIso
  exact PointedCGWH.modelCategory.derivedLoopLocalizationIsoLoop.trans
    (asIso data.rightComparison)

end PointedCGWH
