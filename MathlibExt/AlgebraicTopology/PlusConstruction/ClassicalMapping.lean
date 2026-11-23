/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalMappingGeometry
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatCofibrationCobaseChange
public import MathlibExt.Topology.Category.TopCat.DoubleMappingCylinderOpenCharts
public import MathlibExt.Topology.Category.TopCat.DoubleMappingCylinderOverlapHomotopy
public import MathlibExt.Topology.Homotopy.VanKampenMapEndDescent
public import MathlibExt.Topology.Homotopy.VanKampenFullness
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Actual collar calibration for plus-map extension

This source is being assembled against the single original double mapping
cylinder. The private calibration below uses its computed inverse and both
relative homotopies. The final map theorem will derive the actual pushout
fundamental-group and coefficient properties before using a lifting property.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomotopicalAlgebra TopCat
open MathlibExt.Topology.Homotopy.VanKampenWanted
open scoped TopCat.modelCategory ContinuousMap

universe u

namespace AlgebraicTopology.LoopCellIndependentPlus

private theorem groupoid_comp_of_square
    {A B C D : TopCat.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (h : a ≫ b = c ≫ d) :
    FundamentalGroupoid.map a.hom ⋙ FundamentalGroupoid.map b.hom =
      FundamentalGroupoid.map c.hom ⋙ FundamentalGroupoid.map d.hom := by
  have he : b.hom.comp a.hom = d.hom.comp c.hom :=
    (TopCat.hom_comp a b).symm.trans
      ((congrArg (fun k : A ⟶ D => k.hom) h).trans (TopCat.hom_comp c d))
  exact (FundamentalGroupoid.map_comp b.hom a.hom).symm.trans
    ((congrArg FundamentalGroupoid.map he).trans
      (FundamentalGroupoid.map_comp d.hom c.hom))

private theorem groupoid_comp_of_retraction
    {A B : TopCat.{u}} (s : A ⟶ B) (r : B ⟶ A) (h : s ≫ r = 𝟙 A) :
    FundamentalGroupoid.map s.hom ⋙ FundamentalGroupoid.map r.hom =
      𝟭 (FundamentalGroupoid A) := by
  have he : r.hom.comp s.hom = ContinuousMap.id A :=
    (TopCat.hom_comp s r).symm.trans
      ((congrArg (fun k : A ⟶ A => k.hom) h).trans (TopCat.hom_id (X := A)))
  exact (FundamentalGroupoid.map_comp r.hom s.hom).symm.trans
    ((congrArg FundamentalGroupoid.map he).trans (FundamentalGroupoid.map_id (X := A)))

private theorem end_values_eq_of_point_eq
    {A : Type u} [TopologicalSpace A] {G : Type u} [Group G]
    (F K : FundamentalGroupoid A ⥤ SingleObj G) {a b : A} (h : b = a)
    (he : ∀ q : FundamentalGroup A a, (F.map q.asHom : G) = (K.map q.asHom : G)) :
    ∀ q : FundamentalGroup A b, (F.map q.asHom : G) = (K.map q.asHom : G) := by
  cases h
  exact he

private theorem groupoid_isEquivalence_of_calibratedHomotopyEquiv
    {A B : TopCat.{u}} (q : A ⟶ B) (e : A ≃ₕ B) (he : e.toFun = q.hom) :
    (FundamentalGroupoid.map q.hom).IsEquivalence := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  have hF : E.functor = FundamentalGroupoid.map q.hom := by
    change FundamentalGroupoid.map e.toFun = FundamentalGroupoid.map q.hom
    exact congrArg FundamentalGroupoid.map he
  rw [← hF]
  exact E.isEquivalence_functor

private def actualOpenHEquivalence
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ≃ₕ H := by
  let U := TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f))
  let r := doubleMappingCylinderOpenHRetraction i f
  let a := doubleMappingCylinderHToOpenH i f
  have hr : r.hom.comp a.hom = ContinuousMap.id H :=
    (TopCat.hom_comp a r).symm.trans
      ((congrArg (fun k : H ⟶ H => k.hom) (doubleMappingCylinderHToOpenH_retraction i f)).trans
        (TopCat.hom_id (X := H)))
  exact
    { toFun := r.hom
      invFun := a.hom
      left_inv := ⟨(doubleMappingCylinderOpenHHomotopy i f).symm.toHomotopy.cast
        (TopCat.hom_comp r a) (TopCat.hom_id (X := U))⟩
      right_inv := ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id H)).cast hr.symm rfl⟩ }

private def actualOpenBEquivalence
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) ≃ₕ B := by
  let V := TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f))
  let r := doubleMappingCylinderOpenBRetraction i f
  let a := doubleMappingCylinderBToOpenB i f
  have hr : r.hom.comp a.hom = ContinuousMap.id B :=
    (TopCat.hom_comp a r).symm.trans
      ((congrArg (fun k : B ⟶ B => k.hom) (doubleMappingCylinderBToOpenB_retraction i f)).trans
        (TopCat.hom_id (X := B)))
  exact
    { toFun := r.hom
      invFun := a.hom
      left_inv := ⟨(doubleMappingCylinderOpenBHomotopy i f).symm.toHomotopy.cast
        (TopCat.hom_comp r a) (TopCat.hom_id (X := V))⟩
      right_inv := ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id B)).cast hr.symm rfl⟩ }

private theorem bijective_mapOfEq_of_calibratedHomotopyEquiv
    {A B : TopCat.{u}} (q : A ⟶ B) (e : A ≃ₕ B) (he : e.toFun = q.hom)
    (a : A) (b : B) (hab : q a = b) :
    Function.Bijective (FundamentalGroup.mapOfEq q.hom hab) := by
  let F := FundamentalGroupoid.map q.hom
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  have hF : E.functor = F := by
    change FundamentalGroupoid.map e.toFun = FundamentalGroupoid.map q.hom
    exact congrArg FundamentalGroupoid.map he
  let : F.IsEquivalence := by
    rw [← hF]
    exact E.isEquivalence_functor
  have hm : Function.Bijective (F.mapEnd (FundamentalGroupoid.mk a)) := by
    constructor
    · intro p r h
      apply End.ext
      exact F.map_injective
        (congrArg (fun z : End (F.obj (FundamentalGroupoid.mk a)) => z.asHom) h)
    · intro p
      obtain ⟨r, hr⟩ := F.map_surjective p.asHom
      exact ⟨End.of r, by apply End.ext; exact hr⟩
  change Function.Bijective
    ((eqToIso (congrArg FundamentalGroupoid.mk hab)).conj.toMonoidHom.comp
      (F.mapEnd (FundamentalGroupoid.mk a)))
  exact (eqToIso (congrArg FundamentalGroupoid.mk hab)).conj.bijective.comp hm

private def actualDoubleCylinderEquivalence
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    doubleMappingCylinder i f ≃ₕ (pushout i f : TopCat.{u}) := by
  let q := doubleMappingCylinderProjection i f
  let s := doubleMappingCylinderPairEquivalence i f
  exact
    { toFun := q.hom
      invFun := s.inverse.hom
      left_inv := ⟨s.cylinderHomotopy.symm.toHomotopy.cast
        (TopCat.hom_comp q s.inverse) (TopCat.hom_id (X := doubleMappingCylinder i f))⟩
      right_inv := ⟨s.pushoutHomotopy.symm.toHomotopy.cast
        (TopCat.hom_comp s.inverse q) (TopCat.hom_id (X := pushout i f))⟩ }

private theorem fundamentalGroupMapOfEq_congr
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (f g : C(A, B)) {a : A} {b : B} (hfg : f = g)
    (hf : f a = b) (hg : g a = b) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  cases hfg
  rfl

private theorem actualPushout_pi1_bijective_of_doubleCylinder
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H)
    (hD : ∀ h : H, Function.Bijective (FundamentalGroup.mapOfEq
      (doubleMappingCylinderH i f).hom (rfl : doubleMappingCylinderH i f h =
        doubleMappingCylinderH i f h))) :
    ∀ h : H, Function.Bijective (FundamentalGroup.mapOfEq
      (pushout.inr i f).hom (rfl : pushout.inr i f h = pushout.inr i f h)) := by
  intro h
  let d := doubleMappingCylinderH i f
  let q := doubleMappingCylinderProjection i f
  let j := pushout.inr i f
  have hpoint : q (d h) = j h :=
    ConcreteCategory.congr_hom (doubleMappingCylinderProjection_H i f) h
  have hq := bijective_mapOfEq_of_calibratedHomotopyEquiv q
    (actualDoubleCylinderEquivalence i f) rfl (d h) (j h) hpoint
  have heq : FundamentalGroup.mapOfEq (d ≫ q).hom hpoint =
      FundamentalGroup.mapOfEq j.hom rfl := by
    have hm : (d ≫ q).hom = j.hom :=
      congrArg (fun k : H ⟶ (pushout i f : TopCat.{u}) => k.hom)
        (doubleMappingCylinderProjection_H i f)
    exact fundamentalGroupMapOfEq_congr (d ≫ q).hom j.hom hm hpoint rfl
  have hcomp : FundamentalGroup.mapOfEq j.hom rfl =
      (FundamentalGroup.mapOfEq q.hom hpoint).comp
        (FundamentalGroup.mapOfEq d.hom rfl) :=
    heq.symm.trans (FundamentalGroup.mapOfEq_comp d.hom q.hom rfl hpoint hpoint)
  rw [hcomp]
  exact hq.comp (hD h)

private theorem actualDoubleCylinder_pi1_injective
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    ∀ h : H, Function.Injective (FundamentalGroup.mapOfEq
      (doubleMappingCylinderH i f).hom rfl (x := h)) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let B := LoopCellRegularThreeComparison.originalThree X x P
  let i := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let D := doubleMappingCylinder i f
  let U := (doubleMappingCylinderOpenH i f : Set D)
  let V := (doubleMappingCylinderOpenB i f : Set D)
  let O := TopCat.of (doubleMappingCylinderOverlap i f : Set D)
  let rH := doubleMappingCylinderOpenHRetraction i f
  let rB := doubleMappingCylinderOpenBRetraction i f
  let rO := doubleMappingCylinderOverlapProjection i f
  let tH := doubleMappingCylinderOverlapToOpenH i f
  let tB := doubleMappingCylinderOverlapToOpenB i f
  let I_L := FundamentalGroupoid.map (inclusionInterLeft U V)
  let I_R := FundamentalGroupoid.map (inclusionInterRight U V)
  have htH : tH.hom = inclusionInterLeft U V := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    change (tH p).val = p.val
    exact ConcreteCategory.congr_hom
      (doubleMappingCylinderOverlapToOpenH_inclusion i f) p
  have htB : tB.hom = inclusionInterRight U V := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    change (tB p).val = p.val
    exact ConcreteCategory.congr_hom
      (doubleMappingCylinderOverlapToOpenB_inclusion i f) p
  let eO := doubleMappingCylinderOverlapHomotopyEquiv i f
  let RO := FundamentalGroupoid.map rO.hom
  let : RO.IsEquivalence :=
    groupoid_isEquivalence_of_calibratedHomotopyEquiv rO eO.val eO.property.1
  let b : FundamentalGroupoid O := FundamentalGroupoid.mk (doubleMappingCylinderMidpoint i f x)
  let β (c : FundamentalGroupoid O) : b ⟶ c :=
    RO.preimage (Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath (rO (doubleMappingCylinderMidpoint i f x)) (rO c.as)))
  change ∀ h : H, Function.Injective (FundamentalGroup.mapOfEq
    (doubleMappingCylinderH i f).hom rfl (x := h))
  intro h
  let G := FundamentalGroup H h
  let B_H := Groupoid.basedFunctor (FundamentalGroupoid.mk h) (MonoidHom.id G)
  obtain ⟨Fplus, hdesc⟩ := originalInclusion_basedFunctor_end_desc X x P H f hkill h
  let F₀ := FundamentalGroupoid.map f.hom ⋙ B_H
  let Fi := FundamentalGroupoid.map i.hom ⋙ Fplus
  let F_U := FundamentalGroupoid.map rH.hom ⋙ B_H
  let F_V := FundamentalGroupoid.map rB.hom ⋙ Fplus
  have hbaseU : I_L ⋙ FundamentalGroupoid.map rH.hom =
      RO ⋙ FundamentalGroupoid.map f.hom :=
    (congrArg (fun K : FundamentalGroupoid O ⥤ FundamentalGroupoid U =>
      K ⋙ FundamentalGroupoid.map rH.hom) (congrArg FundamentalGroupoid.map htH).symm).trans
        (groupoid_comp_of_square tH rH rO f (doubleMappingCylinderOverlap_H_square i f))
  have hbaseV : I_R ⋙ FundamentalGroupoid.map rB.hom =
      RO ⋙ FundamentalGroupoid.map i.hom :=
    (congrArg (fun K : FundamentalGroupoid O ⥤ FundamentalGroupoid V =>
      K ⋙ FundamentalGroupoid.map rB.hom) (congrArg FundamentalGroupoid.map htB).symm).trans
        (groupoid_comp_of_square tB rB rO i (doubleMappingCylinderOverlap_B_square i f))
  have hfunU : I_L ⋙ F_U = RO ⋙ F₀ :=
    congrArg (fun K : FundamentalGroupoid O ⥤ FundamentalGroupoid H => K ⋙ B_H) hbaseU
  have hfunV : I_R ⋙ F_V = RO ⋙ Fi :=
    congrArg (fun K : FundamentalGroupoid O ⥤ FundamentalGroupoid B => K ⋙ Fplus) hbaseV
  have hEnd : ∀ e : End b, (F_U.map (I_L.map e.asHom) : G) =
      (F_V.map (I_R.map e.asHom) : G) := by
    intro e
    let z := rO (doubleMappingCylinderMidpoint i f x)
    let q : FundamentalGroup X z := RO.mapEnd b e
    have hz : z = x :=
      ConcreteCategory.congr_hom (doubleMappingCylinderMidpoint_projection i f) x
    have hq := end_values_eq_of_point_eq Fi F₀ hz hdesc q
    have hu := congrArg
      (fun K : FundamentalGroupoid O ⥤ SingleObj G => (K.map e.asHom : G)) hfunU
    have hv := congrArg
      (fun K : FundamentalGroupoid O ⥤ SingleObj G => (K.map e.asHom : G)) hfunV
    exact hu.trans (hq.symm.trans hv.symm)
  obtain ⟨F, hF_V, hOutside⟩ := exists_globalFunctor_of_overlap_mapEnd_eq
    (doubleMappingCylinderOpenH i f).isOpen (doubleMappingCylinderOpenB i f).isOpen
    (doubleMappingCylinderOpen_cover i f) F_U F_V b β hEnd
  let s := doubleMappingCylinderHToOpenH i f
  let d := doubleMappingCylinderH i f
  let tU : TopCat.of U ⟶ D := TopCat.ofHom (inclusionSub U)
  have hsd : s ≫ tU = d := by
    change s ≫ subspaceIncl (X := D) U = d
    exact doubleMappingCylinderHToOpenH_inclusion i f
  have hsdHom : tU.hom.comp s.hom = d.hom :=
    (TopCat.hom_comp s tU).symm.trans (congrArg (fun k : H ⟶ D => k.hom) hsd)
  have hmapD : FundamentalGroupoid.map d.hom =
      FundamentalGroupoid.map s.hom ⋙ FundamentalGroupoid.map tU.hom :=
    (congrArg FundamentalGroupoid.map hsdHom).symm.trans
      (FundamentalGroupoid.map_comp tU.hom s.hom)
  have hrestrict : FundamentalGroupoid.map s.hom ⋙ F_U = B_H :=
    (congrArg (fun K : FundamentalGroupoid H ⥤ FundamentalGroupoid H => K ⋙ B_H)
      (groupoid_comp_of_retraction s rH (doubleMappingCylinderHToOpenH_retraction i f))).trans
        (Functor.id_comp B_H)
  have hsPoint : (s h).val = d h :=
    ConcreteCategory.congr_hom (doubleMappingCylinderHToOpenH_inclusion i f) h
  have hidentity : ∀ q : G,
      (F.map ((FundamentalGroupoid.map d.hom).map q.asHom) : G) = q := by
    intro q
    have hp : (s h).val ∉ V := by
      intro hp
      exact (doubleMappingCylinderH_disjoint_openB i f h) (hsPoint ▸ hp)
    have hstep := hOutside (s h) hp ((FundamentalGroupoid.map s.hom).mapEnd
      (FundamentalGroupoid.mk h) q)
    have hstart := congrArg
      (fun K : FundamentalGroupoid H ⥤ SingleObj G => (K.map q.asHom : G))
      (congrArg (fun K : FundamentalGroupoid H ⥤ FundamentalGroupoid D => K ⋙ F) hmapD)
    have hend := congrArg
      (fun K : FundamentalGroupoid H ⥤ SingleObj G => (K.map q.asHom : G)) hrestrict
    exact hstart.trans (hstep.trans (hend.trans
      (Groupoid.basedFunctor_map_end (FundamentalGroupoid.mk h) (MonoidHom.id G) q)))
  let ρ : FundamentalGroup D (d h) →* G :=
    (SingleObj.toEnd G).symm.toMonoidHom.comp (F.mapEnd (FundamentalGroupoid.mk (d h)))
  have hleft : Function.LeftInverse ρ (FundamentalGroup.mapOfEq d.hom rfl) := by
    intro q
    rw [FundamentalGroup.mapOfEq_rfl]
    exact hidentity q
  exact hleft.injective

private theorem actualDoubleCylinder_pi1_surjective
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    ∀ h : H, Function.Surjective (FundamentalGroup.mapOfEq
      (doubleMappingCylinderH i f).hom rfl (x := h)) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let B := LoopCellRegularThreeComparison.originalThree X x P
  let i := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let D := doubleMappingCylinder i f
  let U := (doubleMappingCylinderOpenH i f : Set D)
  let V := (doubleMappingCylinderOpenB i f : Set D)
  let O := TopCat.of (doubleMappingCylinderOverlap i f : Set D)
  let I := FundamentalGroupoid.map i.hom
  have hi := originalInclusion_groupoid_full_essSurj X x P
  let : I.Full := hi.1
  let : I.EssSurj := hi.2
  let rO := doubleMappingCylinderOverlapProjection i f
  let rB := doubleMappingCylinderOpenBRetraction i f
  let tB := doubleMappingCylinderOverlapToOpenB i f
  let RO := FundamentalGroupoid.map rO.hom
  let RB := FundamentalGroupoid.map rB.hom
  let eO := doubleMappingCylinderOverlapHomotopyEquiv i f
  let : RO.IsEquivalence :=
    groupoid_isEquivalence_of_calibratedHomotopyEquiv rO eO.val eO.property.1
  let : RB.IsEquivalence :=
    groupoid_isEquivalence_of_calibratedHomotopyEquiv rB (actualOpenBEquivalence i f) rfl
  let I_R := FundamentalGroupoid.map (inclusionInterRight U V)
  have htB : tB.hom = inclusionInterRight U V := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    change (tB p).val = p.val
    exact ConcreteCategory.congr_hom
      (doubleMappingCylinderOverlapToOpenB_inclusion i f) p
  have hsquare : I_R ⋙ RB = RO ⋙ I :=
    (congrArg (fun K : FundamentalGroupoid O ⥤ FundamentalGroupoid V => K ⋙ RB)
      (congrArg FundamentalGroupoid.map htB).symm).trans
        (groupoid_comp_of_square tB rB rO i (doubleMappingCylinderOverlap_B_square i f))
  let : (I_R ⋙ RB).Full := Functor.Full.of_iso (eqToIso hsquare.symm)
  let : (I_R ⋙ RB).EssSurj := Functor.essSurj_of_iso (eqToIso hsquare.symm)
  let : I_R.Full := Functor.Full.of_comp_faithful I_R RB
  let : I_R.EssSurj := Functor.essSurj_of_comp_fully_faithful I_R RB
  let J := FundamentalGroupoid.map (inclusionSub U)
  let : J.Full := inclusionSub_full_of_interRight_full_essSurj
    (doubleMappingCylinderOpenH i f).isOpen (doubleMappingCylinderOpenB i f).isOpen
    (doubleMappingCylinderOpen_cover i f) (inferInstance : I_R.Full)
    (inferInstance : I_R.EssSurj)
  let s := doubleMappingCylinderHToOpenH i f
  let S := FundamentalGroupoid.map s.hom
  let : S.IsEquivalence :=
    groupoid_isEquivalence_of_calibratedHomotopyEquiv s (actualOpenHEquivalence i f).symm rfl
  let d := doubleMappingCylinderH i f
  let K := FundamentalGroupoid.map d.hom
  let tU : TopCat.of U ⟶ D := TopCat.ofHom (inclusionSub U)
  have hsd : s ≫ tU = d := by
    change s ≫ subspaceIncl (X := D) U = d
    exact doubleMappingCylinderHToOpenH_inclusion i f
  have hsdHom : tU.hom.comp s.hom = d.hom :=
    (TopCat.hom_comp s tU).symm.trans (congrArg (fun k : H ⟶ D => k.hom) hsd)
  have hmap : S ⋙ J = K :=
    (FundamentalGroupoid.map_comp tU.hom s.hom).symm.trans
      (congrArg FundamentalGroupoid.map hsdHom)
  let : K.Full := Functor.Full.of_iso (eqToIso hmap)
  change ∀ h : H, Function.Surjective (FundamentalGroup.mapOfEq
    (doubleMappingCylinderH i f).hom rfl (x := h))
  intro h q
  let target : K.obj (FundamentalGroupoid.mk h) ⟶ K.obj (FundamentalGroupoid.mk h) := q.asHom
  obtain ⟨p, hp⟩ := K.map_surjective target
  refine ⟨End.of p, ?_⟩
  rw [FundamentalGroup.mapOfEq_rfl]
  apply End.ext
  exact hp

/-- The literal original cobase-change inclusion has bijective ordinary
fundamental-group maps at EVERY target-source point. The collar End
retraction and full inclusion are derived; no groupoid pushout or map
isomorphism witness is supplied. -/
public theorem originalPushoutInclusion_pi1_bijective
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    ∀ h : H, Function.Bijective (FundamentalGroup.mapOfEq
      (pushout.inr i f).hom rfl (x := h)) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let i := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let : Cofibration i := originalInclusion_cofibration X x P
  have hD : ∀ h : H, Function.Bijective (FundamentalGroup.mapOfEq
      (doubleMappingCylinderH i f).hom rfl (x := h)) := fun h =>
    ⟨actualDoubleCylinder_pi1_injective X x P H f hkill h,
      actualDoubleCylinder_pi1_surjective X x P H f h⟩
  exact actualPushout_pi1_bijective_of_doubleCylinder i f hD

private def fixedHomotopyOfEq
    {A B : TopCat.{u}} (f g : A ⟶ B) (h : f = g) (S : Set A) :
    ContinuousMap.HomotopyRel f.hom g.hom S :=
  (ContinuousMap.HomotopyRel.refl g.hom S).cast
    (congrArg (fun k : A ⟶ B => k.hom) h).symm rfl

/-- The independently constructed ORIGINAL plus map admits an actual
factor into any target when the original fundamental-group map kills P.
The same actual pushout gives a retraction, BOTH whole-source-relative
inverse families, a strict source triangle, and relative uniqueness of
strict extensions. No coefficient, pi1, weak, retraction, extension,
inverse or relative-homotopy witness is supplied by the caller. -/
public theorem original_connected_CW_plus_map_extension
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let B := LoopCellRegularThreeComparison.originalThree X x P
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let W := pushout i f
    let a := pushout.inl i f
    let j := pushout.inr i f
    ∃ r : W ⟶ H, ∃ F : B ⟶ H,
      F = a ≫ r ∧ i ≫ F = f ∧ j ≫ r = 𝟙 H ∧
        Nonempty (ContinuousMap.HomotopyRel (i ≫ F).hom f.hom Set.univ) ∧
        Nonempty (ContinuousMap.HomotopyRel (j ≫ r).hom
          (𝟙 H : H ⟶ H).hom Set.univ) ∧
        Nonempty (ContinuousMap.HomotopyRel (r ≫ j).hom
          (𝟙 W : W ⟶ W).hom (Set.range j)) ∧
        ∀ G : B ⟶ H, i ≫ G = f →
          Nonempty (ContinuousMap.HomotopyRel F.hom G.hom (Set.range i)) ∧
            Nonempty (ContinuousMap.HomotopyRel G.hom F.hom (Set.range i)) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let B := LoopCellRegularThreeComparison.originalThree X x P
  let i := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let W := pushout i f
  let a := pushout.inl i f
  let j := pushout.inr i f
  let : Cofibration i := originalInclusion_cofibration X x P
  let : Cofibration j := inferInstance
  have hi : TopCat.IsLocalCoefficientHomologyEquivalence i :=
    (original_connected_CW_plus_construction_full X x P).2.1
  have hL : TopCat.IsLocalCoefficientHomologyEquivalence j :=
    TopCat.IsLocalCoefficientHomologyEquivalence.pushout_inr i hi f
  have hπ : ∀ h : H, Function.Bijective (FundamentalGroup.mapOfEq j.hom rfl (x := h)) :=
    originalPushoutInclusion_pi1_bijective X x P H f hkill
  have hw : TopCat.weakHomotopyEquivalences j :=
    TopCat.allLocalCoefficient_piOneIso_mem_weakHomotopyEquivalences j hL hπ
  let : WeakEquivalence j := (weakEquivalence_iff j).mpr hw
  obtain ⟨F, hF, hUnique⟩ := TopCat.exists_pushout_extension_of_trivialCofibration i f
  let r : W ⟶ H := pushout.desc F (𝟙 H) (hF.trans (Category.comp_id f).symm)
  have hr : j ≫ r = 𝟙 H := pushout.inr_desc _ _ _
  have hFar : a ≫ r = F := pushout.inl_desc _ _ _
  have hR : Nonempty (ContinuousMap.HomotopyRel
      (r ≫ j).hom (𝟙 W : W ⟶ W).hom (Set.range j)) :=
    TopCat.homotopyRel_of_trivialCofibration j (r ≫ j) (𝟙 W) (by
      rw [← Category.assoc, hr, Category.id_comp, Category.comp_id])
  refine ⟨r, F, hFar.symm, hF, hr, ⟨fixedHomotopyOfEq (i ≫ F) f hF Set.univ⟩,
    ⟨fixedHomotopyOfEq (j ≫ r) (𝟙 H) hr Set.univ⟩, hR, ?_⟩
  intro G hG
  have hFG := hUnique G hG
  exact ⟨hFG, ⟨hFG.some.symm⟩⟩

private theorem mapOfEq_eq_one_iff_imageEq
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (h : f a = b) (q : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq f h q = 1 ↔ FundamentalGroup.mapOfEq f rfl q = 1 := by
  cases h
  rfl

/-- A map carrying the selected perfect normal subgroup into the selected
target subgroup extends between the independently constructed actual plus
targets. The original source triangle and BOTH relative comparison families
are retained. The subgroup condition is on the actual source map. -/
public theorem original_subgroupPreserving_plus_map_extension
    (X Y : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]
    [ConnectedSpace Y] (x : X) (y : Y) (f : X ⟶ Y) (hxy : f x = y)
    (P : Subgroup (FundamentalGroup X x)) (Q : Subgroup (FundamentalGroup Y y))
    [P.Normal] [Group.IsPerfect P] [Q.Normal] [Group.IsPerfect Q]
    (hPQ : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom hxy p ∈ Q) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    letI : PathConnectedSpace Y :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl Y)
    let iX := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let iY := LoopCellAttachment.inclusion Y y Q ≫
      LoopCellRegularThreeComparison.originalThreeInclusion Y y Q
    ∃ F : LoopCellRegularThreeComparison.originalThree X x P ⟶
        LoopCellRegularThreeComparison.originalThree Y y Q,
      iX ≫ F = f ≫ iY ∧
        Nonempty (ContinuousMap.HomotopyRel (iX ≫ F).hom (f ≫ iY).hom Set.univ) ∧
        ∀ G, iX ≫ G = f ≫ iY →
          Nonempty (ContinuousMap.HomotopyRel F.hom G.hom (Set.range iX)) ∧
            Nonempty (ContinuousMap.HomotopyRel G.hom F.hom (Set.range iX)) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let : PathConnectedSpace Y :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl Y)
  let iY := LoopCellAttachment.inclusion Y y Q ≫
    LoopCellRegularThreeComparison.originalThreeInclusion Y y Q
  let g := f ≫ iY
  have hk := subgroupPreserving_composite_kills X Y x y f hxy P Q hPQ
  have hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq g.hom rfl p = 1 := by
    intro p hp
    exact (mapOfEq_eq_one_iff_imageEq g.hom (congrArg iY hxy) p).mp
      (MonoidHom.mem_ker.mp (hk hp))
  obtain ⟨r, F, hFr, hF, hr, htriangle, hleft, hright, hUnique⟩ :=
    original_connected_CW_plus_map_extension X x P _ g hkill
  exact ⟨F, hF, htriangle, hUnique⟩

end AlgebraicTopology.LoopCellIndependentPlus

end
