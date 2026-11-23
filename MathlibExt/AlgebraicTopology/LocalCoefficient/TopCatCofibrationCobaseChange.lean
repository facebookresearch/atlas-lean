/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatOpenCoverExcision
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatRelativeSquareMap
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetRelativeLeftBaseComparison
public import MathlibExt.Topology.Category.TopCat.DoubleMappingCylinderRetunedPair
public import MathlibExt.Topology.Category.TopCat.DoubleMappingCylinderOverlapHomotopy
public import Mathlib.Topology.Category.TopCat.EpiMono

import Mathlib.Tactic.NormNum

/-!
# Cobase change of an original acyclic cofibration with all integer systems

The one actual double mapping cylinder supplies both open collar
retractions and the actual relative collapse. The HEP-retuned original
cofibration pair lies strictly in (V,O). Its original relative acyclicity
passes through the actual open-excision and H/U quotient maps. Composing
the original coefficient map with the actual collapse gives the same j.

The exact original (B,X)→(pushout i f,H) map is a quasi-isomorphism because
both of its ORIGINAL relative complexes are derived acyclic. Its actual
projection square is retained. The final constructed-plus application
derives the all-system premise for i from canonical existence; it does not
ask its caller for an excision, weak, kernel or extension witness.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomotopicalAlgebra AlgebraicTopology
open scoped TopCat.modelCategory

universe u

namespace TopCat

private theorem acyclic_target_of_quasiIso
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L)
    (hf : QuasiIso f) (hK : K.Acyclic) : L.Acyclic := by
  intro n
  exact (quasiIsoAt_iff_exactAt f n (hK n)).mp ((quasiIso_iff f).mp hf n)

private theorem acyclic_source_of_quasiIso
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L)
    (hf : QuasiIso f) (hL : L.Acyclic) : K.Acyclic := by
  intro n
  exact (quasiIsoAt_iff_exactAt' f n (hL n)).mp ((quasiIso_iff f).mp hf n)

private theorem quasiIso_of_both_acyclic
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L)
    (hK : K.Acyclic) (hL : L.Acyclic) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt f n (hK n)).mpr (hL n)

private theorem subspaceIncl_mono {D : TopCat.{u}} (S : Set D) : Mono (subspaceIncl S) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

private theorem mono_between_subspaces
    {D : TopCat.{u}} {S T : Set D} (f : TopCat.of S ⟶ TopCat.of T)
    (hf : f ≫ subspaceIncl T = subspaceIncl S) : Mono f := by
  apply (TopCat.mono_iff_injective f).mpr
  intro x y hxy
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom hf x).symm.trans
    ((congrArg (subspaceIncl T).hom hxy).trans (ConcreteCategory.congr_hom hf y))

private theorem mappingCylinderSource_mono_without_hyp
    {X B : TopCat.{u}} (i : X ⟶ B) : Mono (mappingCylinderSource i) := by
  apply (TopCat.mono_iff_injective _).mpr
  intro x y hxy
  have hNamed : IsPushout (mappingCylinderEndpoint X 1) i
      (mappingCylinderCylinder i) (mappingCylinderTarget i) := by
    rw [mappingCylinderCylinder_eq, mappingCylinderTarget_eq]
    exact IsPushout.of_hasPushout (mappingCylinderEndpoint X 1) i
  let sq := hNamed.flip.map (forget TopCat)
  have hx : (x, (0 : TopCat.I.{u})) ∉ Set.range (mappingCylinderEndpoint X 1).hom := by
    rintro ⟨z, hz⟩
    rw [mappingCylinderEndpoint_apply] at hz
    have ht := congrArg Prod.snd hz
    have hr := congrArg (fun t : TopCat.I.{u} => (TopCat.I.homeomorph t : ℝ)) ht
    norm_num [TopCat.I.homeomorph_zero, TopCat.I.homeomorph_one] at hr
  rw [mappingCylinderSource_apply, mappingCylinderSource_apply] at hxy
  have h := Types.pushoutCocone_inr_eq_inr_of_not_mem_range_of_isColimit
    sq.isColimit hx hxy
  exact congrArg Prod.fst h

private theorem mono_of_cofibration_through_original_cylinder
    {X B : TopCat.{u}} (i : X ⟶ B) [Cofibration i] : Mono i := by
  let e := mappingCylinderPairEquivalence i
  have hs := (TopCat.mono_iff_injective (mappingCylinderSource i)).mp
    (mappingCylinderSource_mono_without_hyp i)
  apply (TopCat.mono_iff_injective i).mpr
  intro x y hxy
  apply hs
  exact (ConcreteCategory.congr_hom e.inverse_source x).symm.trans
    ((congrArg e.inverse.hom hxy).trans (ConcreteCategory.congr_hom e.inverse_source y))

private theorem doubleMappingCylinderH_mono
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) : Mono (doubleMappingCylinderH i f) := by
  let a := doubleMappingCylinderHToOpenH i f
  let r := doubleMappingCylinderOpenHRetraction i f
  let U := doubleMappingCylinderOpenH i f
  let : Mono a := (TopCat.mono_iff_injective a).mpr
    (Function.LeftInverse.injective (fun h =>
      ConcreteCategory.congr_hom (doubleMappingCylinderHToOpenH_retraction i f) h))
  let : Mono (subspaceIncl (U : Set (doubleMappingCylinder i f))) := subspaceIncl_mono _
  have hm : Mono (a ≫ subspaceIncl (U : Set (doubleMappingCylinder i f))) := inferInstance
  exact (doubleMappingCylinderHToOpenH_inclusion i f) ▸ hm

private theorem pushoutInr_mono_from_relative_collapse
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    Mono (pushout.inr i f) := by
  let e := doubleMappingCylinderPairEquivalence i f
  have hd := (TopCat.mono_iff_injective (doubleMappingCylinderH i f)).mp
    (doubleMappingCylinderH_mono i f)
  apply (TopCat.mono_iff_injective _).mpr
  intro h k hEq
  apply hd
  exact (ConcreteCategory.congr_hom e.inverse_H h).symm.trans
    ((congrArg e.inverse.hom hEq).trans (ConcreteCategory.congr_hom e.inverse_H k))

private theorem singular_weak_of_original
    {A B : TopCat.{u}} (f : A ⟶ B) (hf : TopCat.weakHomotopyEquivalences f) :
    SSet.realizationWeakEquivalences (TopCat.toSSet.map f) := by
  let : SSet.KanComplex (TopCat.toSSet.obj A) := TopCat.toSSet_obj_kanComplex A
  let : SSet.KanComplex (TopCat.toSSet.obj B) := TopCat.toSSet_obj_kanComplex B
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
    ((TopCat.mem_weakHomotopyEquivalences_iff f).mp hf)

private theorem midpoint_weak
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.weakHomotopyEquivalences (doubleMappingCylinderMidpoint i f) := by
  let e := doubleMappingCylinderOverlapHomotopyEquiv i f
  apply TopCat.mem_of_eq_toFun e.1.symm
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun k => k x) e.2.2.symm

private theorem HToOpenH_weak
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.weakHomotopyEquivalences (doubleMappingCylinderHToOpenH i f) := by
  have hr := doubleMappingCylinderOpenHRetraction_mem_weakHomotopyEquivalences i f
  have hComp : TopCat.weakHomotopyEquivalences
      (doubleMappingCylinderHToOpenH i f ≫ doubleMappingCylinderOpenHRetraction i f) := by
    rw [doubleMappingCylinderHToOpenH_retraction]
    exact TopCat.weakHomotopyEquivalences.of_isIso _
  exact TopCat.weakHomotopyEquivalences.of_postcomp _ _ hr hComp

private theorem pushout_inr_singular_quasiIso
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i]
    (hi : TopCat.IsLocalCoefficientHomologyEquivalence i) (f : X ⟶ H)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj (pushout i f))) :
    QuasiIso (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (pushout.inr i f)) L) := by
  let D := doubleMappingCylinder i f
  let U := doubleMappingCylinderOpenH i f
  let V := doubleMappingCylinderOpenB i f
  let O := doubleMappingCylinderOverlap i f
  let u : TopCat.of (U : Set D) ⟶ D := subspaceIncl (U : Set D)
  let v : TopCat.of (V : Set D) ⟶ D := subspaceIncl (V : Set D)
  let o : TopCat.of (O : Set D) ⟶ D := subspaceIncl (O : Set D)
  let ov := doubleMappingCylinderOverlapToOpenB i f
  let h := doubleMappingCylinderH i f
  let hu := doubleMappingCylinderHToOpenH i f
  let g := doubleMappingCylinderRetunedB i f
  let m := doubleMappingCylinderMidpoint i f
  let q := doubleMappingCylinderProjection i f
  let j := pushout.inr i f
  let LD := L.pullback (TopCat.toSSet.map q)
  let LV := LD.pullback (TopCat.toSSet.map v)
  let sq : CommSq i m g ov := ⟨doubleMappingCylinderRetunedB_source i f⟩
  let a := localCoefficientRelativeSquareSourceArrow i m g ov sq LV
  let : Mono i := mono_of_cofibration_through_original_cylinder i
  let : Mono (TopCat.toSSet.map i) := inferInstance
  let : Mono u := subspaceIncl_mono _
  let : Mono v := subspaceIncl_mono _
  let : Mono o := subspaceIncl_mono _
  let : Mono ov := mono_between_subspaces ov (doubleMappingCylinderOverlapToOpenB_inclusion i f)
  let : Mono (TopCat.toSSet.map ov) := inferInstance
  let : Mono a := by
    change Mono (localCoefficientRelativeSquareSourceArrow i m g ov sq LV)
    rw [localCoefficientRelativeSquareSourceArrow_eq i m g ov sq LV]
    exact SSet.localCoefficientChainMapOver_mono _ _ _ _ LV
  have hSourceQI : QuasiIso a := by
    change QuasiIso (localCoefficientRelativeSquareSourceArrow i m g ov sq LV)
    rw [localCoefficientRelativeSquareSourceArrow_eq i m g ov sq LV]
    exact SSet.localCoefficientChainMapOver_quasiIso_of_pullback _ _ _ _ LV
      (TopCat.IsLocalCoefficientHomologyEquivalence.quasiIso_singularPullbackChainMap
        i hi (LV.pullback (TopCat.toSSet.map g)))
  have hSource : (cokernel a).Acyclic := (quasiIso_iff_acyclic_cokernel a).mp hSourceQI
  let φ := localCoefficientRelativeSquareMap i m g ov sq LV
  have hφ : QuasiIso φ := localCoefficientRelativeSquareMap_quasiIso_of_weak_mates
    i m g ov sq (midpoint_weak i f)
        (doubleMappingCylinderRetunedB_mem_weakHomotopyEquivalences i f) LV
  have hVO : (cokernel (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map ov) LV)).Acyclic :=
    acyclic_target_of_quasiIso φ hφ hSource
  let : Mono (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map ov) LV) :=
    SSet.localCoefficientPullbackChainMap_mono_of_mono _ _
  have hOV : QuasiIso (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map ov) LV) :=
    (quasiIso_iff_acyclic_cokernel _).mpr hVO
  let s : TopCat.of ↥(Set.inter (U : Set D) (V : Set D)) ⟶
      TopCat.of (V : Set D) :=
    @subspaceInclOfSubset D (Set.inter (U : Set D) (V : Set D)) (V : Set D)
      Set.inter_subset_right
  have hs : s = ov := by
    apply (cancel_mono v).mp
    rw [subspaceInclOfSubset_comp, doubleMappingCylinderOverlapToOpenB_inclusion]
    rfl
  let : Mono s := by
    rw [hs]
    infer_instance
  let : Mono (TopCat.toSSet.map s) := inferInstance
  let : Mono (TopCat.toSSet.map
      (@subspaceInclOfSubset D (Set.inter (U : Set D) (V : Set D)) (V : Set D)
        Set.inter_subset_right)) := by
    change Mono (TopCat.toSSet.map s)
    infer_instance
  have hOV' : QuasiIso (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map s) LV) :=
      hs.symm ▸ hOV
  let eS := localCoefficientExcisionSourceArrow D U V LD
  let : Mono eS := by
    change Mono (localCoefficientExcisionSourceArrow D (U : Set D) (V : Set D) LD)
    rw [localCoefficientExcisionSourceArrow_eq D (U : Set D) (V : Set D) LD,
      localCoefficientSingularSubspaceMap_eq]
    exact SSet.localCoefficientChainMapOver_mono _ _ _ _ LD
  have heS : QuasiIso eS := by
    change QuasiIso (localCoefficientExcisionSourceArrow D (U : Set D) (V : Set D) LD)
    rw [localCoefficientExcisionSourceArrow_eq D (U : Set D) (V : Set D) LD,
      localCoefficientSingularSubspaceMap_eq]
    exact SSet.localCoefficientChainMapOver_quasiIso_of_pullback _ _ _ _ LD hOV'
  have heSA : (cokernel eS).Acyclic := (quasiIso_iff_acyclic_cokernel eS).mp heS
  let e := localCoefficientExcisionChainMap D U V LD
  have he : QuasiIso e := localCoefficientExcisionChainMap_quasiIso_of_openCover
    D U V (doubleMappingCylinderOpen_cover i f) LD
  have hUA := acyclic_target_of_quasiIso e he heSA
  rw [localCoefficientExcisionTargetArrow_eq] at hUA
  let : Mono h := doubleMappingCylinderH_mono i f
  let : Mono (TopCat.toSSet.map h) := inferInstance
  let : Mono (TopCat.toSSet.map u) := inferInstance
  have hhu : TopCat.toSSet.map h = TopCat.toSSet.map hu ≫ TopCat.toSSet.map u := by
    rw [← TopCat.toSSet.map_comp, doubleMappingCylinderHToOpenH_inclusion]
  let ψ := SSet.localCoefficientRelativeLeftBaseMap
    (TopCat.toSSet.map hu) (TopCat.toSSet.map u) (TopCat.toSSet.map h) hhu LD
  have hψ : QuasiIso ψ := SSet.localCoefficientRelativeLeftBaseMap_quasiIso_of_weak
    (TopCat.toSSet.map hu) (singular_weak_of_original hu (HToOpenH_weak i f))
    (TopCat.toSSet.map u) (TopCat.toSSet.map h) hhu LD
  have hHA := acyclic_source_of_quasiIso ψ hψ hUA
  let : Mono (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map h) LD) :=
    SSet.localCoefficientPullbackChainMap_mono_of_mono _ _
  have hH : QuasiIso (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map h) LD) :=
    (quasiIso_iff_acyclic_cokernel _).mpr hHA
  have hq : SSet.realizationWeakEquivalences (TopCat.toSSet.map q) :=
    singular_weak_of_original q (doubleMappingCylinderProjection_mem_weakHomotopyEquivalences i f)
  have hj : TopCat.toSSet.map j = TopCat.toSSet.map h ≫ TopCat.toSSet.map q := by
    rw [← TopCat.toSSet.map_comp, doubleMappingCylinderProjection_H]
  let c := SSet.localCoefficientChainMapOver (TopCat.toSSet.map h) (TopCat.toSSet.map q)
    (TopCat.toSSet.map j) hj L
  let b := SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map q) L
  let : QuasiIso c := SSet.localCoefficientChainMapOver_quasiIso_of_pullback _ _ _ _ L hH
  letI : QuasiIso b :=
      SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap_allComponents
    (TopCat.toSSet.map q) hq L
  have hcb : QuasiIso (c ≫ b) := inferInstance
  rw [SSet.localCoefficientChainMapOver_comp] at hcb
  exact hcb

private theorem originalPushoutSource_quasiIso
    {X B H : TopCat.{u}} (i : X ⟶ B)
    (hi : TopCat.IsLocalCoefficientHomologyEquivalence i) (f : X ⟶ H)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj (pushout i f))) :
    QuasiIso (localCoefficientPushoutRelativeSourceArrow i f L) := by
  rw [localCoefficientPushoutRelativeSourceArrow_eq]
  exact SSet.localCoefficientChainMapOver_quasiIso_of_pullback _ _ _ _ L
    (TopCat.IsLocalCoefficientHomologyEquivalence.quasiIso_singularPullbackChainMap
      i hi (L.pullback (TopCat.toSSet.map (pushout.inl i f))))

/-- The EXACT original relative pair map in an acyclic cofibration's
cobase change is a quasi-isomorphism for every integer target system. Both
original relative complexes are derived acyclic using the actual collar. -/
public theorem localCoefficientPushoutRelativeMap_quasiIso_of_acyclic_cofibration
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i]
    (hi : TopCat.IsLocalCoefficientHomologyEquivalence i) (f : X ⟶ H)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj (pushout i f))) :
    QuasiIso (localCoefficientPushoutRelativeMap i f L) := by
  let a := localCoefficientPushoutRelativeSourceArrow i f L
  let j := pushout.inr i f
  let : Mono i := mono_of_cofibration_through_original_cylinder i
  let : Mono (TopCat.toSSet.map i) := inferInstance
  let : Mono j := pushoutInr_mono_from_relative_collapse i f
  let : Mono (TopCat.toSSet.map j) := inferInstance
  let : Mono a := by
    change Mono (localCoefficientPushoutRelativeSourceArrow i f L)
    rw [localCoefficientPushoutRelativeSourceArrow_eq i f L]
    exact SSet.localCoefficientChainMapOver_mono _ _ _ _ L
  have ha : QuasiIso a := originalPushoutSource_quasiIso i hi f L
  have hA := (quasiIso_iff_acyclic_cokernel a).mp ha
  let b := SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map j) L
  let : Mono b := SSet.localCoefficientPullbackChainMap_mono_of_mono _ _
  have hb : QuasiIso b := pushout_inr_singular_quasiIso i hi f L
  have hB := (quasiIso_iff_acyclic_cokernel b).mp hb
  exact quasiIso_of_both_acyclic (localCoefficientPushoutRelativeMap i f L) hA hB

/-- Acyclic cofibrations remain ORIGINAL all-integer-local-system
homology equivalences under cobase change into arbitrary H. The exact
relative map above and source acyclicity derive the actual j comparison. -/
public theorem IsLocalCoefficientHomologyEquivalence.pushout_inr
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i]
    (hi : TopCat.IsLocalCoefficientHomologyEquivalence i) (f : X ⟶ H) :
    TopCat.IsLocalCoefficientHomologyEquivalence (pushout.inr i f) := by
  let j := pushout.inr i f
  intro L n
  let ES := TopCat.LocalSystem.singularPullbackIso j L
  let c := SSet.localCoefficientChainMap ES.inv
  let e := (SSet.localCoefficientChainComplexFunctor (R := ℤ) (X := TopCat.toSSet.obj H)).mapIso ES
  let : IsIso c := by
    change IsIso e.inv
    infer_instance
  let a := localCoefficientPushoutRelativeSourceArrow i f L.toSingular
  let b := SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map j) L.toSingular
  let : Mono i := mono_of_cofibration_through_original_cylinder i
  let : Mono (TopCat.toSSet.map i) := inferInstance
  let : Mono j := pushoutInr_mono_from_relative_collapse i f
  let : Mono (TopCat.toSSet.map j) := inferInstance
  let : Mono a := by
    change Mono (localCoefficientPushoutRelativeSourceArrow i f L.toSingular)
    rw [localCoefficientPushoutRelativeSourceArrow_eq i f L.toSingular]
    exact SSet.localCoefficientChainMapOver_mono _ _ _ _ L.toSingular
  let : Mono b := SSet.localCoefficientPullbackChainMap_mono_of_mono _ _
  have hSource := (quasiIso_iff_acyclic_cokernel a).mp
    (originalPushoutSource_quasiIso i hi f L.toSingular)
  have hMap := localCoefficientPushoutRelativeMap_quasiIso_of_acyclic_cofibration i hi f
      L.toSingular
  have hTarget := acyclic_target_of_quasiIso
      (localCoefficientPushoutRelativeMap i f L.toSingular) hMap hSource
  let : QuasiIso b := (quasiIso_iff_acyclic_cokernel b).mpr hTarget
  let : QuasiIso (TopCat.localCoefficientPullbackChainMap j L) := by
    change QuasiIso (c ≫ SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map j) L.toSingular)
    infer_instance
  change IsIso (HomologicalComplex.homologyMap (TopCat.localCoefficientPullbackChainMap j L) n)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

end TopCat

end
