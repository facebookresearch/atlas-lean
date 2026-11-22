/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Path
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.Topology.Category.TopCat.HomotopyPullback

/-!
# Landing native CGWH paths in compact-open TopCat paths

The native interval is compared with `TopCat.I`, and compact-Hausdorff probe
precomposition lands the native internal Hom in the ordinary compact-open path
object. The probe and the generated mapping-space bridge supply the full landing map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Topology
open scoped Simplicial

namespace CGWH

/-- The included native interval is canonically the ordinary TopCat interval. -/
noncomputable def intervalToTopIso :
    CGWH.cgwhToTop.obj CGWH.interval.{u, v} ≅ TopCat.I.{v} :=
  SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v}) ≪≫
    SSet.stdSimplex.toTopObjIsoI.{v}

/-- The native time-zero point lands at the ordinary zero endpoint. -/
theorem intervalToTopIso_zero :
    CGWH.cgwhToTop.map CGWH.intervalZero.{u, v} ≫
        intervalToTopIso.{u, v}.hom =
      TopCat.const (0 : TopCat.I.{v}) := by
  apply TopCat.ext
  intro x
  change SSet.stdSimplex.toTopObjIsoI.hom
    (SSet.toTop.map (SSet.stdSimplex.δ 1)
      (CGWH.cgwhToTop.map
        SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv x)) = 0
  have hx : CGWH.cgwhToTop.{u, v}.map
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}.inv x =
      (default : SSet.toTop.obj (Δ[0] : SSet.{v})) := by
    apply (TopCat.homeoOfIso (CGWH.cgwhToTop.mapIso
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v})).injective
    cases x
    rfl
  rw [hx, ← SSet.toTopObjIsoI_inv_zero]
  simp

/-- The native time-one point lands at the ordinary one endpoint. -/
theorem intervalToTopIso_one :
    CGWH.cgwhToTop.map CGWH.intervalOne.{u, v} ≫
        intervalToTopIso.{u, v}.hom =
      TopCat.const (1 : TopCat.I.{v}) := by
  apply TopCat.ext
  intro x
  change SSet.stdSimplex.toTopObjIsoI.hom
    (SSet.toTop.map (SSet.stdSimplex.δ 0)
      (CGWH.cgwhToTop.map
        SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv x)) = 1
  have hx : CGWH.cgwhToTop.{u, v}.map
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}.inv x =
      (default : SSet.toTop.obj (Δ[0] : SSet.{v})) := by
    apply (TopCat.homeoOfIso (CGWH.cgwhToTop.mapIso
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v})).injective
    cases x
    rfl
  rw [hx, ← SSet.toTopObjIsoI_inv_one]
  simp

/-- The lifted unit interval viewed as a compact Hausdorff space. -/
private noncomputable def intervalCompHaus : CompHaus.{u} :=
  CompHaus.of (ULift.{u} unitInterval)

/-- The homeomorphism identifying the lifted compact interval with the topological interval. -/
private noncomputable def intervalCompHausHomeomorph :
    CompactlyGenerated.compactHausProbes
        intervalCompHaus.{u} ≃ₜ TopCat.I.{v} :=
  Homeomorph.ulift.{u, 0}.trans TopCat.I.homeomorph.{v}.symm

/-- The continuous map identifying the compact interval probe with the CGWH interval. -/
private noncomputable def intervalCompHausToInterval :
    C(CompactlyGenerated.compactHausProbes intervalCompHaus.{u},
      CGWH.interval.{u, v}) :=
  (ConcreteCategory.hom intervalToTopIso.{u, v}.inv).comp
    ⟨intervalCompHausHomeomorph.{u, v},
      intervalCompHausHomeomorph.{u, v}.continuous⟩

/-- The continuous map from the generated interval mapping space to the
compact-open TopCat path space. -/
private noncomputable def pathLandingRaw (E : CGWH.{u, v}) :
    C(ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u}
        CGWH.interval.{u, v} E,
      C(TopCat.I.{v}, E)) where
  toFun g :=
    (Homeomorph.arrowCongr intervalCompHausHomeomorph.{u, v}
      (Homeomorph.refl E))
      (ContinuousMapGeneratedBy.precomp
        intervalCompHausToInterval.{u, v} g)
  continuous_toFun :=
    (Homeomorph.arrowCongr intervalCompHausHomeomorph.{u, v}
      (Homeomorph.refl E)).continuous.comp
      (ContinuousMapGeneratedBy.continuous_precomp
        intervalCompHausToInterval.{u, v})

/-- Land a native CGWH path in the ordinary compact-open TopCat path object. -/
noncomputable def pathLanding (E : CGWH.{u, v}) :
    CGWH.cgwhToTop.obj (CGWH.path.{u, v}.obj E) ⟶
      TopCat.pathObject (CGWH.cgwhToTop.obj E) := by
  let intervalProbe : CompHaus.{u} := CompHaus.of (ULift.{u} unitInterval)
  let intervalHomeo : CompactlyGenerated.compactHausProbes intervalProbe ≃ₜ TopCat.I.{v} :=
    Homeomorph.ulift.{u, 0}.trans TopCat.I.homeomorph.{v}.symm
  let intervalMap : C(CompactlyGenerated.compactHausProbes intervalProbe, CGWH.interval.{u, v}) :=
    (ConcreteCategory.hom intervalToTopIso.{u, v}.inv).comp
      ⟨intervalHomeo, intervalHomeo.continuous⟩
  let rawLanding : C(ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{u}
      CGWH.interval.{u, v} E, C(TopCat.I.{v}, E)) :=
    { toFun := fun g =>
        (Homeomorph.arrowCongr intervalHomeo (Homeomorph.refl E))
          (ContinuousMapGeneratedBy.precomp intervalMap g)
      continuous_toFun :=
        (Homeomorph.arrowCongr intervalHomeo (Homeomorph.refl E)).continuous.comp
          (ContinuousMapGeneratedBy.continuous_precomp intervalMap) }
  exact CGWH.internalHomToRawGenerated CGWH.interval.{u, v} E ≫ TopCat.ofHom rawLanding

/-- Path landing commutes with postcomposition. -/
theorem pathLanding_naturality {E E' : CGWH.{u, v}} (f : E ⟶ E') :
    CGWH.cgwhToTop.map (CGWH.path.{u, v}.map f) ≫ pathLanding E' =
      pathLanding E ≫ TopCat.pathObjectMap (CGWH.cgwhToTop.map f) := by
  apply TopCat.ext
  intro gamma
  apply ContinuousMap.ext
  intro t
  rfl

/-- Landing a native path and evaluating at zero agrees with native evaluation. -/
theorem pathLanding_evalZero (E : CGWH.{u, v}) :
    pathLanding E ≫ TopCat.pathEvalZero _ =
      CGWH.cgwhToTop.map (CGWH.pathEvalZero.{u, v}.app E) := by
  apply TopCat.ext
  intro gamma
  let rawGamma := (WithGeneratedByTopology.equiv
      (X := CompactlyGenerated.compactHausProbes.{u})
      (Y := ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} CGWH.interval.{u, v} E) gamma :
      ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} CGWH.interval.{u, v} E)
  let e := intervalCompHausHomeomorph.{u, v}
  change rawGamma (intervalToTopIso.{u, v}.inv
      (e (e.symm (0 : TopCat.I.{v})))) =
    ConcreteCategory.hom
      (CGWH.cgwhToTop.map (CGWH.pathEvalZero.app E)) gamma
  rw [e.apply_symm_apply]
  have hpoint : intervalToTopIso.{u, v}.inv (0 : TopCat.I.{v}) =
      CGWH.intervalZero.{u, v} PUnit.unit := by
    have hz := ConcreteCategory.congr_hom
      (intervalToTopIso_zero.{u, v}) PUnit.unit
    change intervalToTopIso.{u, v}.hom
      (CGWH.intervalZero.{u, v} PUnit.unit) = 0 at hz
    rw [← hz]
    exact ConcreteCategory.congr_hom intervalToTopIso.{u, v}.hom_inv_id _
  rw [hpoint]
  let b : CGWH.point.{u, v} ⟶ CGWH.internalHom CGWH.interval E :=
    (CGWH.pointHomEquiv _).symm gamma
  let z := (CartesianMonoidalCategory.lift CGWH.intervalZero b) PUnit.unit
  have hfst : ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.fst CGWH.interval (CGWH.internalHom CGWH.interval E)) z =
      CGWH.intervalZero PUnit.unit := by
    dsimp [z]
    change ConcreteCategory.hom
      (CartesianMonoidalCategory.lift CGWH.intervalZero b ≫
        CartesianMonoidalCategory.fst CGWH.interval
          (CGWH.internalHom CGWH.interval E)) PUnit.unit = _
    rw [CartesianMonoidalCategory.lift_fst]
  have hsnd : ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.snd CGWH.interval
        (CGWH.internalHom CGWH.interval E)) z = gamma := by
    dsimp [z]
    change ConcreteCategory.hom
      (CartesianMonoidalCategory.lift CGWH.intervalZero b ≫
        CartesianMonoidalCategory.snd CGWH.interval
          (CGWH.internalHom CGWH.interval E)) PUnit.unit = _
    rw [CartesianMonoidalCategory.lift_snd]
    rfl
  have hev := CGWH.internalHom_ev_apply CGWH.interval E z
  rw [hfst, hsnd] at hev
  have hpath : CGWH.pathEvalZero.app E gamma =
      (ihom.ev CGWH.interval).app E z := by
    let e0 := CGWH.point_isTerminal.from
      (MonoidalCategoryStruct.tensorUnit CGWH.{u, v}) ≫ CGWH.intervalZero
    have hpair : b ≫
        (MonoidalCategoryStruct.leftUnitor
          (CGWH.internalHom CGWH.interval E)).inv ≫
        MonoidalCategoryStruct.whiskerRight e0
          (CGWH.internalHom CGWH.interval E) =
        CartesianMonoidalCategory.lift CGWH.intervalZero b := by
      have hprefix : b ≫
          SemiCartesianMonoidalCategory.toUnit
            (CGWH.internalHom CGWH.interval E) ≫
          CGWH.point_isTerminal.from
            (MonoidalCategoryStruct.tensorUnit CGWH.{u, v}) =
          𝟙 CGWH.point := by
        apply CGWH.point_isTerminal.hom_ext
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc,
          CartesianMonoidalCategory.whiskerRight_fst,
          CartesianMonoidalCategory.lift_fst]
        slice_lhs 2 3 =>
          rw [CartesianMonoidalCategory.leftUnitor_inv_fst]
        slice_lhs 1 3 => rw [hprefix]
        rw [Category.id_comp]
      · simp [e0, Category.assoc]
    have hcat := congrArg
      (fun q => q ≫ (ihom.ev CGWH.interval).app E) hpair
    change ConcreteCategory.hom
        (b ≫ (MonoidalCategoryStruct.leftUnitor
          (CGWH.internalHom CGWH.interval E)).inv ≫
          MonoidalCategoryStruct.whiskerRight e0
            (CGWH.internalHom CGWH.interval E) ≫
            (ihom.ev CGWH.interval).app E) PUnit.unit = _
    exact ConcreteCategory.congr_hom (by simpa only [Category.assoc] using hcat) _
  change rawGamma (CGWH.intervalZero PUnit.unit) =
    CGWH.pathEvalZero.app E gamma
  exact hev.symm.trans hpath.symm

/-- Landing a native path and evaluating at one agrees with native evaluation. -/
theorem pathLanding_evalOne (E : CGWH.{u, v}) :
    pathLanding E ≫ TopCat.pathEvalOne _ =
      CGWH.cgwhToTop.map (CGWH.pathEvalOne.{u, v}.app E) := by
  apply TopCat.ext
  intro gamma
  let rawGamma := (WithGeneratedByTopology.equiv
      (X := CompactlyGenerated.compactHausProbes.{u})
      (Y := ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} CGWH.interval.{u, v} E) gamma :
      ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} CGWH.interval.{u, v} E)
  let e := intervalCompHausHomeomorph.{u, v}
  change rawGamma (intervalToTopIso.{u, v}.inv
      (e (e.symm (1 : TopCat.I.{v})))) =
    ConcreteCategory.hom
      (CGWH.cgwhToTop.map (CGWH.pathEvalOne.app E)) gamma
  rw [e.apply_symm_apply]
  have hpoint : intervalToTopIso.{u, v}.inv (1 : TopCat.I.{v}) =
      CGWH.intervalOne.{u, v} PUnit.unit := by
    have ho := ConcreteCategory.congr_hom
      (intervalToTopIso_one.{u, v}) PUnit.unit
    change intervalToTopIso.{u, v}.hom
      (CGWH.intervalOne.{u, v} PUnit.unit) = 1 at ho
    rw [← ho]
    exact ConcreteCategory.congr_hom intervalToTopIso.{u, v}.hom_inv_id _
  rw [hpoint]
  let b : CGWH.point.{u, v} ⟶ CGWH.internalHom CGWH.interval E :=
    (CGWH.pointHomEquiv _).symm gamma
  let z := (CartesianMonoidalCategory.lift CGWH.intervalOne b) PUnit.unit
  have hfst : ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.fst CGWH.interval (CGWH.internalHom CGWH.interval E)) z =
      CGWH.intervalOne PUnit.unit := by
    dsimp [z]
    change ConcreteCategory.hom
      (CartesianMonoidalCategory.lift CGWH.intervalOne b ≫
        CartesianMonoidalCategory.fst CGWH.interval
          (CGWH.internalHom CGWH.interval E)) PUnit.unit = _
    rw [CartesianMonoidalCategory.lift_fst]
  have hsnd : ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.snd CGWH.interval
        (CGWH.internalHom CGWH.interval E)) z = gamma := by
    dsimp [z]
    change ConcreteCategory.hom
      (CartesianMonoidalCategory.lift CGWH.intervalOne b ≫
        CartesianMonoidalCategory.snd CGWH.interval
          (CGWH.internalHom CGWH.interval E)) PUnit.unit = _
    rw [CartesianMonoidalCategory.lift_snd]
    rfl
  have hev := CGWH.internalHom_ev_apply CGWH.interval E z
  rw [hfst, hsnd] at hev
  have hpath : CGWH.pathEvalOne.app E gamma =
      (ihom.ev CGWH.interval).app E z := by
    let e1 := CGWH.point_isTerminal.from
      (MonoidalCategoryStruct.tensorUnit CGWH.{u, v}) ≫ CGWH.intervalOne
    have hpair : b ≫
        (MonoidalCategoryStruct.leftUnitor
          (CGWH.internalHom CGWH.interval E)).inv ≫
        MonoidalCategoryStruct.whiskerRight e1
          (CGWH.internalHom CGWH.interval E) =
        CartesianMonoidalCategory.lift CGWH.intervalOne b := by
      have hprefix : b ≫
          SemiCartesianMonoidalCategory.toUnit
            (CGWH.internalHom CGWH.interval E) ≫
          CGWH.point_isTerminal.from
            (MonoidalCategoryStruct.tensorUnit CGWH.{u, v}) =
          𝟙 CGWH.point := by
        apply CGWH.point_isTerminal.hom_ext
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc,
          CartesianMonoidalCategory.whiskerRight_fst,
          CartesianMonoidalCategory.lift_fst]
        slice_lhs 2 3 =>
          rw [CartesianMonoidalCategory.leftUnitor_inv_fst]
        slice_lhs 1 3 => rw [hprefix]
        rw [Category.id_comp]
      · simp [e1, Category.assoc]
    have hcat := congrArg
      (fun q => q ≫ (ihom.ev CGWH.interval).app E) hpair
    change ConcreteCategory.hom
        (b ≫ (MonoidalCategoryStruct.leftUnitor
          (CGWH.internalHom CGWH.interval E)).inv ≫
          MonoidalCategoryStruct.whiskerRight e1
            (CGWH.internalHom CGWH.interval E) ≫
            (ihom.ev CGWH.interval).app E) PUnit.unit = _
    exact ConcreteCategory.congr_hom (by simpa only [Category.assoc] using hcat) _
  change rawGamma (CGWH.intervalOne PUnit.unit) =
    CGWH.pathEvalOne.app E gamma
  exact hev.symm.trans hpath.symm

/-- Landing a native constant path gives the corresponding constant TopCat path. -/
@[simp]
theorem pathLanding_constant_apply
    (E : CGWH.{u, v}) (x : E) (t : TopCat.I.{v}) :
    (@DFunLike.coe
      (@ContinuousMap TopCat.I.{v}
        (CompactlyGenerated.compactlyGeneratedToTop.obj (CGWH.cgwhToCompactlyGenerated.obj E))
        TopCat.I.str
        (CompactlyGenerated.compactlyGeneratedToTop.obj (CGWH.cgwhToCompactlyGenerated.obj E)).str)
      TopCat.I.{v}
      (fun _ => CompactlyGenerated.compactlyGeneratedToTop.obj
        (CGWH.cgwhToCompactlyGenerated.obj E))
      (@ContinuousMap.instFunLike TopCat.I.{v}
        (CompactlyGenerated.compactlyGeneratedToTop.obj (CGWH.cgwhToCompactlyGenerated.obj E))
        TopCat.I.str
        (CompactlyGenerated.compactlyGeneratedToTop.obj (CGWH.cgwhToCompactlyGenerated.obj E)).str)
      (@DFunLike.coe
        (@ContinuousMap
          (CompactlyGenerated.compactlyGeneratedToTop.obj
            (CGWH.cgwhToCompactlyGenerated.obj (CGWH.path.obj E)))
          (@ContinuousMap TopCat.I.{v}
            (CompactlyGenerated.compactlyGeneratedToTop.obj (CGWH.cgwhToCompactlyGenerated.obj E))
            TopCat.I.str
            (CompactlyGenerated.compactlyGeneratedToTop.obj (CGWH.cgwhToCompactlyGenerated.obj E)).str)
          (CGWH.cgwhToTop.obj (CGWH.path.obj E)).str
          (TopCat.pathObject (CGWH.cgwhToTop.obj E)).str)
        (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (CGWH.path.obj E)))
        (fun _ => @ContinuousMap TopCat.I.{v}
          (CompactlyGenerated.compactlyGeneratedToTop.obj (CGWH.cgwhToCompactlyGenerated.obj E))
          TopCat.I.str
          (CompactlyGenerated.compactlyGeneratedToTop.obj (CGWH.cgwhToCompactlyGenerated.obj E)).str)
        (@ContinuousMap.instFunLike
          (CompactlyGenerated.compactlyGeneratedToTop.obj
            (CGWH.cgwhToCompactlyGenerated.obj (CGWH.path.obj E)))
          (TopCat.pathObject (CGWH.cgwhToTop.obj E))
          (CGWH.cgwhToTop.obj (CGWH.path.obj E)).str
          (TopCat.pathObject (CGWH.cgwhToTop.obj E)).str)
        (ConcreteCategory.hom (pathLanding E))
        (@DFunLike.coe
          (@ContinuousMap E.toCompactlyGenerated.toTop
            (CGWH.path.obj E).toCompactlyGenerated.toTop
            E.toCompactlyGenerated.toTop.str (CGWH.path.obj E).toCompactlyGenerated.toTop.str)
          E.toCompactlyGenerated.toTop
          (fun _ => (CGWH.path.obj E).toCompactlyGenerated.toTop)
          (@ContinuousMap.instFunLike E.toCompactlyGenerated.toTop
            (CGWH.path.obj E).toCompactlyGenerated.toTop
            E.toCompactlyGenerated.toTop.str (CGWH.path.obj E).toCompactlyGenerated.toTop.str)
          (ConcreteCategory.hom (CGWH.pathConstant.{u, v}.app E)) x))) t = x := by
  let e := intervalCompHausHomeomorph.{u, v}
  change (WithGeneratedByTopology.equiv
      (X := CompactlyGenerated.compactHausProbes.{u})
      (Y := ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} CGWH.interval.{u, v} E)
      (CGWH.pathConstant.{u, v}.app E x) :
      ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} CGWH.interval.{u, v} E)
      (intervalToTopIso.{u, v}.inv (e (e.symm t))) = x
  rw [e.apply_symm_apply]
  let a : CGWH.point.{u, v} ⟶ CGWH.interval.{u, v} :=
    (CGWH.pointHomEquiv CGWH.interval.{u, v}).symm
      (intervalToTopIso.{u, v}.inv t)
  let b : CGWH.point.{u, v} ⟶ E :=
    (CGWH.pointHomEquiv E).symm x
  let z := (CartesianMonoidalCategory.lift a b) PUnit.unit
  have h := CGWH.internalHom_curry_apply
    (A := CGWH.interval.{u, v}) (Y := E) (B := E)
    (CartesianMonoidalCategory.snd CGWH.interval E) z
  have hfst : ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.fst CGWH.interval E) z =
      intervalToTopIso.{u, v}.inv t := by
    dsimp [z]
    change ConcreteCategory.hom
      (CartesianMonoidalCategory.lift a b ≫
        CartesianMonoidalCategory.fst CGWH.interval E) PUnit.unit = _
    rw [CartesianMonoidalCategory.lift_fst]
    rfl
  have hsnd : ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.snd CGWH.interval E) z = x := by
    dsimp [z]
    change ConcreteCategory.hom
      (CartesianMonoidalCategory.lift a b ≫
        CartesianMonoidalCategory.snd CGWH.interval E) PUnit.unit = _
    rw [CartesianMonoidalCategory.lift_snd]
    rfl
  rw [hfst, hsnd] at h
  simpa [CGWH.pathConstant] using h

end CGWH
