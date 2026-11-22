/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.SuspensionLoop
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.Topology.Category.CGWH.Reflection
public import MathlibExt.Topology.Category.CGWH.PathLanding
public import MathlibExt.Topology.Homotopy.StrictLoopMap
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Native pointed CGWH loops and compact-open loops

The selected based internal Hom from the native one-sphere agrees with the
compact-generation coreflection of the compact-open topological loop space.
This file also records evaluation and binary-product compatibility for that
strict loop functor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
open scoped Simplicial

namespace PointedCGWH

private def pointValue (X : PointedCGWH.{u, v}) : X.right :=
  X.hom (show CGWH.point.{u, v} from PUnit.unit)

/-- Strict postcomposition on compact-open loops of pointed CGWH spaces. -/
@[no_expose]
noncomputable def strictLoopMap {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    C(LoopSpace X.right (X.hom (show CGWH.point.{u, v} from PUnit.unit)),
      LoopSpace Y.right (Y.hom (show CGWH.point.{u, v} from PUnit.unit))) := by
  have h0 : f.right (pointValue X) = pointValue Y :=
    ConcreteCategory.congr_hom (Under.w f) PUnit.unit
  let f' : C(X.right, Y.right) := ConcreteCategory.hom f.right
  exact
    { toFun := fun gamma =>
        (ContinuousMap.strictLoopMap
          f' (pointValue X) gamma).cast
            h0.symm h0.symm
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        exact f'.continuous.comp
          (continuous_fst.eval continuous_snd) }

/-- The pointed strict loop map is literal postcomposition pointwise. -/
@[simp]
theorem strictLoopMap_apply {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (gamma : LoopSpace X.right (X.hom (show CGWH.point.{u, v} from PUnit.unit))) (t : unitInterval) :
    strictLoopMap f gamma t = f.right (gamma t) := by
  rfl

private theorem strictLoopMap_id (X : PointedCGWH.{u, v}) :
    strictLoopMap (𝟙 X) =
      ContinuousMap.id (LoopSpace X.right (pointValue X)) := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  funext t
  rfl

private theorem strictLoopMap_comp
    {X Y Z : PointedCGWH.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (strictLoopMap g).comp (strictLoopMap f) = strictLoopMap (f ≫ g) := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  funext t
  rfl

private theorem strictLoopMap_refl
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    strictLoopMap f (Path.refl (pointValue X)) =
      Path.refl (pointValue Y) := by
  apply Path.ext
  funext t
  exact (strictLoopMap_apply f (Path.refl (pointValue X)) t).trans
    (ConcreteCategory.congr_hom (Under.w f) PUnit.unit)

private noncomputable def compactOpenLoopCarrier
    (X : PointedCGWH.{u, v}) : CGWH.{u, v} := by
  let Raw : TopCat.{v} := TopCat.of (LoopSpace X.right (pointValue X))
  let R : CompactlyGenerated.{u, v} :=
    TopCat.toCompactlyGenerated.{u, v}.obj Raw
  have hWeak : UWeakHausdorffSpace.{u} R := by
    rw [uWeakHausdorffSpace_iff_isClosed_equalizer]
    intro K a b
    let c : CompactlyGenerated.compactlyGeneratedToTop.obj R ⟶ Raw :=
      CompactlyGenerated.adj.{u, v}.counit.app Raw
    let evalAt (t : unitInterval) : C(R, X.right) :=
      (⟨fun gamma : LoopSpace X.right (pointValue X) => gamma t,
        continuous_eval_const t⟩ :
          C(LoopSpace X.right (pointValue X), X.right)).comp
        c.hom
    let Et (t : unitInterval) : Set ↥K :=
      fun k => evalAt t (a k) = evalAt t (b k)
    have hSet : (fun k : ↥K => a k = b k) =
        ⋂ t : unitInterval, Et t := by
      ext k
      change (a k = b k) ↔ k ∈ ⋂ t : unitInterval, Et t
      rw [Set.mem_iInter]
      change (a k = b k) ↔
        ∀ t : unitInterval, evalAt t (a k) = evalAt t (b k)
      constructor
      · intro hab t
        rw [hab]
      · intro h
        have hc : c (a k) = c (b k) := by
          apply Path.ext
          funext t
          have ht := h t
          change c (a k) t = c (b k) t at ht
          exact ht
        exact (CompactlyGenerated.adjCounit_apply.{v, u} Raw (a k)).symm.trans
          (hc.trans (CompactlyGenerated.adjCounit_apply.{v, u} Raw (b k)))
    rw [hSet]
    apply isClosed_iInter
    intro t
    exact
      (uWeakHausdorffSpace_iff_isClosed_equalizer.mp inferInstance)
        K ((evalAt t).comp a) ((evalAt t).comp b)
  exact
    { toCompactlyGenerated := R
      is_weakHausdorff := hWeak }

/-- Compact generation of the raw compact-open loop space, regarded as a
pointed CGWH space with the constant loop as basepoint. -/
@[no_expose]
noncomputable def compactOpenLoopCoreflection :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} where
  obj X := Under.mk (ConcreteCategory.ofHom
    ⟨fun _ => Path.refl (pointValue X), continuous_const⟩ :
      CGWH.point.{u, v} ⟶ compactOpenLoopCarrier X)
  map {X Y} f := by
    let m : compactOpenLoopCarrier X ⟶ compactOpenLoopCarrier Y :=
      CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage (by
        dsimp only [compactOpenLoopCarrier]
        exact TopCat.toCompactlyGenerated.{u, v}.map
          (TopCat.ofHom (strictLoopMap f)))
    exact Under.homMk m (by
      apply ConcreteCategory.hom_ext
      intro p
      change strictLoopMap f (Path.refl (pointValue X)) =
        Path.refl (pointValue Y)
      exact strictLoopMap_refl f)
  map_id X := by
    apply Under.UnderMorphism.ext
    apply CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_injective
    apply ConcreteCategory.hom_ext
    intro gamma
    change strictLoopMap (𝟙 X) gamma = gamma
    exact congrArg (fun q => q gamma) (strictLoopMap_id X)
  map_comp {X Y Z} f g := by
    apply Under.UnderMorphism.ext
    apply CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_injective
    apply ConcreteCategory.hom_ext
    intro gamma
    change strictLoopMap (f ≫ g) gamma =
      strictLoopMap g (strictLoopMap f gamma)
    exact (congrArg (fun q => q gamma) (strictLoopMap_comp f g)).symm

private noncomputable def diskIntervalIso :
    CGWH.cgwhToTop.obj PointedCGWH.diskOne.{u, v}.right ≅
      TopCat.I.{v} :=
  SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v}) ≪≫
    SSet.stdSimplex.toTopObjIsoI

private noncomputable def diskToSphere :
    PointedCGWH.diskOne.{u, v} ⟶ PointedCGWH.sphereOne.{u, v} := by
  let i : SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ⟶
      SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v}) :=
    SSet.toCGWH.map (SSet.boundary.{v} 1).ι
  let c : SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ⟶
      CGWH.point.{u, v} := CGWH.point_isTerminal.from _
  let e0 : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
  let r0 : CGWH.point.{u, v} ⟶
      SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) :=
    e0.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (0 : Fin 2))
  refine Under.homMk (pushout.inl i c) ?_
  change (e0.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ (0 : Fin 2))) ≫
      pushout.inl i c = pushout.inr i c
  have hri : r0 ≫ i =
      e0.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ (0 : Fin 2)) := by
    dsimp only [r0, i]
    rw [Category.assoc, ← Functor.map_comp, SSet.boundary.ι_ι]
  rw [← hri, Category.assoc, pushout.condition]
  rw [← Category.assoc]
  have hrc : r0 ≫ c = 𝟙 CGWH.point.{u, v} :=
    CGWH.point_isTerminal.hom_ext _ _
  rw [hrc, Category.id_comp]

/-- The interval parameterization of the native one-sphere.  Its endpoints
are both the collapsed sphere point. -/
@[no_expose]
noncomputable def sphereOneParam :
    TopCat.I.{v} ⟶
      CGWH.cgwhToTop.obj PointedCGWH.sphereOne.{u, v}.right :=
  diskIntervalIso.inv ≫ CGWH.cgwhToTop.map diskToSphere.right

/-- The canonical disk leg of the ordinary cofiber comparison agrees at
every interval parameter with the native sphere parameterization. -/
theorem diskCofiberIsoSphereOne_param
    (t : TopCat.I.{v}) :
    CGWH.cgwhToTop.map
        ((colimit.ι
            (HomotopicalAlgebra.cofiberSpan.obj
              (CategoryTheory.Arrow.mk
                PointedCGWH.diskBoundary.{u, v}))
            WalkingSpan.left ≫
          PointedCGWH.diskCofiberIsoSphereOne.{u, v}.hom).right)
        (CGWH.intervalToTopIso.{u, v}.inv t) =
      PointedCGWH.sphereOneParam.{u, v} t := by
  let S0 : PointedCGWH.{u, v} :=
    (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).left
  let qD : PointedCGWH.diskOne.{u, v} ⟶
      (HomotopicalAlgebra.ordinaryCofiber
        (C := PointedCGWH.{u, v})).obj
          (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) :=
    pushout.inl PointedCGWH.diskBoundary (terminal.from S0)
  let eC := PointedCGWH.diskCofiberIsoSphereOne.{u, v}
  have hDiskCofiber : diskToSphere.{u, v} ≫ eC.inv = qD := by
    apply (cancel_mono eC.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Under.UnderMorphism.ext
    unfold eC qD diskToSphere PointedCGWH.diskCofiberIsoSphereOne
    dsimp
    generalize_proofs _ hP
    let hOrd := IsPushout.of_hasPushout PointedCGWH.diskBoundary
      (terminal.from S0)
    exact congrArg Under.Hom.right
      (hOrd.inl_isoIsPushout_hom _ _ (by assumption)).symm
  have hqDHom : qD ≫ eC.hom = diskToSphere.{u, v} := by
    rw [← hDiskCofiber, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  change
    CGWH.cgwhToTop.map
        ((qD ≫ eC.hom).right)
        (CGWH.intervalToTopIso.{u, v}.inv t) =
      CGWH.cgwhToTop.map diskToSphere.{u, v}.right
        (CGWH.intervalToTopIso.{u, v}.inv t)
  rw [hqDHom]

private theorem sphereOneParam_zero :
    sphereOneParam.{u, v} (0 : TopCat.I.{v}) =
      PointedCGWH.sphereOne.{u, v}.hom
        (show CGWH.point.{u, v} from PUnit.unit) := by
  let i : SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ⟶
      SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v}) :=
    SSet.toCGWH.map (SSet.boundary.{v} 1).ι
  let c : SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ⟶
      CGWH.point.{u, v} := CGWH.point_isTerminal.from _
  let e0 : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
  let r1 : CGWH.point.{u, v} ⟶
      SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) :=
    e0.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (1 : Fin 2))
  have hInput : diskIntervalIso.{u, v}.inv (0 : TopCat.I.{v}) =
      (e0.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ (1 : Fin 2)))
        PUnit.unit := by
    change SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I.{v}) = _
    rw [SSet.toTopObjIsoI_inv_zero]
    change SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) default =
      SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) (e0.inv PUnit.unit)
    exact congrArg _ (Subsingleton.elim _ _)
  have hri : r1 ≫ i =
      e0.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ (1 : Fin 2)) := by
    dsimp only [r1, i]
    rw [Category.assoc, ← Functor.map_comp, SSet.boundary.ι_ι]
  have hrc : r1 ≫ c = 𝟙 CGWH.point.{u, v} :=
    CGWH.point_isTerminal.hom_ext _ _
  have hq :
      (e0.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ (1 : Fin 2))) ≫
          pushout.inl i c = pushout.inr i c := by
    rw [← hri, Category.assoc, pushout.condition, ← Category.assoc, hrc,
      Category.id_comp]
  change diskToSphere.right (diskIntervalIso.inv 0) = _
  rw [hInput]
  exact ConcreteCategory.congr_hom hq
    (show CGWH.point.{u, v} from PUnit.unit)

private theorem sphereOneParam_one :
    sphereOneParam.{u, v} (1 : TopCat.I.{v}) =
      PointedCGWH.sphereOne.{u, v}.hom
        (show CGWH.point.{u, v} from PUnit.unit) := by
  let e0 : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
  have hInput : diskIntervalIso.{u, v}.inv (1 : TopCat.I.{v}) =
      PointedCGWH.diskOne.{u, v}.hom PUnit.unit := by
    change SSet.stdSimplex.toTopObjIsoI.inv (1 : TopCat.I.{v}) = _
    rw [SSet.toTopObjIsoI_inv_one]
    change SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) default =
      SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) (e0.inv PUnit.unit)
    exact congrArg _ (Subsingleton.elim _ _)
  change diskToSphere.right (diskIntervalIso.inv 1) = _
  rw [hInput]
  exact ConcreteCategory.congr_hom (Under.w diskToSphere)
    (show CGWH.point.{u, v} from PUnit.unit)

private noncomputable def loopLandingRaw (X : PointedCGWH.{u, v}) :
    {f : CGWH.cgwhToTop.obj (PointedCGWH.loop.obj X).right ⟶
        TopCat.of (LoopSpace X.right (pointValue X)) //
      f ((PointedCGWH.loop.obj X).hom PUnit.unit) =
        Path.refl (pointValue X) ∧
      ∀ (gamma : (PointedCGWH.loop.obj X).right) (t : unitInterval),
        f gamma t =
          let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
            ConcreteCategory.ofHom (ContinuousMap.const _
              (sphereOneParam.{u, v} (TopCat.I.homeomorph.symm t)))
          let b : CGWH.point.{u, v} ⟶
              (PointedCGWH.loop.obj X).right :=
            ConcreteCategory.ofHom (ContinuousMap.const _ gamma)
          (PointedCGWH.basedEval PointedCGWH.sphereOne).app X |>.right
            ((CategoryTheory.Pointed.smashPresentation
              CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
                (PointedCGWH.loop.obj X)).2.1.inl
              (CartesianMonoidalCategory.lift a b PUnit.unit))} := by
  let L := PointedCGWH.loop.obj X
  let J : CGWH.{u, v} := PointedCGWH.diskOne.{u, v}.right
  let _ : T2Space TopCat.I.{v} := TopCat.I.homeomorph.symm.t2Space
  let hJ : J ≃ₜ TopCat.I.{v} :=
    TopCat.homeoOfIso diskIntervalIso.{u, v}
  let _ : LocallyCompactSpace J := (hJ.locallyCompactSpace_iff).2 inferInstance
  let _ : T2Space J := hJ.symm.t2Space
  let param : J ⟶ PointedCGWH.sphereOne.{u, v}.right :=
    diskToSphere.{u, v}.right
  let hProd : IsHomeomorph (CGWH.prodComparisonToTop J L.right) :=
    CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_left J L.right
  let eProd : CGWH.cgwhToTop.obj (J ⨯ L.right) ≅
      TopCat.of (J × L.right) :=
    TopCat.isoOfHomeo hProd.homeomorph
  let rawParamPair : TopCat.of (TopCat.I.{v} × L.right) ⟶
      TopCat.of (J × L.right) := TopCat.ofHom
    ⟨fun z => (diskIntervalIso.{u, v}.inv z.1, z.2),
      (diskIntervalIso.{u, v}.inv.hom.continuous.comp continuous_fst).prodMk
        continuous_snd⟩
  let toTensor : J ⨯ L.right ⟶
      PointedCGWH.sphereOne.{u, v}.right ⊗ L.right :=
    CartesianMonoidalCategory.lift
      ((Limits.prod.fst : J ⨯ L.right ⟶ J) ≫ param)
      (Limits.prod.snd : J ⨯ L.right ⟶ L.right)
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne L
  let q : PointedCGWH.sphereOne.{u, v}.right ⊗ L.right ⟶
      ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).right :=
    p.2.1.inl
  let ev : (PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L ⟶ X :=
    (PointedCGWH.basedEval PointedCGWH.sphereOne).app X
  let rawEval : TopCat.of (J × L.right) ⟶ CGWH.cgwhToTop.obj X.right :=
    eProd.inv ≫ CGWH.cgwhToTop.map toTensor ≫
      CGWH.cgwhToTop.map q ≫ CGWH.cgwhToTop.map ev.right
  let rawEvalI : TopCat.of (TopCat.I.{v} × L.right) ⟶
      CGWH.cgwhToTop.obj X.right := rawParamPair ≫ rawEval
  have hRawEval (gamma : L.right) (s : TopCat.I.{v}) :
      rawEvalI (s, gamma) =
        let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
          ConcreteCategory.ofHom (ContinuousMap.const _ (sphereOneParam s))
        let b : CGWH.point.{u, v} ⟶ L.right :=
          ConcreteCategory.ofHom (ContinuousMap.const _ gamma)
        ev.right (q (CartesianMonoidalCategory.lift a b PUnit.unit)) := by
    let d : J := diskIntervalIso.{u, v}.inv s
    let aD : CGWH.point.{u, v} ⟶ J :=
      ConcreteCategory.ofHom (ContinuousMap.const _ d)
    let b : CGWH.point.{u, v} ⟶ L.right :=
      ConcreteCategory.ofHom (ContinuousMap.const _ gamma)
    let pair : CGWH.point.{u, v} ⟶ J ⨯ L.right := Limits.prod.lift aD b
    have hForward : eProd.hom (pair PUnit.unit) = (d, gamma) := by
      apply Prod.ext
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_fst J L.right) (pair PUnit.unit)
        change (eProd.hom (pair PUnit.unit)).1 = _ at h
        rw [h]
        exact ConcreteCategory.congr_hom (Limits.prod.lift_fst aD b) PUnit.unit
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_snd J L.right) (pair PUnit.unit)
        change (eProd.hom (pair PUnit.unit)).2 = _ at h
        rw [h]
        exact ConcreteCategory.congr_hom (Limits.prod.lift_snd aD b) PUnit.unit
    have hPair : eProd.inv (d, gamma) = pair PUnit.unit := by
      apply (TopCat.homeoOfIso eProd).injective
      exact eProd.inv_hom_id_apply (d, gamma) |>.trans hForward.symm
    let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
      ConcreteCategory.ofHom (ContinuousMap.const _ (sphereOneParam s))
    have hParam : aD ≫ param = a := by
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    have hTensor : pair ≫ toTensor =
        CartesianMonoidalCategory.lift a b := by
      apply CartesianMonoidalCategory.hom_ext
      · dsimp only [pair, toTensor]
        rw [Category.assoc, CartesianMonoidalCategory.lift_fst,
          ← Category.assoc, Limits.prod.lift_fst, hParam,
          CartesianMonoidalCategory.lift_fst]
      · dsimp only [pair, toTensor]
        rw [Category.assoc, CartesianMonoidalCategory.lift_snd,
          Limits.prod.lift_snd, CartesianMonoidalCategory.lift_snd]
    change ev.right (q (toTensor (eProd.inv (d, gamma)))) = _
    rw [hPair]
    exact congrArg (fun z => ev.right (q z))
      (ConcreteCategory.congr_hom hTensor PUnit.unit)
  have hEndpoint (t : TopCat.I.{v})
      (ht : sphereOneParam.{u, v} t =
        PointedCGWH.sphereOne.{u, v}.hom
          (show CGWH.point.{u, v} from PUnit.unit))
      (gamma : L.right) : rawEvalI (t, gamma) = pointValue X := by
    let d : J := diskIntervalIso.{u, v}.inv t
    let jt : CGWH.point.{u, v} ⟶ J := ConcreteCategory.ofHom
      (ContinuousMap.const _ d)
    let axis : L.right ⟶ J ⨯ L.right :=
      Limits.prod.lift (CGWH.point_isTerminal.from L.right ≫ jt) (𝟙 L.right)
    have hParam : jt ≫ param = PointedCGWH.sphereOne.{u, v}.hom := by
      apply ConcreteCategory.hom_ext
      intro z
      change diskToSphere.{u, v}.right d = _
      dsimp only [d]
      exact ht
    have hForward : eProd.hom (axis gamma) = (d, gamma) := by
      apply Prod.ext
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_fst J L.right) (axis gamma)
        change (eProd.hom (axis gamma)).1 = _ at h
        rw [h]
        exact ConcreteCategory.congr_hom
          (Limits.prod.lift_fst
            (CGWH.point_isTerminal.from L.right ≫ jt) (𝟙 L.right)) gamma
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_snd J L.right) (axis gamma)
        change (eProd.hom (axis gamma)).2 = _ at h
        rw [h]
        exact ConcreteCategory.congr_hom
          (Limits.prod.lift_snd
            (CGWH.point_isTerminal.from L.right ≫ jt) (𝟙 L.right)) gamma
    have hPair : eProd.inv (d, gamma) = axis gamma := by
      apply (TopCat.homeoOfIso eProd).injective
      exact eProd.inv_hom_id_apply (d, gamma) |>.trans hForward.symm
    let rightRaw : L.right ⟶
        PointedCGWH.sphereOne.{u, v}.right ⊗ L.right :=
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from L.right ≫
          PointedCGWH.sphereOne.{u, v}.hom) (𝟙 L.right)
    have hAxis : axis ≫ toTensor = rightRaw := by
      apply CartesianMonoidalCategory.hom_ext
      · dsimp only [axis, toTensor, rightRaw]
        rw [Category.assoc, CartesianMonoidalCategory.lift_fst]
        rw [← Category.assoc, Limits.prod.lift_fst]
        rw [Category.assoc, hParam,
          CartesianMonoidalCategory.lift_fst]
      · dsimp only [axis, toTensor, rightRaw]
        rw [Category.assoc, CartesianMonoidalCategory.lift_snd]
        rw [Limits.prod.lift_snd,
          CartesianMonoidalCategory.lift_snd]
    let wedgeInr : L ⟶
        ((CategoryTheory.Pointed.wedge CGWH.point).obj
          PointedCGWH.sphereOne).obj L :=
      Under.homMk (pushout.inr PointedCGWH.sphereOne.hom L.hom) (by
        dsimp only [CategoryTheory.Pointed.wedge, Under.mk_hom]
        exact pushout.condition.symm)
    have hpInr : wedgeInr.right ≫ p.1.right = rightRaw := by
      change pushout.inr PointedCGWH.sphereOne.hom L.hom ≫
          pushout.desc _ _ _ = _
      rw [pushout.inr_desc]
      rfl
    have hqPoint : rightRaw ≫ q =
        CGWH.point_isTerminal.from L.right ≫
          (((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).hom) := by
      rw [← hpInr, Category.assoc]
      change wedgeInr.right ≫ p.1.right ≫ p.2.1.inl = _
      rw [p.2.1.condition]
      rw [← Category.assoc]
      exact congrArg
        (fun k : L.right ⟶ CGWH.point =>
          k ≫ ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).hom)
        (CGWH.point_isTerminal.hom_ext _ _)
    have hcomp : axis ≫ toTensor ≫ q ≫ ev.right =
        CGWH.point_isTerminal.from L.right ≫ X.hom := by
      change (axis ≫ toTensor) ≫ q ≫ ev.right = _
      rw [hAxis, ← Category.assoc, hqPoint, Category.assoc, Under.w ev]
    change ev.right
      (q (toTensor (eProd.inv (d, gamma)))) = pointValue X
    rw [hPair]
    exact ConcreteCategory.congr_hom hcomp gamma
  have hLoopPoint (t : TopCat.I.{v}) :
      rawEvalI (t, L.hom PUnit.unit) = pointValue X := by
    let d : J := diskIntervalIso.{u, v}.inv t
    let axis : J ⟶ J ⨯ L.right :=
      Limits.prod.lift (𝟙 J)
        (CGWH.point_isTerminal.from J ≫ L.hom)
    have hForward : eProd.hom (axis d) = (d, L.hom PUnit.unit) := by
      apply Prod.ext
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_fst J L.right) (axis d)
        change (eProd.hom (axis d)).1 = _ at h
        rw [h]
        exact ConcreteCategory.congr_hom
          (Limits.prod.lift_fst (𝟙 J)
            (CGWH.point_isTerminal.from J ≫ L.hom)) d
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_snd J L.right) (axis d)
        change (eProd.hom (axis d)).2 = _ at h
        rw [h]
        have hs := ConcreteCategory.congr_hom
          (Limits.prod.lift_snd (𝟙 J)
            (CGWH.point_isTerminal.from J ≫ L.hom)) d
        exact hs.trans (congrArg (fun z : CGWH.point.{u, v} => L.hom z)
          (Subsingleton.elim _ PUnit.unit))
    have hPair : eProd.inv (d, L.hom PUnit.unit) = axis d := by
      apply (TopCat.homeoOfIso eProd).injective
      exact eProd.inv_hom_id_apply (d, L.hom PUnit.unit) |>.trans
        hForward.symm
    let leftRaw : PointedCGWH.sphereOne.{u, v}.right ⟶
        PointedCGWH.sphereOne.{u, v}.right ⊗ L.right :=
      CartesianMonoidalCategory.lift (𝟙 _)
        (CGWH.point_isTerminal.from _ ≫ L.hom)
    have hAxis : axis ≫ toTensor = param ≫ leftRaw := by
      apply CartesianMonoidalCategory.hom_ext
      · dsimp only [axis, toTensor, leftRaw]
        rw [Category.assoc, CartesianMonoidalCategory.lift_fst]
        rw [← Category.assoc, Limits.prod.lift_fst, Category.id_comp]
        rw [Category.assoc, CartesianMonoidalCategory.lift_fst,
          Category.comp_id]
      · dsimp only [axis, toTensor, leftRaw]
        simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
        rw [Limits.prod.lift_snd]
        exact (congrArg (fun k : J ⟶ CGWH.point => k ≫ L.hom)
          (CGWH.point_isTerminal.hom_ext
            (CGWH.point_isTerminal.from J)
            (param ≫ CGWH.point_isTerminal.from _))).symm
    let wedgeInl : PointedCGWH.sphereOne.{u, v} ⟶
        ((CategoryTheory.Pointed.wedge CGWH.point).obj
          PointedCGWH.sphereOne).obj L :=
      Under.homMk (pushout.inl PointedCGWH.sphereOne.hom L.hom) rfl
    have hpInl : wedgeInl.right ≫ p.1.right = leftRaw := by
      change pushout.inl PointedCGWH.sphereOne.hom L.hom ≫
          pushout.desc _ _ _ = _
      rw [pushout.inl_desc]
      rfl
    have hqPoint : leftRaw ≫ q =
        CGWH.point_isTerminal.from PointedCGWH.sphereOne.right ≫
          (((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).hom) := by
      rw [← hpInl, Category.assoc]
      change wedgeInl.right ≫ p.1.right ≫ p.2.1.inl = _
      rw [p.2.1.condition]
      rw [← Category.assoc]
      exact congrArg
        (fun k : PointedCGWH.sphereOne.right ⟶ CGWH.point =>
          k ≫ ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).hom)
        (CGWH.point_isTerminal.hom_ext _ _)
    have hcomp : axis ≫ toTensor ≫ q ≫ ev.right =
        CGWH.point_isTerminal.from J ≫ X.hom := by
      change (axis ≫ toTensor) ≫ q ≫ ev.right = _
      rw [hAxis]
      slice_lhs 2 3 => rw [hqPoint]
      slice_lhs 3 4 => rw [Under.w ev]
      exact congrArg (fun k : J ⟶ CGWH.point => k ≫ X.hom)
        (CGWH.point_isTerminal.hom_ext
          (param ≫ CGWH.point_isTerminal.from _)
          (CGWH.point_isTerminal.from J))
    change ev.right (q (toTensor (eProd.inv (d, L.hom PUnit.unit)))) =
      pointValue X
    rw [hPair]
    exact ConcreteCategory.congr_hom hcomp d
  let landing (gamma : L.right) : LoopSpace X.right (pointValue X) :=
    { toFun := fun t =>
        rawEvalI (TopCat.I.homeomorph.symm t, gamma)
      continuous_toFun := rawEvalI.hom.continuous.comp
        (TopCat.I.homeomorph.symm.continuous.comp continuous_id |>.prodMk
          continuous_const)
      source' := by
        rw [show TopCat.I.homeomorph.symm (0 : unitInterval) =
          (0 : TopCat.I.{v}) by rfl]
        exact hEndpoint (0 : TopCat.I.{v}) sphereOneParam_zero gamma
      target' := by
        rw [show TopCat.I.homeomorph.symm (1 : unitInterval) =
          (1 : TopCat.I.{v}) by rfl]
        exact hEndpoint (1 : TopCat.I.{v}) sphereOneParam_one gamma }
  let f : CGWH.cgwhToTop.obj L.right ⟶
      TopCat.of (LoopSpace X.right (pointValue X)) := TopCat.ofHom
    ⟨landing, by
      apply Path.continuous_uncurry_iff.mp
      exact rawEvalI.hom.continuous.comp
        ((TopCat.I.homeomorph.symm.continuous.comp continuous_snd).prodMk
          continuous_fst)⟩
  refine ⟨f, ?_, ?_⟩
  · apply Path.ext
    funext t
    change rawEvalI (TopCat.I.homeomorph.symm t, L.hom PUnit.unit) = _
    exact hLoopPoint (TopCat.I.homeomorph.symm t)
  · intro gamma t
    exact hRawEval gamma (TopCat.I.homeomorph.symm t)

private noncomputable def toCompactOpen (X : PointedCGWH.{u, v}) :
    PointedCGWH.loop.obj X ⟶ compactOpenLoopCoreflection.obj X := by
  let Raw : TopCat.{v} := TopCat.of (LoopSpace X.right (pointValue X))
  let A : CompactlyGenerated.{u, v} :=
    CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj X).right
  let mC : A ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw :=
    CompactlyGenerated.adj.{u, v}.homEquiv A Raw (loopLandingRaw X).1
  let m : (PointedCGWH.loop.obj X).right ⟶ compactOpenLoopCarrier X :=
    CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage (by
      dsimp only [compactOpenLoopCarrier]
      exact mC)
  have hRaw := (loopLandingRaw X).2.1
  have hm :=
    (CompactlyGenerated.adj.{u, v}.homEquiv A Raw).symm_apply_apply
      (loopLandingRaw X).1
  rw [CompactlyGenerated.adj.{u, v}.homEquiv_counit] at hm
  have hmMap : CGWH.cgwhToCompactlyGenerated.map m = mC :=
    CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage _
  have hm' : CGWH.cgwhToTop.map m ≫
      CompactlyGenerated.adj.{u, v}.counit.app Raw = (loopLandingRaw X).1 := by
    change CompactlyGenerated.compactlyGeneratedToTop.map
        (CGWH.cgwhToCompactlyGenerated.map m) ≫
      CompactlyGenerated.adj.{u, v}.counit.app Raw = _
    rw [hmMap]
    exact hm
  refine Under.homMk m ?_
  apply ConcreteCategory.hom_ext
  intro p
  have hmPoint := ConcreteCategory.congr_hom hm'
    ((PointedCGWH.loop.obj X).hom p)
  change m ((PointedCGWH.loop.obj X).hom p) = Path.refl (pointValue X)
  have hmPoint' := hmPoint
  have hp : p = (show CGWH.point.{u, v} from PUnit.unit) := by
    change PUnit.{v + 1} at p
    cases p
    rfl
  rw [hp] at hmPoint' ⊢
  exact hmPoint'.trans hRaw

private noncomputable def diskEvaluationData (X : PointedCGWH.{u, v}) :
    let K := compactOpenLoopCoreflection.obj X
    let S0 := (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).left
    let Raw := TopCat.of (LoopSpace X.right (pointValue X))
    {f : PointedCGWH.diskOne.{u, v}.right ⊗ K.right ⟶ X.right //
      (((coprod.inl : CGWH.point.{u, v} ⟶ S0.right) ▷ K.right) ≫
          (PointedCGWH.diskBoundary.{u, v}.right ▷ K.right) ≫ f =
        CGWH.point_isTerminal.from (CGWH.point.{u, v} ⊗ K.right) ≫ X.hom) ∧
      (((coprod.inr : CGWH.point.{u, v} ⟶ S0.right) ▷ K.right) ≫
          (PointedCGWH.diskBoundary.{u, v}.right ▷ K.right) ≫ f =
        CGWH.point_isTerminal.from (CGWH.point.{u, v} ⊗ K.right) ≫ X.hom) ∧
      ((PointedCGWH.diskOne.{u, v}.right ◁ K.hom) ≫ f =
        CGWH.point_isTerminal.from
          (PointedCGWH.diskOne.{u, v}.right ⊗ CGWH.point.{u, v}) ≫ X.hom) ∧
      (∀ z, f z =
        (show LoopSpace X.right (pointValue X) from
          CompactlyGenerated.adj.{u, v}.counit.app Raw
            (CartesianMonoidalCategory.snd PointedCGWH.diskOne.right K.right z))
          (TopCat.I.homeomorph
            (diskIntervalIso.{u, v}.hom
              (CartesianMonoidalCategory.fst
                PointedCGWH.diskOne.right K.right z))))} := by
  let K := compactOpenLoopCoreflection.obj X
  let D := PointedCGWH.diskOne.{u, v}.right
  let Raw : TopCat.{v} := TopCat.of (LoopSpace X.right (pointValue X))
  let cK : CGWH.cgwhToTop.obj K.right ⟶ Raw := by
    change CompactlyGenerated.compactlyGeneratedToTop.obj
        (TopCat.toCompactlyGenerated.{u, v}.obj Raw) ⟶ Raw
    exact CompactlyGenerated.adj.{u, v}.counit.app Raw
  let forgetPath : C(LoopSpace X.right (pointValue X),
      C(unitInterval, X.right)) :=
    ⟨fun gamma => gamma.toContinuousMap, continuous_induced_dom⟩
  let loopFamily : C(K.right, C(unitInterval, X.right)) :=
    forgetPath.comp cK.hom
  let RawPair : TopCat.{v} := TopCat.of
    (↥(CGWH.cgwhToTop.obj D) × ↥(CGWH.cgwhToTop.obj K.right))
  let rawDiskEval : C(RawPair, X.right) :=
    (ContinuousMap.uncurry loopFamily).comp
      ⟨fun z => (z.2,
          TopCat.I.homeomorph (diskIntervalIso.{u, v}.hom z.1)),
        continuous_snd.prodMk
          ((TopCat.I.homeomorph.continuous.comp
            diskIntervalIso.{u, v}.hom.hom.continuous).comp continuous_fst)⟩
  let eTensor : D ⊗ K.right ≅ D ⨯ K.right :=
    (CartesianMonoidalCategory.tensorLeftIsoProd D).app K.right
  let tensorToRaw : CGWH.cgwhToTop.obj (D ⊗ K.right) ⟶
      RawPair :=
    CGWH.cgwhToTop.map eTensor.hom ≫ CGWH.prodComparisonToTop D K.right
  have eTensor_fst : eTensor.hom ≫ (Limits.prod.fst : D ⨯ K.right ⟶ D) =
      CartesianMonoidalCategory.fst D K.right :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct D K.right)
      (limit.isLimit _) ⟨WalkingPair.left⟩
  have eTensor_snd : eTensor.hom ≫
      (Limits.prod.snd : D ⨯ K.right ⟶ K.right) =
      CartesianMonoidalCategory.snd D K.right :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct D K.right)
      (limit.isLimit _) ⟨WalkingPair.right⟩
  have tensorToRaw_fst : tensorToRaw ≫ TopCat.prodFst =
      CGWH.cgwhToTop.map (CartesianMonoidalCategory.fst D K.right) := by
    dsimp only [tensorToRaw]
    rw [Category.assoc, CGWH.prodComparisonToTop_fst,
      ← CGWH.cgwhToTop.map_comp, eTensor_fst]
  have tensorToRaw_snd : tensorToRaw ≫ TopCat.prodSnd =
      CGWH.cgwhToTop.map (CartesianMonoidalCategory.snd D K.right) := by
    dsimp only [tensorToRaw]
    rw [Category.assoc, CGWH.prodComparisonToTop_snd,
      ← CGWH.cgwhToTop.map_comp, eTensor_snd]
  let f : D ⊗ K.right ⟶ X.right :=
    CGWH.fullyFaithfulCgwhToTop.preimage
      (tensorToRaw ≫ TopCat.ofHom rawDiskEval)
  have hf (z : (D ⊗ K.right : CGWH.{u, v})) : f z =
      cK (CartesianMonoidalCategory.snd D K.right z)
        (TopCat.I.homeomorph
          (diskIntervalIso.{u, v}.hom
            (CartesianMonoidalCategory.fst D K.right z))) := by
    have hMap := CGWH.fullyFaithfulCgwhToTop.map_preimage
      (tensorToRaw ≫ TopCat.ofHom rawDiskEval)
    have hz := ConcreteCategory.congr_hom hMap z
    have hfst := ConcreteCategory.congr_hom tensorToRaw_fst z
    have hsnd := ConcreteCategory.congr_hom tensorToRaw_snd z
    change f z = rawDiskEval (tensorToRaw z) at hz
    change (tensorToRaw z).1 =
      CartesianMonoidalCategory.fst D K.right z at hfst
    change (tensorToRaw z).2 =
      CartesianMonoidalCategory.snd D K.right z at hsnd
    change f z = cK (tensorToRaw z).2
      (TopCat.I.homeomorph
        (diskIntervalIso.{u, v}.hom (tensorToRaw z).1)) at hz
    rw [hfst, hsnd] at hz
    exact hz
  refine ⟨f, ?_, ?_, ?_, hf⟩
  · apply ConcreteCategory.hom_ext
    intro z
    let a := (coprod.inl : CGWH.point.{u, v} ⟶
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).left.right)
    let w := ((a ▷ K.right) ≫
      (PointedCGWH.diskBoundary.{u, v}.right ▷ K.right)) z
    change f w = _
    rw [hf]
    have hfst1 := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst
        a K.right) z
    have hfst2 := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst
        PointedCGWH.diskBoundary.{u, v}.right K.right) ((a ▷ K.right) z)
    have hsnd1 := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd
        a K.right) z
    have hsnd2 := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd
        PointedCGWH.diskBoundary.{u, v}.right K.right) ((a ▷ K.right) z)
    have hwfst : CartesianMonoidalCategory.fst D K.right w =
        PointedCGWH.diskBoundary.right
          (a (CartesianMonoidalCategory.fst CGWH.point K.right z)) :=
      hfst2.trans (congrArg PointedCGWH.diskBoundary.right hfst1)
    have hwsnd : CartesianMonoidalCategory.snd D K.right w =
        CartesianMonoidalCategory.snd CGWH.point K.right z :=
      hsnd2.trans hsnd1
    have hDisk : diskIntervalIso.{u, v}.inv (1 : TopCat.I.{v}) =
        PointedCGWH.diskBoundary.right
          (a (CartesianMonoidalCategory.fst CGWH.point K.right z)) := by
      have ha : a ≫ PointedCGWH.diskBoundary.{u, v}.right =
          PointedCGWH.diskOne.{u, v}.hom :=
        Under.w PointedCGWH.diskBoundary
      let e0 : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
          CGWH.point.{u, v} := by
        change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
          CGWH.point.{u, v}
        exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
      have hBase : diskIntervalIso.{u, v}.inv (1 : TopCat.I.{v}) =
          PointedCGWH.diskOne.{u, v}.hom
            (CartesianMonoidalCategory.fst CGWH.point K.right z) := by
        change SSet.stdSimplex.toTopObjIsoI.inv (1 : TopCat.I.{v}) = _
        rw [SSet.toTopObjIsoI_inv_one]
        change SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) default =
          SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2))
            (e0.inv (CartesianMonoidalCategory.fst CGWH.point K.right z))
        exact congrArg _ (Subsingleton.elim _ _)
      exact hBase.trans (ConcreteCategory.congr_hom ha _).symm
    have hTime : TopCat.I.homeomorph
        (diskIntervalIso.{u, v}.hom
          (PointedCGWH.diskBoundary.right
            (a (CartesianMonoidalCategory.fst CGWH.point K.right z)))) = 1 := by
      rw [← hDisk, Iso.inv_hom_id_apply, TopCat.I.homeomorph_one]
    rw [hwfst, hwsnd, hTime]
    exact (Path.target (cK _)).trans
      (congrArg X.hom (Subsingleton.elim _ PUnit.unit))
  · apply ConcreteCategory.hom_ext
    intro z
    let a := (coprod.inr : CGWH.point.{u, v} ⟶
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).left.right)
    let w := ((a ▷ K.right) ≫
      (PointedCGWH.diskBoundary.{u, v}.right ▷ K.right)) z
    change f w = _
    rw [hf]
    have hfst1 := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst a K.right) z
    have hfst2 := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst
        PointedCGWH.diskBoundary.{u, v}.right K.right) ((a ▷ K.right) z)
    have hsnd1 := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd a K.right) z
    have hsnd2 := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd
        PointedCGWH.diskBoundary.{u, v}.right K.right) ((a ▷ K.right) z)
    have hwfst : CartesianMonoidalCategory.fst D K.right w =
        PointedCGWH.diskBoundary.right
          (a (CartesianMonoidalCategory.fst CGWH.point K.right z)) :=
      hfst2.trans (congrArg PointedCGWH.diskBoundary.right hfst1)
    have hwsnd : CartesianMonoidalCategory.snd D K.right w =
        CartesianMonoidalCategory.snd CGWH.point K.right z :=
      hsnd2.trans hsnd1
    have hDisk : diskIntervalIso.{u, v}.inv (0 : TopCat.I.{v}) =
        PointedCGWH.diskBoundary.right
          (a (CartesianMonoidalCategory.fst CGWH.point K.right z)) := by
      let p1 : CGWH.point.{u, v} ⟶ PointedCGWH.diskOne.{u, v}.right :=
        (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
          SSet.toCGWH.{u, v}.map (SSet.stdSimplex.δ (1 : Fin 2))
      have ha : a ≫ PointedCGWH.diskBoundary.{u, v}.right = p1 := by
        dsimp only [a, p1]
        simp [PointedCGWH.diskBoundary]
      let e0 : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
          CGWH.point.{u, v} := by
        change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
          CGWH.point.{u, v}
        exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
      have hBase : diskIntervalIso.{u, v}.inv (0 : TopCat.I.{v}) =
          p1 (CartesianMonoidalCategory.fst CGWH.point K.right z) := by
        change SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I.{v}) = _
        rw [SSet.toTopObjIsoI_inv_zero]
        change SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) default =
          SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2))
            (e0.inv (CartesianMonoidalCategory.fst CGWH.point K.right z))
        exact congrArg _ (Subsingleton.elim _ _)
      exact hBase.trans (ConcreteCategory.congr_hom ha _).symm
    have hTime : TopCat.I.homeomorph
        (diskIntervalIso.{u, v}.hom
          (PointedCGWH.diskBoundary.right
            (a (CartesianMonoidalCategory.fst CGWH.point K.right z)))) = 0 := by
      rw [← hDisk, Iso.inv_hom_id_apply, TopCat.I.homeomorph_zero]
    rw [hwfst, hwsnd, hTime]
    exact (Path.source (cK _)).trans
      (congrArg X.hom (Subsingleton.elim _ PUnit.unit))
  · apply ConcreteCategory.hom_ext
    intro z
    let w := (D ◁ K.hom) z
    change f w = _
    rw [hf]
    have hsnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_snd D K.hom) z
    have hwsnd : CartesianMonoidalCategory.snd D K.right w =
        K.hom (CartesianMonoidalCategory.snd D CGWH.point z) := hsnd
    have hKpoint : cK (K.hom
        (CartesianMonoidalCategory.snd D CGWH.point z)) =
        Path.refl (pointValue X) := by
      change CompactlyGenerated.adj.{u, v}.counit.app Raw
          (Path.refl (pointValue X)) = Path.refl (pointValue X)
      exact CompactlyGenerated.adjCounit_apply.{v, u} _ _
    rw [hwsnd, hKpoint]
    change pointValue X = X.hom
      (CGWH.point_isTerminal.from (D ⊗ CGWH.point) z)
    have hp : (show CGWH.point.{u, v} from PUnit.unit) =
        CGWH.point_isTerminal.from (D ⊗ CGWH.point) z := by
      change (PUnit.unit : PUnit.{v + 1}) = _
      exact Subsingleton.elim _ _
    exact congrArg X.hom hp

private noncomputable def fromCompactOpen (X : PointedCGWH.{u, v}) :
    {f : compactOpenLoopCoreflection.obj X ⟶ PointedCGWH.loop.obj X //
      f ≫ toCompactOpen X = 𝟙 (compactOpenLoopCoreflection.obj X) ∧
        toCompactOpen X ≫ f = 𝟙 (PointedCGWH.loop.obj X)} := by
  let K := compactOpenLoopCoreflection.obj X
  let S0 := (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).left
  let T := ⊤_ PointedCGWH.{u, v}
  let d := diskEvaluationData X
  let qD : PointedCGWH.diskOne.{u, v} ⟶
      (HomotopicalAlgebra.ordinaryCofiber
        (C := PointedCGWH.{u, v})).obj
          (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) :=
    pushout.inl PointedCGWH.diskBoundary (terminal.from S0)
  let qT : T ⟶
      (HomotopicalAlgebra.ordinaryCofiber
        (C := PointedCGWH.{u, v})).obj
          (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) :=
    pushout.inr PointedCGWH.diskBoundary (terminal.from S0)
  let hUnder : IsPushout PointedCGWH.diskBoundary (terminal.from S0) qD qT :=
    IsPushout.of_hasPushout _ _
  let hCarrier := hUnder.map (Under.forget CGWH.point.{u, v})
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : (tensorRight K.right).IsLeftAdjoint := inferInstance
  let hTensor := hCarrier.map (tensorRight K.right)
  let constT : T.right ⊗ K.right ⟶ X.right :=
    CGWH.point_isTerminal.from _ ≫ X.hom
  have hCompat :
      (PointedCGWH.diskBoundary.right ▷ K.right) ≫ d.1 =
        ((terminal.from S0).right ▷ K.right) ≫ constT := by
    let F := tensorRight K.right
    let hCop := isColimitOfPreserves F
      (coprodIsCoprod CGWH.point.{u, v} CGWH.point.{u, v})
    apply hCop.hom_ext
    rintro ⟨j⟩
    rcases j with (_ | _)
    · change ((coprod.inl : CGWH.point.{u, v} ⟶ S0.right) ▷ K.right) ≫
          (PointedCGWH.diskBoundary.right ▷ K.right) ≫ d.1 = _
      rw [d.2.1]
      let r : CGWH.point.{u, v} ⊗ K.right ⟶ CGWH.point :=
        ((coprod.inl : CGWH.point.{u, v} ⟶ S0.right) ▷ K.right) ≫
          ((terminal.from S0).right ▷ K.right) ≫
            CGWH.point_isTerminal.from (T.right ⊗ K.right)
      have hr : CGWH.point_isTerminal.from
          (CGWH.point.{u, v} ⊗ K.right) = r :=
        CGWH.point_isTerminal.hom_ext _ _
      rw [hr]
      dsimp only [r, constT, F]
      rfl
    · change ((coprod.inr : CGWH.point.{u, v} ⟶ S0.right) ▷ K.right) ≫
          (PointedCGWH.diskBoundary.right ▷ K.right) ≫ d.1 = _
      rw [d.2.2.1]
      let r : CGWH.point.{u, v} ⊗ K.right ⟶ CGWH.point :=
        ((coprod.inr : CGWH.point.{u, v} ⟶ S0.right) ▷ K.right) ≫
          ((terminal.from S0).right ▷ K.right) ≫
            CGWH.point_isTerminal.from (T.right ⊗ K.right)
      have hr : CGWH.point_isTerminal.from
          (CGWH.point.{u, v} ⊗ K.right) = r :=
        CGWH.point_isTerminal.hom_ext _ _
      rw [hr]
      dsimp only [r, constT, F]
      rfl
  let C0 := (HomotopicalAlgebra.ordinaryCofiber
    (C := PointedCGWH.{u, v})).obj
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary)
  let cofiberEval : C0.right ⊗ K.right ⟶ X.right :=
    hTensor.desc d.1 constT hCompat
  have hTensorInl : (qD.right ▷ K.right) ≫ cofiberEval = d.1 := by
    change (tensorRight K.right).map ((Under.forget CGWH.point).map qD) ≫
      hTensor.desc d.1 constT hCompat = d.1
    exact hTensor.inl_desc _ _ _
  have hTensorInr : (qT.right ▷ K.right) ≫ cofiberEval = constT := by
    change (tensorRight K.right).map ((Under.forget CGWH.point).map qT) ≫
      hTensor.desc d.1 constT hCompat = constT
    exact hTensor.inr_desc _ _ _
  let eC := PointedCGWH.diskCofiberIsoSphereOne.{u, v}
  let sphereEval : PointedCGWH.sphereOne.{u, v}.right ⊗ K.right ⟶ X.right :=
    (eC.inv.right ▷ K.right) ≫ cofiberEval
  have hDiskCofiber : diskToSphere.{u, v} ≫ eC.inv = qD := by
    apply (cancel_mono eC.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Under.UnderMorphism.ext
    unfold eC qD diskToSphere PointedCGWH.diskCofiberIsoSphereOne
    dsimp
    generalize_proofs _ hP
    let hOrd := IsPushout.of_hasPushout PointedCGWH.diskBoundary
      (terminal.from S0)
    exact congrArg Under.Hom.right
      (hOrd.inl_isoIsPushout_hom _ _ (by assumption)).symm
  have hSpherePoint :
      (PointedCGWH.sphereOne.{u, v}.hom ▷ K.right) ≫ sphereEval =
        CGWH.point_isTerminal.from (CGWH.point.{u, v} ⊗ K.right) ≫ X.hom := by
    have he : PointedCGWH.sphereOne.hom ≫ eC.inv.right = C0.hom :=
      Under.w eC.inv
    have hq : T.hom ≫ qT.right = C0.hom := Under.w qT
    change (PointedCGWH.sphereOne.hom ▷ K.right) ≫
      (eC.inv.right ▷ K.right) ≫ cofiberEval = _
    slice_lhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight]
    rw [he, ← hq, MonoidalCategory.comp_whiskerRight]
    slice_lhs 2 3 => rw [hTensorInr]
    let r : CGWH.point.{u, v} ⊗ K.right ⟶ CGWH.point :=
      (T.hom ▷ K.right) ≫
        CGWH.point_isTerminal.from (T.right ⊗ K.right)
    have hr : r = CGWH.point_isTerminal.from
        (CGWH.point.{u, v} ⊗ K.right) :=
      CGWH.point_isTerminal.hom_ext _ _
    change r ≫ X.hom = _
    rw [hr]
  let _ : (tensorRight CGWH.point.{u, v}).IsLeftAdjoint := inferInstance
  let hTensorPoint := hCarrier.map (tensorRight CGWH.point.{u, v})
  have hCofiberConst : (C0.right ◁ K.hom) ≫ cofiberEval =
      CGWH.point_isTerminal.from (C0.right ⊗ CGWH.point.{u, v}) ≫ X.hom := by
    apply hTensorPoint.hom_ext
    · change (qD.right ▷ CGWH.point.{u, v}) ≫
          (C0.right ◁ K.hom) ≫ cofiberEval =
        (qD.right ▷ CGWH.point.{u, v}) ≫
          CGWH.point_isTerminal.from (C0.right ⊗ CGWH.point) ≫ X.hom
      have hInterchange : (qD.right ▷ CGWH.point.{u, v}) ≫
          (C0.right ◁ K.hom) =
          (PointedCGWH.diskOne.right ◁ K.hom) ≫ (qD.right ▷ K.right) := by
        change (qD.right ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ K.hom) =
          (𝟙 _ ⊗ₘ K.hom) ≫ (qD.right ⊗ₘ 𝟙 _)
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
        simp
      slice_lhs 1 2 => rw [hInterchange]
      slice_lhs 2 3 => rw [hTensorInl]
      rw [d.2.2.2.1]
      let r : PointedCGWH.diskOne.right ⊗ CGWH.point ⟶ CGWH.point :=
        (qD.right ▷ CGWH.point.{u, v}) ≫
          CGWH.point_isTerminal.from (C0.right ⊗ CGWH.point)
      have hr : CGWH.point_isTerminal.from
          (PointedCGWH.diskOne.right ⊗ CGWH.point) = r :=
        CGWH.point_isTerminal.hom_ext _ _
      rw [hr]
      dsimp only [r]
      rw [Category.assoc]
    · change (qT.right ▷ CGWH.point.{u, v}) ≫
          (C0.right ◁ K.hom) ≫ cofiberEval =
        (qT.right ▷ CGWH.point.{u, v}) ≫
          CGWH.point_isTerminal.from (C0.right ⊗ CGWH.point) ≫ X.hom
      have hInterchange : (qT.right ▷ CGWH.point.{u, v}) ≫
          (C0.right ◁ K.hom) =
          (T.right ◁ K.hom) ≫ (qT.right ▷ K.right) := by
        change (qT.right ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ K.hom) =
          (𝟙 _ ⊗ₘ K.hom) ≫ (qT.right ⊗ₘ 𝟙 _)
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
        simp
      slice_lhs 1 2 => rw [hInterchange]
      slice_lhs 2 3 => rw [hTensorInr]
      let r1 : T.right ⊗ CGWH.point ⟶ CGWH.point :=
        (T.right ◁ K.hom) ≫
          CGWH.point_isTerminal.from (T.right ⊗ K.right)
      let r2 : T.right ⊗ CGWH.point ⟶ CGWH.point :=
        (qT.right ▷ CGWH.point.{u, v}) ≫
          CGWH.point_isTerminal.from (C0.right ⊗ CGWH.point)
      have hr : r1 = r2 := CGWH.point_isTerminal.hom_ext _ _
      change r1 ≫ X.hom = r2 ≫ X.hom
      rw [hr]
  have hSphereConst :
      (PointedCGWH.sphereOne.right ◁ K.hom) ≫ sphereEval =
        CGWH.point_isTerminal.from
          (PointedCGWH.sphereOne.right ⊗ CGWH.point.{u, v}) ≫ X.hom := by
    have hInterchange : (PointedCGWH.sphereOne.right ◁ K.hom) ≫
        (eC.inv.right ▷ K.right) =
        (eC.inv.right ▷ CGWH.point.{u, v}) ≫ (C0.right ◁ K.hom) := by
      change (𝟙 _ ⊗ₘ K.hom) ≫ (eC.inv.right ⊗ₘ 𝟙 _) =
        (eC.inv.right ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ K.hom)
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      simp
    change (PointedCGWH.sphereOne.right ◁ K.hom) ≫
      (eC.inv.right ▷ K.right) ≫ cofiberEval = _
    rw [← Category.assoc, hInterchange, Category.assoc, hCofiberConst]
    let r : PointedCGWH.sphereOne.right ⊗ CGWH.point ⟶ CGWH.point :=
      (eC.inv.right ▷ CGWH.point.{u, v}) ≫
        CGWH.point_isTerminal.from (C0.right ⊗ CGWH.point)
    have hr : r = CGWH.point_isTerminal.from
        (PointedCGWH.sphereOne.right ⊗ CGWH.point) :=
      CGWH.point_isTerminal.hom_ext _ _
    change r ≫ X.hom = _
    rw [hr]
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne K
  let q : PointedCGWH.sphereOne.{u, v}.right ⊗ K.right ⟶
      ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj K).right := p.2.1.inl
  let leftRaw : PointedCGWH.sphereOne.right ⟶
      PointedCGWH.sphereOne.right ⊗ K.right :=
    CartesianMonoidalCategory.lift (𝟙 _)
      (CGWH.point_isTerminal.from _ ≫ K.hom)
  let rightRaw : K.right ⟶ PointedCGWH.sphereOne.right ⊗ K.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from _ ≫ PointedCGWH.sphereOne.hom) (𝟙 _)
  have hLeft : leftRaw ≫ sphereEval =
      CGWH.point_isTerminal.from PointedCGWH.sphereOne.right ≫ X.hom := by
    let insert : PointedCGWH.sphereOne.right ⟶
        PointedCGWH.sphereOne.right ⊗ CGWH.point.{u, v} :=
      CartesianMonoidalCategory.lift (𝟙 _)
        (CGWH.point_isTerminal.from _)
    have hi : insert ≫ (PointedCGWH.sphereOne.right ◁ K.hom) = leftRaw := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [insert, leftRaw]
    rw [← hi, Category.assoc, hSphereConst]
    let r : PointedCGWH.sphereOne.right ⟶ CGWH.point :=
      insert ≫ CGWH.point_isTerminal.from
        (PointedCGWH.sphereOne.right ⊗ CGWH.point)
    have hr : r = CGWH.point_isTerminal.from
        PointedCGWH.sphereOne.right :=
      CGWH.point_isTerminal.hom_ext _ _
    change r ≫ X.hom = _
    rw [hr]
  have hRight : rightRaw ≫ sphereEval =
      CGWH.point_isTerminal.from K.right ≫ X.hom := by
    let insert : K.right ⟶ CGWH.point.{u, v} ⊗ K.right :=
      CartesianMonoidalCategory.lift (CGWH.point_isTerminal.from _) (𝟙 _)
    have hi : insert ≫ (PointedCGWH.sphereOne.hom ▷ K.right) = rightRaw := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [insert, rightRaw]
    rw [← hi, Category.assoc, hSpherePoint]
    let r : K.right ⟶ CGWH.point :=
      insert ≫ CGWH.point_isTerminal.from (CGWH.point ⊗ K.right)
    have hr : r = CGWH.point_isTerminal.from K.right :=
      CGWH.point_isTerminal.hom_ext _ _
    change r ≫ X.hom = _
    rw [hr]
  let wedgeInl : PointedCGWH.sphereOne.{u, v} ⟶
      ((CategoryTheory.Pointed.wedge CGWH.point).obj
        PointedCGWH.sphereOne).obj K :=
    Under.homMk (pushout.inl PointedCGWH.sphereOne.hom K.hom) rfl
  let wedgeInr : K ⟶
      ((CategoryTheory.Pointed.wedge CGWH.point).obj
        PointedCGWH.sphereOne).obj K :=
    Under.homMk (pushout.inr PointedCGWH.sphereOne.hom K.hom)
      pushout.condition.symm
  have hpInl : wedgeInl.right ≫ p.1.right = leftRaw := by
    change pushout.inl PointedCGWH.sphereOne.hom K.hom ≫
      pushout.desc _ _ _ = _
    rw [pushout.inl_desc]
    rfl
  have hpInr : wedgeInr.right ≫ p.1.right = rightRaw := by
    change pushout.inr PointedCGWH.sphereOne.hom K.hom ≫
      pushout.desc _ _ _ = _
    rw [pushout.inr_desc]
    rfl
  have hWedge : p.1.right ≫ sphereEval =
      CGWH.point_isTerminal.from
        (((CategoryTheory.Pointed.wedge CGWH.point).obj
          PointedCGWH.sphereOne).obj K).right ≫ X.hom := by
    apply pushout.hom_ext
    · change wedgeInl.right ≫ p.1.right ≫ sphereEval =
        wedgeInl.right ≫ CGWH.point_isTerminal.from
          (((CategoryTheory.Pointed.wedge CGWH.point).obj
            PointedCGWH.sphereOne).obj K).right ≫ X.hom
      slice_lhs 1 2 => rw [hpInl]
      rw [Category.assoc, hLeft]
      let r : PointedCGWH.sphereOne.right ⟶ CGWH.point :=
        wedgeInl.right ≫ CGWH.point_isTerminal.from
          (((CategoryTheory.Pointed.wedge CGWH.point).obj
            PointedCGWH.sphereOne).obj K).right
      have hr : CGWH.point_isTerminal.from PointedCGWH.sphereOne.right = r :=
        CGWH.point_isTerminal.hom_ext _ _
      rw [hr]
      rfl
    · change wedgeInr.right ≫ p.1.right ≫ sphereEval =
        wedgeInr.right ≫ CGWH.point_isTerminal.from
          (((CategoryTheory.Pointed.wedge CGWH.point).obj
            PointedCGWH.sphereOne).obj K).right ≫ X.hom
      slice_lhs 1 2 => rw [hpInr]
      rw [Category.assoc, hRight]
      let r : K.right ⟶ CGWH.point :=
        wedgeInr.right ≫ CGWH.point_isTerminal.from
          (((CategoryTheory.Pointed.wedge CGWH.point).obj
            PointedCGWH.sphereOne).obj K).right
      have hr : CGWH.point_isTerminal.from K.right = r :=
        CGWH.point_isTerminal.hom_ext _ _
      rw [hr]
      rfl
  let evalSmash : (PointedCGWH.smash.obj PointedCGWH.sphereOne).obj K ⟶ X :=
    Under.homMk (PushoutCocone.IsColimit.desc p.2.2 sphereEval X.hom hWedge)
      (PushoutCocone.IsColimit.inr_desc p.2.2 _ _ _)
  let invMapCore : K ⟶
      (PointedCGWH.power PointedCGWH.sphereOne).obj X :=
    (PointedCGWH.suspensionLoopAdjunction.homEquiv K X) evalSmash
  let invMap : K ⟶ PointedCGWH.loop.obj X := invMapCore
  let toCore : (PointedCGWH.power PointedCGWH.sphereOne).obj X ⟶ K :=
    toCompactOpen X
  have hTo (eta : (PointedCGWH.loop.obj X).right) :
      (toCompactOpen X).right eta = (loopLandingRaw X).1 eta := by
    let Raw : TopCat.{v} := TopCat.of (LoopSpace X.right (pointValue X))
    let A : CompactlyGenerated.{u, v} :=
      CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj X).right
    let mC : A ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw :=
      CompactlyGenerated.adj.{u, v}.homEquiv A Raw (loopLandingRaw X).1
    let m : (PointedCGWH.loop.obj X).right ⟶ compactOpenLoopCarrier X :=
      CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage (by
        dsimp only [compactOpenLoopCarrier]
        exact mC)
    have hm := (CompactlyGenerated.adj.{u, v}.homEquiv A Raw).symm_apply_apply
      (loopLandingRaw X).1
    rw [CompactlyGenerated.adj.{u, v}.homEquiv_counit] at hm
    have hmEta := ConcreteCategory.congr_hom hm eta
    have hmEta' := hmEta
    have hMap := ConcreteCategory.congr_hom
      (CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage
        (X := (PointedCGWH.loop.obj X).right)
        (Y := compactOpenLoopCarrier X) (by
        change A ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw
        exact mC)) eta
    change m eta = (loopLandingRaw X).1 eta
    change m eta = mC eta at hMap
    exact hMap.trans hmEta'
  have hDiskSphereEval :
      (diskToSphere.{u, v}.right ▷ K.right) ≫ sphereEval = d.1 := by
    have hDiskCofiberRight : diskToSphere.{u, v}.right ≫ eC.inv.right =
        qD.right := by
      simpa only [Under.comp_right] using
        congrArg Under.Hom.right hDiskCofiber
    change (diskToSphere.{u, v}.right ▷ K.right) ≫
      (eC.inv.right ▷ K.right) ≫ cofiberEval = d.1
    slice_lhs 1 2 =>
      rw [← MonoidalCategory.comp_whiskerRight,
        hDiskCofiberRight]
    exact hTensorInl
  have hSphereEval (gamma : K.right) (t : unitInterval) :
      let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
        ConcreteCategory.ofHom (ContinuousMap.const _
          (sphereOneParam.{u, v} (TopCat.I.homeomorph.symm t)))
      let b : CGWH.point.{u, v} ⟶ K.right :=
        ConcreteCategory.ofHom (ContinuousMap.const _ gamma)
      sphereEval (CartesianMonoidalCategory.lift a b PUnit.unit) =
        (show LoopSpace X.right (pointValue X) from
          CompactlyGenerated.adj.{u, v}.counit.app
            (TopCat.of (LoopSpace X.right (pointValue X))) gamma) t := by
    let s : TopCat.I.{v} := TopCat.I.homeomorph.symm t
    let aD : CGWH.point.{u, v} ⟶ PointedCGWH.diskOne.{u, v}.right :=
      ConcreteCategory.ofHom
        (ContinuousMap.const _ (diskIntervalIso.{u, v}.inv s))
    let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
      ConcreteCategory.ofHom (ContinuousMap.const _ (sphereOneParam.{u, v} s))
    let b : CGWH.point.{u, v} ⟶ K.right :=
      ConcreteCategory.ofHom (ContinuousMap.const _ gamma)
    let z : (PointedCGWH.diskOne.{u, v}.right ⊗ K.right : CGWH.{u, v}) :=
      CartesianMonoidalCategory.lift aD b PUnit.unit
    have ha : aD ≫ diskToSphere.{u, v}.right = a := by
      apply ConcreteCategory.hom_ext
      intro p
      rfl
    have hz : (diskToSphere.{u, v}.right ▷ K.right) z =
        CartesianMonoidalCategory.lift a b PUnit.unit := by
      let pairD := CartesianMonoidalCategory.lift aD b
      let pairS := CartesianMonoidalCategory.lift a b
      have hPair : pairD ≫ (diskToSphere.{u, v}.right ▷ K.right) =
          pairS := by
        dsimp only [pairD, pairS]
        change CartesianMonoidalCategory.lift aD b ≫
            (diskToSphere.{u, v}.right ⊗ₘ 𝟙 K.right) =
          CartesianMonoidalCategory.lift a b
        rw [CartesianMonoidalCategory.lift_map, ha]
        simp
      exact ConcreteCategory.congr_hom hPair PUnit.unit
    change sphereEval (CartesianMonoidalCategory.lift a b PUnit.unit) = _
    rw [← hz]
    change ((diskToSphere.{u, v}.right ▷ K.right) ≫ sphereEval) z = _
    rw [hDiskSphereEval, d.2.2.2.2]
    have hfst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst aD b) PUnit.unit
    have hsnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd aD b) PUnit.unit
    change CartesianMonoidalCategory.fst PointedCGWH.diskOne.right K.right z =
      aD PUnit.unit at hfst
    change CartesianMonoidalCategory.snd PointedCGWH.diskOne.right K.right z =
      b PUnit.unit at hsnd
    rw [hfst, hsnd]
    change (show LoopSpace X.right (pointValue X) from
      CompactlyGenerated.adj.{u, v}.counit.app
        (TopCat.of (LoopSpace X.right (pointValue X))) gamma)
          (TopCat.I.homeomorph
            (diskIntervalIso.{u, v}.hom
              (diskIntervalIso.{u, v}.inv s))) =
      (show LoopSpace X.right (pointValue X) from
        CompactlyGenerated.adj.{u, v}.counit.app
          (TopCat.of (LoopSpace X.right (pointValue X))) gamma) t
    rw [Iso.inv_hom_id_apply]
    have hs : TopCat.I.homeomorph.{v} s = t := by
      dsimp only [s]
      exact TopCat.I.homeomorph.{v}.apply_symm_apply t
    rw [hs]
  have hUncurry :
      ((PointedCGWH.smash.obj PointedCGWH.sphereOne).map invMapCore) ≫
          (PointedCGWH.basedEval PointedCGWH.sphereOne).app X =
        evalSmash := by
    have h :=
      (PointedCGWH.suspensionLoopAdjunction.homEquiv K X).symm_apply_apply
        evalSmash
    rw [PointedCGWH.suspensionLoopAdjunction.homEquiv_counit] at h
    exact h
  let pL := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
      ((PointedCGWH.power PointedCGWH.sphereOne).obj X)
  let qL : PointedCGWH.sphereOne.{u, v}.right ⊗
      ((PointedCGWH.power PointedCGWH.sphereOne).obj X).right ⟶
        ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
          ((PointedCGWH.power PointedCGWH.sphereOne).obj X)).right :=
    pL.2.1.inl
  have hSmashMap : q ≫
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          invMapCore).right) =
      ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ invMapCore.right) ≫ qL := by
    change (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne K).2.1.inl ≫
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          invMapCore).right) =
      ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ invMapCore.right) ≫
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
            ((PointedCGWH.power PointedCGWH.sphereOne).obj X)).2.1.inl
    unfold PointedCGWH.smash CategoryTheory.Pointed.smash
    exact PushoutCocone.IsColimit.inl_desc
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne K).2.2 _ _ _
  let pN := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
      (PointedCGWH.loop.obj X)
  let qN : PointedCGWH.sphereOne.{u, v}.right ⊗
      (PointedCGWH.loop.obj X).right ⟶
        ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
          (PointedCGWH.loop.obj X)).right := pN.2.1.inl
  let evN : (PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
      (PointedCGWH.loop.obj X) ⟶ X :=
    (PointedCGWH.basedEval PointedCGWH.sphereOne).app X
  have hSmashTo : qN ≫
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (toCompactOpen X)).right) =
      ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ (toCompactOpen X).right) ≫ q := by
    change (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
          (PointedCGWH.loop.obj X)).2.1.inl ≫
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (toCompactOpen X)).right) =
      ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ (toCompactOpen X).right) ≫
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne K).2.1.inl
    unfold PointedCGWH.smash CategoryTheory.Pointed.smash
    exact PushoutCocone.IsColimit.inl_desc
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
          (PointedCGWH.loop.obj X)).2.2 _ _ _
  have hInterchangeDisk :
      (diskToSphere.{u, v}.right ▷ (PointedCGWH.loop.obj X).right) ≫
          ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ (toCompactOpen X).right) =
        ((𝟙 PointedCGWH.diskOne.right) ⊗ₘ (toCompactOpen X).right) ≫
          (diskToSphere.{u, v}.right ▷ K.right) := by
    change (diskToSphere.{u, v}.right ⊗ₘ 𝟙 _) ≫
        (𝟙 _ ⊗ₘ (toCompactOpen X).right) =
      (𝟙 _ ⊗ₘ (toCompactOpen X).right) ≫
        (diskToSphere.{u, v}.right ⊗ₘ 𝟙 _)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp
  have hDiskTensorEval :
      (diskToSphere.{u, v}.right ▷ (PointedCGWH.loop.obj X).right) ≫
          ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ (toCompactOpen X).right) ≫
            sphereEval =
        (diskToSphere.{u, v}.right ▷ (PointedCGWH.loop.obj X).right) ≫
          qN ≫ evN.right := by
    rw [← Category.assoc, hInterchangeDisk, Category.assoc,
      hDiskSphereEval]
    apply ConcreteCategory.hom_ext
    intro z
    let eta : (PointedCGWH.loop.obj X).right :=
      CartesianMonoidalCategory.snd PointedCGWH.diskOne.right
        (PointedCGWH.loop.obj X).right z
    let x : PointedCGWH.diskOne.{u, v}.right :=
      CartesianMonoidalCategory.fst PointedCGWH.diskOne.right
        (PointedCGWH.loop.obj X).right z
    let t : unitInterval :=
      TopCat.I.homeomorph.{v} (diskIntervalIso.{u, v}.hom x)
    let aD : CGWH.point.{u, v} ⟶ PointedCGWH.diskOne.{u, v}.right :=
      ConcreteCategory.ofHom (ContinuousMap.const _ x)
    let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
      ConcreteCategory.ofHom (ContinuousMap.const _
        (sphereOneParam.{u, v} (TopCat.I.homeomorph.{v}.symm t)))
    let b : CGWH.point.{u, v} ⟶ (PointedCGWH.loop.obj X).right :=
      ConcreteCategory.ofHom (ContinuousMap.const _ eta)
    let c : CGWH.point.{u, v} ⟶
        PointedCGWH.diskOne.{u, v}.right ⊗
          (PointedCGWH.loop.obj X).right :=
      ConcreteCategory.ofHom (ContinuousMap.const _ z)
    have hc : CartesianMonoidalCategory.lift aD b = c := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [CartesianMonoidalCategory.lift_fst]
        apply ConcreteCategory.hom_ext
        intro p
        rfl
      · rw [CartesianMonoidalCategory.lift_snd]
        apply ConcreteCategory.hom_ext
        intro p
        rfl
    have hz : CartesianMonoidalCategory.lift aD b PUnit.unit = z := by
      rw [hc]
      rfl
    have ha : aD ≫ diskToSphere.{u, v}.right = a := by
      apply ConcreteCategory.hom_ext
      intro p
      change diskToSphere.{u, v}.right x =
        diskToSphere.{u, v}.right
          (diskIntervalIso.{u, v}.inv
            (TopCat.I.homeomorph.{v}.symm
              (TopCat.I.homeomorph.{v} (diskIntervalIso.{u, v}.hom x))))
      rw [TopCat.I.homeomorph.{v}.symm_apply_apply]
      have hx : diskIntervalIso.{u, v}.inv
          (diskIntervalIso.{u, v}.hom x) = x :=
        diskIntervalIso.{u, v}.hom_inv_id_apply x
      rw [hx]
    have hPair : CartesianMonoidalCategory.lift aD b ≫
        (diskToSphere.{u, v}.right ▷ (PointedCGWH.loop.obj X).right) =
      CartesianMonoidalCategory.lift a b := by
      change CartesianMonoidalCategory.lift aD b ≫
          (diskToSphere.{u, v}.right ⊗ₘ 𝟙 _) =
        CartesianMonoidalCategory.lift a b
      rw [CartesianMonoidalCategory.lift_map, ha]
      simp
    have hMapped :
        (diskToSphere.{u, v}.right ▷ (PointedCGWH.loop.obj X).right) z =
          CartesianMonoidalCategory.lift a b PUnit.unit := by
      rw [← hz]
      exact ConcreteCategory.congr_hom hPair PUnit.unit
    let w := ((𝟙 PointedCGWH.diskOne.right) ⊗ₘ
      (toCompactOpen X).right) z
    change d.1 w =
      evN.right (qN ((diskToSphere.{u, v}.right ▷
        (PointedCGWH.loop.obj X).right) z))
    rw [d.2.2.2.2]
    have hfst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_fst
        PointedCGWH.diskOne.right (toCompactOpen X).right) z
    have hsnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_snd
        PointedCGWH.diskOne.right (toCompactOpen X).right) z
    change CartesianMonoidalCategory.fst PointedCGWH.diskOne.right K.right w =
      x at hfst
    change CartesianMonoidalCategory.snd PointedCGWH.diskOne.right K.right w =
      (toCompactOpen X).right eta at hsnd
    rw [hfst, hsnd]
    have hCounit := CompactlyGenerated.adjCounit_apply.{v, u}
      (TopCat.of (LoopSpace X.right (pointValue X)))
        ((toCompactOpen X).right eta)
    have hCounitAt := congrArg
      (fun gamma : LoopSpace X.right (pointValue X) => gamma t) hCounit
    have hToAt := congrArg
      (fun gamma : LoopSpace X.right (pointValue X) => gamma t) (hTo eta)
    have hLanding := (loopLandingRaw X).2.2 eta t
    change (loopLandingRaw X).1 eta t =
      evN.right (qN (CartesianMonoidalCategory.lift a b PUnit.unit)) at hLanding
    have hMappedEval := congrArg
      (fun y => evN.right (qN y)) hMapped.symm
    exact hCounitAt.trans (hToAt.trans (hLanding.trans hMappedEval))
  let rightRawN : (PointedCGWH.loop.obj X).right ⟶
      PointedCGWH.sphereOne.{u, v}.right ⊗
        (PointedCGWH.loop.obj X).right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from _ ≫ PointedCGWH.sphereOne.hom) (𝟙 _)
  let wedgeInrN : PointedCGWH.loop.obj X ⟶
      ((CategoryTheory.Pointed.wedge CGWH.point).obj
        PointedCGWH.sphereOne).obj (PointedCGWH.loop.obj X) :=
    Under.homMk
      (pushout.inr PointedCGWH.sphereOne.hom
        (PointedCGWH.loop.obj X).hom) pushout.condition.symm
  have hpInrN : wedgeInrN.right ≫ pN.1.right = rightRawN := by
    change pushout.inr PointedCGWH.sphereOne.hom
        (PointedCGWH.loop.obj X).hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inr_desc]
    rfl
  have hRightBase : rightRawN ≫ qN =
      CGWH.point_isTerminal.from (PointedCGWH.loop.obj X).right ≫
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
          (PointedCGWH.loop.obj X)).hom) := by
    rw [← hpInrN, Category.assoc]
    change wedgeInrN.right ≫ pN.1.right ≫ pN.2.1.inl = _
    rw [pN.2.1.condition, ← Category.assoc]
    exact congrArg
      (fun k : (PointedCGWH.loop.obj X).right ⟶ CGWH.point =>
        k ≫ ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
          (PointedCGWH.loop.obj X)).hom)
      (CGWH.point_isTerminal.hom_ext _ _)
  let projN : CGWH.point.{u, v} ⊗ (PointedCGWH.loop.obj X).right ⟶
      (PointedCGWH.loop.obj X).right :=
    CartesianMonoidalCategory.snd CGWH.point (PointedCGWH.loop.obj X).right
  have hBaseFactor :
      (PointedCGWH.sphereOne.{u, v}.hom ▷
          (PointedCGWH.loop.obj X).right) =
        projN ≫ rightRawN := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.whiskerRight_fst,
        Category.assoc, CartesianMonoidalCategory.lift_fst]
      exact congrArg (fun k : CGWH.point ⊗
          (PointedCGWH.loop.obj X).right ⟶ CGWH.point =>
            k ≫ PointedCGWH.sphereOne.hom)
        (CGWH.point_isTerminal.hom_ext
          (CartesianMonoidalCategory.fst CGWH.point
            (PointedCGWH.loop.obj X).right)
          (projN ≫ CGWH.point_isTerminal.from
            (PointedCGWH.loop.obj X).right))
    · rw [CartesianMonoidalCategory.whiskerRight_snd,
        Category.assoc, CartesianMonoidalCategory.lift_snd,
        Category.comp_id]
  have hBaseQuotient :
      (PointedCGWH.sphereOne.{u, v}.hom ▷
          (PointedCGWH.loop.obj X).right) ≫ qN =
        CGWH.point_isTerminal.from
            (CGWH.point.{u, v} ⊗ (PointedCGWH.loop.obj X).right) ≫
          (((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
            (PointedCGWH.loop.obj X)).hom) := by
    rw [hBaseFactor, Category.assoc, hRightBase]
    rw [← Category.assoc]
    exact congrArg (fun k : CGWH.point ⊗
        (PointedCGWH.loop.obj X).right ⟶ CGWH.point =>
          k ≫ ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
            (PointedCGWH.loop.obj X)).hom)
      (CGWH.point_isTerminal.hom_ext
        (projN ≫ CGWH.point_isTerminal.from
          (PointedCGWH.loop.obj X).right)
        (CGWH.point_isTerminal.from
          (CGWH.point ⊗ (PointedCGWH.loop.obj X).right)))
  have hInterchangePoint :
      (PointedCGWH.sphereOne.{u, v}.hom ▷
          (PointedCGWH.loop.obj X).right) ≫
        ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ (toCompactOpen X).right) =
      (CGWH.point.{u, v} ◁ (toCompactOpen X).right) ≫
        (PointedCGWH.sphereOne.hom ▷ K.right) := by
    change (PointedCGWH.sphereOne.hom ⊗ₘ 𝟙 _) ≫
        (𝟙 _ ⊗ₘ (toCompactOpen X).right) =
      (𝟙 _ ⊗ₘ (toCompactOpen X).right) ≫
        (PointedCGWH.sphereOne.hom ⊗ₘ 𝟙 _)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp
  have hPointTensorEval :
      (PointedCGWH.sphereOne.{u, v}.hom ▷
          (PointedCGWH.loop.obj X).right) ≫
          ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ (toCompactOpen X).right) ≫
            sphereEval =
        (PointedCGWH.sphereOne.{u, v}.hom ▷
          (PointedCGWH.loop.obj X).right) ≫ qN ≫ evN.right := by
    rw [← Category.assoc, hInterchangePoint, Category.assoc, hSpherePoint]
    slice_rhs 1 2 => rw [hBaseQuotient]
    rw [Category.assoc, Under.w evN]
    rw [← Category.assoc]
    exact congrArg (fun k : CGWH.point ⊗
        (PointedCGWH.loop.obj X).right ⟶ CGWH.point => k ≫ X.hom)
      (CGWH.point_isTerminal.hom_ext
        ((CGWH.point.{u, v} ◁ (toCompactOpen X).right) ≫
          CGWH.point_isTerminal.from (CGWH.point ⊗ K.right))
        (CGWH.point_isTerminal.from
          (CGWH.point ⊗ (PointedCGWH.loop.obj X).right)))
  have hqDHom : qD ≫ eC.hom = diskToSphere.{u, v} := by
    rw [← hDiskCofiber, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  let eCRight : C0.right ≅ PointedCGWH.sphereOne.{u, v}.right :=
    (Under.forget CGWH.point).mapIso eC
  have heCRight : eCRight.hom = eC.hom.right := rfl
  have hqDRight : qD.right ≫ eCRight.hom = diskToSphere.{u, v}.right := by
    rw [heCRight]
    simpa only [Under.comp_right] using congrArg Under.Hom.right hqDHom
  let hTRight : IsTerminal T.right := by
    exact (terminalIsTerminal : IsTerminal T).isTerminalObj
      (Under.forget CGWH.point)
  let eT : CGWH.point.{u, v} ≅ T.right :=
    CGWH.point_isTerminal.uniqueUpToIso hTRight
  have heTHom : eT.hom = T.hom := hTRight.hom_ext _ _
  have hqTRight : qT.right ≫ eCRight.hom =
      eT.inv ≫ PointedCGWH.sphereOne.{u, v}.hom := by
    apply (cancel_epi eT.hom).1
    calc
      eT.hom ≫ (qT.right ≫ eCRight.hom) =
          T.hom ≫ (qT.right ≫ eC.hom.right) := by
        rw [heTHom, heCRight]
      _ = PointedCGWH.sphereOne.hom := by
        simpa only [Under.comp_right] using Under.w (qT ≫ eC.hom)
      _ = eT.hom ≫
          (eT.inv ≫ PointedCGWH.sphereOne.hom) := by simp
  let _ : (tensorRight (PointedCGWH.loop.obj X).right).IsLeftAdjoint :=
    inferInstance
  let hTensorN := hCarrier.map
    (tensorRight (PointedCGWH.loop.obj X).right)
  have hTensorEval :
      ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ (toCompactOpen X).right) ≫
          sphereEval =
        qN ≫ evN.right := by
    apply (cancel_epi (eCRight.hom ▷ (PointedCGWH.loop.obj X).right)).1
    apply hTensorN.hom_ext
    · change (qD.right ▷ (PointedCGWH.loop.obj X).right) ≫
          (eCRight.hom ▷ (PointedCGWH.loop.obj X).right) ≫
            ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ
              (toCompactOpen X).right) ≫ sphereEval =
        (qD.right ▷ (PointedCGWH.loop.obj X).right) ≫
          (eCRight.hom ▷ (PointedCGWH.loop.obj X).right) ≫ qN ≫ evN.right
      slice_lhs 1 2 =>
        rw [← MonoidalCategory.comp_whiskerRight, hqDRight]
      slice_rhs 1 2 =>
        rw [← MonoidalCategory.comp_whiskerRight, hqDRight]
      exact hDiskTensorEval
    · change (qT.right ▷ (PointedCGWH.loop.obj X).right) ≫
          (eCRight.hom ▷ (PointedCGWH.loop.obj X).right) ≫
            ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ
              (toCompactOpen X).right) ≫ sphereEval =
        (qT.right ▷ (PointedCGWH.loop.obj X).right) ≫
          (eCRight.hom ▷ (PointedCGWH.loop.obj X).right) ≫ qN ≫ evN.right
      slice_lhs 1 2 =>
        rw [← MonoidalCategory.comp_whiskerRight, hqTRight]
      slice_rhs 1 2 =>
        rw [← MonoidalCategory.comp_whiskerRight, hqTRight]
      apply (cancel_epi (eT.hom ▷ (PointedCGWH.loop.obj X).right)).1
      slice_lhs 1 2 =>
        rw [← MonoidalCategory.comp_whiskerRight, ← Category.assoc,
          Iso.hom_inv_id, Category.id_comp]
      slice_rhs 1 2 =>
        rw [← MonoidalCategory.comp_whiskerRight, ← Category.assoc,
          Iso.hom_inv_id, Category.id_comp]
      exact hPointTensorEval
  have hEvalSmashTensor : q ≫ evalSmash.right = sphereEval := by
    change p.2.1.inl ≫
      PushoutCocone.IsColimit.desc p.2.2 sphereEval X.hom hWedge = sphereEval
    exact PushoutCocone.IsColimit.inl_desc p.2.2 _ _ _
  have hEvalSmash :
      (PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (toCompactOpen X) ≫ evalSmash = evN := by
    apply Under.UnderMorphism.ext
    let hPN : IsPushout pN.1.right
        (CGWH.point_isTerminal.from
          (((CategoryTheory.Pointed.wedge CGWH.point).obj
            PointedCGWH.sphereOne).obj (PointedCGWH.loop.obj X)).right)
        pN.2.1.inl pN.2.1.inr :=
      IsPushout.of_isColimit_cocone pN.2.2
    apply hPN.hom_ext
    · simp only [Under.comp_right]
      change qN ≫
          ((((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
            (toCompactOpen X)).right) ≫ evalSmash.right) =
        qN ≫ evN.right
      rw [← Category.assoc, hSmashTo, Category.assoc,
        hEvalSmashTensor, hTensorEval]
    · change (((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
          (PointedCGWH.loop.obj X)).hom) ≫
            (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
              (toCompactOpen X)).right ≫ evalSmash.right) =
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
          (PointedCGWH.loop.obj X)).hom) ≫ evN.right
      simpa only [Under.comp_right] using
        (Under.w ((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (toCompactOpen X) ≫ evalSmash)).trans (Under.w evN).symm
  have hUncurryN :
      (PointedCGWH.smash.obj PointedCGWH.sphereOne).map invMap ≫ evN =
        evalSmash := by
    exact hUncurry
  have hSecond : (toCompactOpen X) ≫ invMap =
      𝟙 (PointedCGWH.loop.obj X) := by
    apply (PointedCGWH.suspensionLoopAdjunction.homEquiv
      (PointedCGWH.loop.obj X) X).symm.injective
    rw [PointedCGWH.suspensionLoopAdjunction.homEquiv_counit,
      PointedCGWH.suspensionLoopAdjunction.homEquiv_counit]
    rw [Functor.map_comp]
    change (PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (toCompactOpen X) ≫
          (PointedCGWH.smash.obj PointedCGWH.sphereOne).map invMap ≫ evN =
      (PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (𝟙 (PointedCGWH.loop.obj X)) ≫ evN
    rw [hUncurryN, hEvalSmash]
    calc
      evN = 𝟙 _ ≫ evN := (Category.id_comp _).symm
      _ = (PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (𝟙 (PointedCGWH.loop.obj X)) ≫ evN := by
        exact congrArg (fun k => k ≫ evN)
          ((PointedCGWH.smash.obj PointedCGWH.sphereOne).map_id
            (PointedCGWH.loop.obj X)).symm
  refine ⟨invMap, ?_, hSecond⟩
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro gamma
  change (toCompactOpen X).right (invMap.right gamma) = gamma
  rw [hTo]
  apply Path.ext
  funext t
  rw [(loopLandingRaw X).2.2]
  let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
    ConcreteCategory.ofHom (ContinuousMap.const _
      (sphereOneParam.{u, v} (TopCat.I.homeomorph.symm t)))
  let b : CGWH.point.{u, v} ⟶ K.right :=
    ConcreteCategory.ofHom (ContinuousMap.const _ gamma)
  let bL : CGWH.point.{u, v} ⟶
      ((PointedCGWH.power PointedCGWH.sphereOne).obj X).right :=
    ConcreteCategory.ofHom (ContinuousMap.const _ (invMapCore.right gamma))
  let z : (PointedCGWH.sphereOne.{u, v}.right ⊗ K.right : CGWH.{u, v}) :=
    CartesianMonoidalCategory.lift a b PUnit.unit
  have hb : b ≫ invMapCore.right = bL := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  have hz : ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ invMapCore.right) z =
      CartesianMonoidalCategory.lift a bL PUnit.unit := by
    let pairK := CartesianMonoidalCategory.lift a b
    let pairL := CartesianMonoidalCategory.lift a bL
    have hPair : pairK ≫
        ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ invMapCore.right) = pairL := by
      dsimp only [pairK, pairL]
      rw [CartesianMonoidalCategory.lift_map, hb]
      simp
    exact ConcreteCategory.congr_hom hPair PUnit.unit
  change ((PointedCGWH.basedEval PointedCGWH.sphereOne).app X).right
      (qL (CartesianMonoidalCategory.lift a bL PUnit.unit)) =
    (show LoopSpace X.right (pointValue X) from gamma) t
  rw [← hz]
  have hMapPoint :
      qL (((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ invMapCore.right) z) =
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          invMapCore).right (q z)) := by
    have h := ConcreteCategory.congr_hom hSmashMap z
    change (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
        invMapCore).right (q z)) =
      qL (((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ invMapCore.right) z) at h
    exact h.symm
  rw [hMapPoint]
  have hUncurryPoint :
      ((PointedCGWH.basedEval PointedCGWH.sphereOne).app X).right
          (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
            invMapCore).right (q z)) =
        evalSmash.right (q z) := by
    have h := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right hUncurry) (q z)
    change ((PointedCGWH.basedEval PointedCGWH.sphereOne).app X).right
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          invMapCore).right (q z)) =
      evalSmash.right (q z) at h
    exact h
  rw [hUncurryPoint]
  have hDesc := PushoutCocone.IsColimit.inl_desc p.2.2
    sphereEval X.hom hWedge
  have hDescPoint : evalSmash.right (q z) = sphereEval z := by
    have h := ConcreteCategory.congr_hom hDesc z
    change evalSmash.right (q z) = sphereEval z at h
    exact h
  change evalSmash.right (q z) =
    (show LoopSpace X.right (pointValue X) from gamma) t
  have hEval : sphereEval z =
      (show LoopSpace X.right (pointValue X) from
        CompactlyGenerated.adj.{u, v}.counit.app
          (TopCat.of (LoopSpace X.right (pointValue X))) gamma) t := by
    simpa only [z, a, b] using hSphereEval gamma t
  have hCounit := CompactlyGenerated.adjCounit_apply.{v, u}
    (TopCat.of (LoopSpace X.right (pointValue X))) gamma
  have hCounitAt := congrArg
    (fun eta : LoopSpace X.right (pointValue X) => eta t) hCounit
  exact hDescPoint.trans (hEval.trans hCounitAt)

private theorem fromCompactOpen_toCompactOpen (X : PointedCGWH.{u, v}) :
    (fromCompactOpen X).1 ≫ toCompactOpen X =
      𝟙 (compactOpenLoopCoreflection.obj X) :=
  (fromCompactOpen X).2.1

private theorem toCompactOpen_fromCompactOpen (X : PointedCGWH.{u, v}) :
    toCompactOpen X ≫ (fromCompactOpen X).1 =
      𝟙 (PointedCGWH.loop.obj X) :=
  (fromCompactOpen X).2.2

private theorem toCompactOpen_naturality {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) :
    PointedCGWH.loop.map f ≫ toCompactOpen Y =
      toCompactOpen X ≫ compactOpenLoopCoreflection.map f := by
  have hToAny (Z : PointedCGWH.{u, v})
      (eta : (PointedCGWH.loop.obj Z).right) :
      (toCompactOpen Z).right eta = (loopLandingRaw Z).1 eta := by
    let Raw : TopCat.{v} := TopCat.of (LoopSpace Z.right (pointValue Z))
    let A : CompactlyGenerated.{u, v} :=
      CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj Z).right
    let mC : A ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw :=
      CompactlyGenerated.adj.{u, v}.homEquiv A Raw (loopLandingRaw Z).1
    let m : (PointedCGWH.loop.obj Z).right ⟶ compactOpenLoopCarrier Z :=
      CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage (by
        dsimp only [compactOpenLoopCarrier]
        exact mC)
    have hm :=
      (CompactlyGenerated.adj.{u, v}.homEquiv A Raw).symm_apply_apply
        (loopLandingRaw Z).1
    rw [CompactlyGenerated.adj.{u, v}.homEquiv_counit] at hm
    have hmEta := ConcreteCategory.congr_hom hm eta
    have hmEta' := hmEta
    have hMap := ConcreteCategory.congr_hom
      (CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage
        (X := (PointedCGWH.loop.obj Z).right)
        (Y := compactOpenLoopCarrier Z) (by
          change A ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw
          exact mC)) eta
    change m eta = (loopLandingRaw Z).1 eta
    change m eta = mC eta at hMap
    exact hMap.trans hmEta'
  have hCoreMap
      (gamma : (compactOpenLoopCoreflection.obj X).right) :
      (compactOpenLoopCoreflection.map f).right gamma =
        strictLoopMap f gamma := by
    let gC : CGWH.cgwhToCompactlyGenerated.obj
          (compactOpenLoopCarrier X) ⟶
        CGWH.cgwhToCompactlyGenerated.obj (compactOpenLoopCarrier Y) := by
      dsimp only [compactOpenLoopCarrier]
      exact TopCat.toCompactlyGenerated.{u, v}.map
        (TopCat.ofHom (strictLoopMap f))
    let m : compactOpenLoopCarrier X ⟶ compactOpenLoopCarrier Y :=
      CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage gC
    have hActual : (compactOpenLoopCoreflection.map f).right = m := rfl
    rw [hActual]
    have hMap := ConcreteCategory.congr_hom
      (CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage gC) gamma
    change m gamma = strictLoopMap f gamma at hMap
    exact hMap
  let pX := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
      (PointedCGWH.loop.obj X)
  let pY := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
      (PointedCGWH.loop.obj Y)
  let qX : PointedCGWH.sphereOne.{u, v}.right ⊗
      (PointedCGWH.loop.obj X).right ⟶
        ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
          (PointedCGWH.loop.obj X)).right := pX.2.1.inl
  let qY : PointedCGWH.sphereOne.{u, v}.right ⊗
      (PointedCGWH.loop.obj Y).right ⟶
        ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
          (PointedCGWH.loop.obj Y)).right := pY.2.1.inl
  let evX : (PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
      (PointedCGWH.loop.obj X) ⟶ X :=
    (PointedCGWH.basedEval PointedCGWH.sphereOne).app X
  let evY : (PointedCGWH.smash.obj PointedCGWH.sphereOne).obj
      (PointedCGWH.loop.obj Y) ⟶ Y :=
    (PointedCGWH.basedEval PointedCGWH.sphereOne).app Y
  have hQuotient : qX ≫
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (PointedCGWH.loop.map f)).right) =
      ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ
        (PointedCGWH.loop.map f).right) ≫ qY := by
    change (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
          (PointedCGWH.loop.obj X)).2.1.inl ≫
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (PointedCGWH.loop.map f)).right) =
      ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ
        (PointedCGWH.loop.map f).right) ≫
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
            (PointedCGWH.loop.obj Y)).2.1.inl
    unfold PointedCGWH.smash CategoryTheory.Pointed.smash
    exact PushoutCocone.IsColimit.inl_desc
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne
          (PointedCGWH.loop.obj X)).2.2 _ _ _
  have hEval :
      (PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (PointedCGWH.loop.map f) ≫ evY = evX ≫ f := by
    have h := (PointedCGWH.basedEval PointedCGWH.sphereOne).naturality f
    change (PointedCGWH.smash.obj PointedCGWH.sphereOne).map
        (PointedCGWH.loop.map f) ≫ evY = evX ≫ f at h
    exact h
  have hLanding (gamma : (PointedCGWH.loop.obj X).right)
      (t : unitInterval) :
      (loopLandingRaw Y).1 ((PointedCGWH.loop.map f).right gamma) t =
        f.right ((loopLandingRaw X).1 gamma t) := by
    rw [(loopLandingRaw Y).2.2, (loopLandingRaw X).2.2]
    let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
      ConcreteCategory.ofHom (ContinuousMap.const _
        (sphereOneParam.{u, v} (TopCat.I.homeomorph.{v}.symm t)))
    let bX : CGWH.point.{u, v} ⟶ (PointedCGWH.loop.obj X).right :=
      ConcreteCategory.ofHom (ContinuousMap.const _ gamma)
    let bY : CGWH.point.{u, v} ⟶ (PointedCGWH.loop.obj Y).right :=
      ConcreteCategory.ofHom (ContinuousMap.const _
        ((PointedCGWH.loop.map f).right gamma))
    let z : (PointedCGWH.sphereOne.{u, v}.right ⊗
        (PointedCGWH.loop.obj X).right : CGWH.{u, v}) :=
      CartesianMonoidalCategory.lift a bX PUnit.unit
    have hb : bX ≫ (PointedCGWH.loop.map f).right = bY := by
      apply ConcreteCategory.hom_ext
      intro p
      rfl
    have hz : ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ
          (PointedCGWH.loop.map f).right) z =
        CartesianMonoidalCategory.lift a bY PUnit.unit := by
      let pairX := CartesianMonoidalCategory.lift a bX
      let pairY := CartesianMonoidalCategory.lift a bY
      have hPair : pairX ≫
          ((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ
            (PointedCGWH.loop.map f).right) = pairY := by
        dsimp only [pairX, pairY]
        rw [CartesianMonoidalCategory.lift_map, hb]
        simp
      exact ConcreteCategory.congr_hom hPair PUnit.unit
    change evY.right (qY (CartesianMonoidalCategory.lift a bY PUnit.unit)) =
      f.right (evX.right (qX z))
    rw [← hz]
    have hQuotientPoint :
        qY (((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ
          (PointedCGWH.loop.map f).right) z) =
          (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
            (PointedCGWH.loop.map f)).right (qX z)) := by
      have h := ConcreteCategory.congr_hom hQuotient z
      change (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
          (PointedCGWH.loop.map f)).right (qX z)) =
        qY (((𝟙 PointedCGWH.sphereOne.right) ⊗ₘ
          (PointedCGWH.loop.map f).right) z) at h
      exact h.symm
    rw [hQuotientPoint]
    have hEvalPoint :
        evY.right
            (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
              (PointedCGWH.loop.map f)).right (qX z)) =
          f.right (evX.right (qX z)) := by
      have h := ConcreteCategory.congr_hom
        (congrArg Under.Hom.right hEval) (qX z)
      change evY.right
          (((PointedCGWH.smash.obj PointedCGWH.sphereOne).map
            (PointedCGWH.loop.map f)).right (qX z)) =
        f.right (evX.right (qX z)) at h
      exact h
    exact hEvalPoint
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro gamma
  change (toCompactOpen Y).right
      ((PointedCGWH.loop.map f).right gamma) =
    (compactOpenLoopCoreflection.map f).right
      ((toCompactOpen X).right gamma)
  rw [hToAny, hCoreMap]
  apply Path.ext
  funext t
  have hToAt := congrArg
    (fun eta : LoopSpace X.right (pointValue X) => eta t)
    (hToAny X gamma)
  have hStrict := strictLoopMap_apply f ((toCompactOpen X).right gamma) t
  exact (hLanding gamma t).trans
    ((congrArg f.right hToAt.symm).trans hStrict.symm)

/-- The native based internal Hom from the one-sphere is the compactly
generated compact-open loop space. -/
@[no_expose]
noncomputable def loopIsoCompactOpenCoreflection :
    PointedCGWH.loop.{u, v} ≅ compactOpenLoopCoreflection.{u, v} :=
  NatIso.ofComponents (fun X =>
    { hom := toCompactOpen X
      inv := (fromCompactOpen X).1
      hom_inv_id := toCompactOpen_fromCompactOpen X
      inv_hom_id := fromCompactOpen_toCompactOpen X })
    (fun f => toCompactOpen_naturality f)

/-- The underlying native loop lands continuously in the raw compact-open
topological loop space. -/
@[no_expose]
noncomputable def loopLanding (X : PointedCGWH.{u, v}) :
    TopCat.of ((PointedCGWH.loop.obj X).right) ⟶
      TopCat.of (LoopSpace X.right (X.hom (show CGWH.point.{u, v} from PUnit.unit))) :=
  CGWH.cgwhToTop.map
      (loopIsoCompactOpenCoreflection.hom.app X).right ≫
    CompactlyGenerated.adj.{u, v}.counit.app
      (TopCat.of (LoopSpace X.right (pointValue X)))

/-- Native-loop landing commutes with strict pointed postcomposition. -/
@[reassoc]
theorem loopLanding_naturality {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CGWH.cgwhToTop.map (PointedCGWH.loop.map f).right ≫ loopLanding Y =
      loopLanding X ≫ TopCat.ofHom (strictLoopMap f) := by
  have hCoreMap
      (gamma : (compactOpenLoopCoreflection.obj X).right) :
      (compactOpenLoopCoreflection.map f).right gamma =
        strictLoopMap f gamma := by
    let gC : CGWH.cgwhToCompactlyGenerated.obj
          (compactOpenLoopCarrier X) ⟶
        CGWH.cgwhToCompactlyGenerated.obj (compactOpenLoopCarrier Y) := by
      dsimp only [compactOpenLoopCarrier]
      exact TopCat.toCompactlyGenerated.{u, v}.map
        (TopCat.ofHom (strictLoopMap f))
    let m : compactOpenLoopCarrier X ⟶ compactOpenLoopCarrier Y :=
      CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage gC
    have hActual : (compactOpenLoopCoreflection.map f).right = m := rfl
    rw [hActual]
    have hMap := ConcreteCategory.congr_hom
      (CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage gC) gamma
    change m gamma = strictLoopMap f gamma at hMap
    exact hMap
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro gamma
  let eta : (PointedCGWH.loop.obj X).right := gamma
  let a : (compactOpenLoopCoreflection.obj Y).right :=
    (loopIsoCompactOpenCoreflection.hom.app Y).right
      ((PointedCGWH.loop.map f).right eta)
  let b : (compactOpenLoopCoreflection.obj X).right :=
    (loopIsoCompactOpenCoreflection.hom.app X).right eta
  change CompactlyGenerated.adj.{u, v}.counit.app
      (TopCat.of (LoopSpace Y.right (pointValue Y))) a =
    strictLoopMap f
      (CompactlyGenerated.adj.{u, v}.counit.app
        (TopCat.of (LoopSpace X.right (pointValue X))) b)
  have hCounitY := CompactlyGenerated.adjCounit_apply.{v, u}
    (TopCat.of (LoopSpace Y.right (pointValue Y))) a
  have hCounitX := CompactlyGenerated.adjCounit_apply.{v, u}
    (TopCat.of (LoopSpace X.right (pointValue X))) b
  have hNat := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right
      (loopIsoCompactOpenCoreflection.hom.naturality f)) eta
  change a = (compactOpenLoopCoreflection.map f).right b at hNat
  exact hCounitY.trans
    (hNat.trans ((hCoreMap b).trans
      (congrArg (strictLoopMap f) hCounitX.symm)))

/-- The native loop point lands at the reflexive compact-open loop. -/
@[simp]
theorem loopLanding_basepoint (X : PointedCGWH.{u, v}) :
    loopLanding X ((PointedCGWH.loop.obj X).hom PUnit.unit) =
      Path.refl (X.hom (show CGWH.point.{u, v} from PUnit.unit)) := by
  change CompactlyGenerated.adj.{u, v}.counit.app
      (TopCat.of (LoopSpace X.right (pointValue X)))
        ((loopIsoCompactOpenCoreflection.hom.app X).right
          ((PointedCGWH.loop.obj X).hom PUnit.unit)) =
    Path.refl (pointValue X)
  have hCounit := CompactlyGenerated.adjCounit_apply.{v, u}
    (TopCat.of (LoopSpace X.right (pointValue X)))
      ((loopIsoCompactOpenCoreflection.hom.app X).right
        ((PointedCGWH.loop.obj X).hom PUnit.unit))
  have h := ConcreteCategory.congr_hom
    (Under.w (loopIsoCompactOpenCoreflection.hom.app X)) PUnit.unit
  change (loopIsoCompactOpenCoreflection.hom.app X).right
      ((PointedCGWH.loop.obj X).hom PUnit.unit) =
    Path.refl (pointValue X) at h
  exact hCounit.trans h

/-- Evaluation of a native loop at a point of the lifted unit interval. -/
noncomputable def loopEvalAt (X : PointedCGWH.{u, v})
    (t : TopCat.I.{v}) : PointedCGWH.loop.obj X ⟶ X := by
  let L := PointedCGWH.loop.obj X
  let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
    ConcreteCategory.ofHom
      (ContinuousMap.const _ (sphereOneParam.{u, v} t))
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
      (Limits.prod.snd : PointedCGWH.sphereOne.right ⨯ L.right ⟶ L.right) =
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
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal PointedCGWH.sphereOne L
  let q : PointedCGWH.sphereOne.{u, v}.right ⊗ L.right ⟶
      ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).right :=
    p.2.1.inl
  let ev : (PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L ⟶ X :=
    (PointedCGWH.basedEval PointedCGWH.sphereOne).app X
  let carrier : L.right ⟶ X.right := pairTensor ≫ q ≫ ev.right
  let leftRaw : PointedCGWH.sphereOne.right ⟶
      PointedCGWH.sphereOne.right ⊗ L.right :=
    CartesianMonoidalCategory.lift (𝟙 _)
      (CGWH.point_isTerminal.from _ ≫ L.hom)
  have hAtBase : L.hom ≫ pairTensor = a ≫ leftRaw := by
    rw [hPairTensor]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
      dsimp only [constParam, leftRaw]
      rw [CartesianMonoidalCategory.lift_fst, Category.comp_id]
      have hTerm : L.hom ≫ CGWH.point_isTerminal.from L.right =
          𝟙 CGWH.point.{u, v} :=
        CGWH.point_isTerminal.hom_ext _ _
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun k : CGWH.point ⟶ CGWH.point => k ≫ a) hTerm
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
      dsimp only [leftRaw]
      rw [CartesianMonoidalCategory.lift_snd, Category.comp_id]
      have hTerm : a ≫ CGWH.point_isTerminal.from
          PointedCGWH.sphereOne.right = 𝟙 CGWH.point.{u, v} :=
        CGWH.point_isTerminal.hom_ext _ _
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun k : CGWH.point ⟶ CGWH.point => k ≫ L.hom) hTerm.symm
  let wedgeInl : PointedCGWH.sphereOne.{u, v} ⟶
      ((CategoryTheory.Pointed.wedge CGWH.point).obj
        PointedCGWH.sphereOne).obj L :=
    Under.homMk (pushout.inl PointedCGWH.sphereOne.hom L.hom) rfl
  have hpInl : wedgeInl.right ≫ p.1.right = leftRaw := by
    change pushout.inl PointedCGWH.sphereOne.hom L.hom ≫
      pushout.desc _ _ _ = _
    rw [pushout.inl_desc]
    rfl
  have hLeftPoint : leftRaw ≫ q =
      CGWH.point_isTerminal.from PointedCGWH.sphereOne.right ≫
        (((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).hom) := by
    rw [← hpInl, Category.assoc]
    change wedgeInl.right ≫ p.1.right ≫ p.2.1.inl = _
    rw [p.2.1.condition, ← Category.assoc]
    exact congrArg
      (fun k : PointedCGWH.sphereOne.right ⟶ CGWH.point =>
        k ≫ ((PointedCGWH.smash.obj PointedCGWH.sphereOne).obj L).hom)
      (CGWH.point_isTerminal.hom_ext _ _)
  refine Under.homMk carrier ?_
  change L.hom ≫ carrier = X.hom
  dsimp only [carrier]
  rw [← Category.assoc, hAtBase, Category.assoc]
  slice_lhs 2 3 => rw [hLeftPoint]
  slice_lhs 3 4 => rw [Under.w ev]
  have hTerm : a ≫ CGWH.point_isTerminal.from
      PointedCGWH.sphereOne.right = 𝟙 CGWH.point.{u, v} :=
    CGWH.point_isTerminal.hom_ext _ _
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun k : CGWH.point ⟶ CGWH.point => k ≫ X.hom) hTerm

/-- Native evaluation agrees pointwise with evaluation of the landed
compact-open loop. -/
@[simp]
theorem loopLanding_evaluation (X : PointedCGWH.{u, v})
    (gamma : (PointedCGWH.loop.obj X).right) (t : TopCat.I.{v}) :
    (loopLanding X gamma) (TopCat.I.homeomorph t) =
      (loopEvalAt X t).right gamma := by
  let L := PointedCGWH.loop.obj X
  let a : CGWH.point.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
    ConcreteCategory.ofHom
      (ContinuousMap.const _ (sphereOneParam.{u, v} t))
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
      (Limits.prod.snd : PointedCGWH.sphereOne.right ⨯ L.right ⟶ L.right) =
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
  have hEvalAt : (loopEvalAt X t).right gamma =
      ev.right (q (CartesianMonoidalCategory.lift a b PUnit.unit)) := by
    change ev.right (q (pairTensor gamma)) = _
    rw [hPairTensor, hPairPoint]
  have hTo : (toCompactOpen X).right gamma = (loopLandingRaw X).1 gamma := by
    let Raw : TopCat.{v} := TopCat.of (LoopSpace X.right (pointValue X))
    let A : CompactlyGenerated.{u, v} :=
      CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj X).right
    let mC : A ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw :=
      CompactlyGenerated.adj.{u, v}.homEquiv A Raw (loopLandingRaw X).1
    let m : (PointedCGWH.loop.obj X).right ⟶ compactOpenLoopCarrier X :=
      CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage (by
        dsimp only [compactOpenLoopCarrier]
        exact mC)
    have hm :=
      (CompactlyGenerated.adj.{u, v}.homEquiv A Raw).symm_apply_apply
        (loopLandingRaw X).1
    rw [CompactlyGenerated.adj.{u, v}.homEquiv_counit] at hm
    have hmGamma := ConcreteCategory.congr_hom hm gamma
    have hmGamma' := hmGamma
    have hMap := ConcreteCategory.congr_hom
      (CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage
        (X := (PointedCGWH.loop.obj X).right)
        (Y := compactOpenLoopCarrier X) (by
          change A ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw
          exact mC)) gamma
    change m gamma = (loopLandingRaw X).1 gamma
    change m gamma = mC gamma at hMap
    exact hMap.trans hmGamma'
  let r : unitInterval := TopCat.I.homeomorph.{v} t
  have hRaw := (loopLandingRaw X).2.2 gamma r
  have ht : TopCat.I.homeomorph.{v}.symm r = t := by
    dsimp only [r]
    exact TopCat.I.homeomorph.{v}.symm_apply_apply t
  rw [ht] at hRaw
  change (loopLandingRaw X).1 gamma r =
    ev.right (q (CartesianMonoidalCategory.lift a b PUnit.unit)) at hRaw
  let eta : (compactOpenLoopCoreflection.obj X).right :=
    (loopIsoCompactOpenCoreflection.hom.app X).right gamma
  change (show LoopSpace X.right (pointValue X) from
      CompactlyGenerated.adj.{u, v}.counit.app
        (TopCat.of (LoopSpace X.right (pointValue X))) eta) r =
    (loopEvalAt X t).right gamma
  have hCounit := CompactlyGenerated.adjCounit_apply.{v, u}
    (TopCat.of (LoopSpace X.right (pointValue X))) eta
  have hCounitAt := congrArg
    (fun delta : LoopSpace X.right (pointValue X) => delta r) hCounit
  have hToAt := congrArg
    (fun delta : LoopSpace X.right (pointValue X) => delta r) hTo
  exact hCounitAt.trans
    (hToAt.trans (hRaw.trans hEvalAt.symm))

/-- The strict native loop functor preserves the selected binary product. -/
noncomputable def loopProdIso (X Y : PointedCGWH.{u, v}) :
    PointedCGWH.loop.obj (X ⨯ Y) ≅
      PointedCGWH.loop.obj X ⨯ PointedCGWH.loop.obj Y := by
  let _ :=
    PointedCGWH.suspensionLoopAdjunction.{u, v}.rightAdjoint_preservesLimits
  exact Limits.PreservesLimitPair.iso PointedCGWH.loop X Y

/-- The loop/product comparison has the expected first projection. -/
@[reassoc]
theorem loopProdIso_hom_fst (X Y : PointedCGWH.{u, v}) :
    (loopProdIso X Y).hom ≫ Limits.prod.fst =
      PointedCGWH.loop.map
        (Limits.prod.fst : X ⨯ Y ⟶ X) := by
  unfold loopProdIso
  simp only [Limits.PreservesLimitPair.iso_hom,
    Limits.prodComparison_fst]

/-- The loop/product comparison has the expected second projection. -/
@[reassoc]
theorem loopProdIso_hom_snd (X Y : PointedCGWH.{u, v}) :
    (loopProdIso X Y).hom ≫ Limits.prod.snd =
      PointedCGWH.loop.map
        (Limits.prod.snd : X ⨯ Y ⟶ Y) := by
  unfold loopProdIso
  simp only [Limits.PreservesLimitPair.iso_hom,
    Limits.prodComparison_snd]

/-- The loop/product comparison intertwines the selected cartesian
symmetries. -/
theorem loopProdIso_symmetry (X Y : PointedCGWH.{u, v}) :
    PointedCGWH.loop.map (Limits.prod.braiding X Y).hom ≫
        (loopProdIso Y X).hom =
      (loopProdIso X Y).hom ≫
        (Limits.prod.braiding
          (PointedCGWH.loop.obj X) (PointedCGWH.loop.obj Y)).hom := by
  unfold loopProdIso
  simp only [Limits.PreservesLimitPair.iso_hom]
  exact Limits.map_braiding_hom_comp_prodComparison
    PointedCGWH.loop (A := Y) (B := X)

end PointedCGWH

namespace PointedCGWH

/-- The actual compact-open loop coreflection retains its original compact-generation object. -/
theorem compactOpenLoopCoreflection_toCompactlyGenerated (X : PointedCGWH.{u, v}) :
    CGWH.cgwhToCompactlyGenerated.obj ((compactOpenLoopCoreflection.obj X).right) =
      TopCat.toCompactlyGenerated.{u, v}.obj
        (TopCat.of (LoopSpace X.right (X.hom (show CGWH.point.{u, v} from PUnit.unit)))) := by
  rfl

/-- The entire original native-loop landing is its original coreflection chart and counit. -/
theorem loopLanding_compactOpenCoreflection_eq (X : PointedCGWH.{u, v}) :
    loopLanding X =
      CGWH.cgwhToTop.map (loopIsoCompactOpenCoreflection.hom.app X).right ≫
        eqToHom (congrArg CompactlyGenerated.compactlyGeneratedToTop.obj
          (compactOpenLoopCoreflection_toCompactlyGenerated X)) ≫
          CompactlyGenerated.adj.{u, v}.counit.app
            (TopCat.of (LoopSpace X.right (X.hom (show CGWH.point.{u, v} from PUnit.unit)))) := by
  rfl

end PointedCGWH
