/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.MixedOriginalQRealizationTransport
public import MathlibExt.KTheory.Ring.StableGeneralLinear.OriginalUnliftedQEvaluatorTransport
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv

/-!
# Actual mixed original Q scalar loop squares

The original scalar/lift natural Isos and canonical Q zero comparisons derive
whole mixed loop homotopies internally. Original up/down functors, realization
maps, selected zeros and root paths are retained. The original retuned Q maps
are attached through their existing full retuning and inverse families.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uD vD uE vE uX uY uA vA uB vB

namespace AlgebraicKTheory.QuillenMixedUniverseTransport

private theorem originalPathHomotopicOfEq
    {X : Type uX} [TopologicalSpace X] {a b : X} {p q : Path a b}
    (h : p = q) : p.Homotopic q := by
  cases h
  exact Path.Homotopic.refl p

private theorem originalWeakPointedExt
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {f g : ContinuousMap.WeaklyPointed x y}
    (h : f.hom = g.hom) (hp : HEq f.rootPath g.rootPath) : f = g := by
  cases f
  cases g
  cases h
  cases hp
  rfl

private theorem originalPathHEqOfValues
    {X : Type uX} [TopologicalSpace X] {a b c d : X} {p : Path a b} {q : Path c d}
    (h : ∀ t, p t = q t) : HEq p q := by
  have hs : a = c := p.source.symm.trans ((h 0).trans q.source)
  have ht : b = d := p.target.symm.trans ((h 1).trans q.target)
  cases hs
  cases ht
  apply heq_of_eq
  apply Path.ext
  funext t
  exact h t

private def originalLoopMapOfEqualMaps
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : ContinuousMap.WeaklyPointed x y) (h : f.hom = g.hom)
    (hp : f.rootPath.Homotopic
      (g.rootPath.cast (congrArg (fun m : C(X, Y) => m x) h) rfl)) :
    ContinuousMap.Homotopy f.loopMap g.loopMap := by
  cases f with
  | mk fm fp =>
    cases g with
    | mk gm gp =>
      dsimp only at h hp
      cases h
      exact ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy fm hp.some

private abbrev originalObjectVertex
    (C : Type uC) [Category.{vC} C] (x : C) : SSet.toTop.obj (nerve C) :=
  SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ x)

private theorem originalNQBasepointEqOriginalZero
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    NQReal.basepoint C = OriginalQZeroComparison.zeroQVertex (C := C) := by
  let p := Path.refl (NQReal.basepoint C)
  let e := OriginalQuillenUnliftedTransport.originalNQLoopPointHomeomorph C
  have hValue : e p 0 = NQReal.basepoint C :=
    (OriginalQuillenUnliftedTransport.originalNQLoopPointHomeomorph_value C p 0).trans p.source
  exact hValue.symm.trans (e p).source

private theorem originalZeroEqNerveZero
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    OriginalQZeroComparison.zeroQVertex (C := C) = originalObjectVertex (QuillenQ C) (⟨0⟩) :=
  originalNQBasepointEqOriginalZero.symm.trans (NQReal.basepoint_eq_realizedVertex C)

private abbrev originalEdgePath
    {C : Type uC} [Category.{vC} C] {x y : C} (a : x ⟶ y) :
    Path (originalObjectVertex C x) (originalObjectVertex C y) :=
  TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk a))

private theorem originalEdgeIsoTriangle
    {C : Type uC} [Category.{vC} C] {x y z : C}
    (a : x ≅ y) (p : x ≅ z) (q : y ≅ z) (h : a ≪≫ q = p) :
    (originalEdgePath p.hom).Homotopic
      ((originalEdgePath a.hom).trans (originalEdgePath q.hom)) := by
  have hc : a.hom ≫ q.hom = p.hom := congrArg Iso.hom h
  have ht := (nerve.nonempty_compStruct_iff a.hom q.hom p.hom).2 hc
  exact SSet.realizedCompStructHomotopic ht.some

private def originalNerveWeakMap
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (x : C) (z : D) (p : F.obj x ≅ z) :
    ContinuousMap.WeaklyPointed (originalObjectVertex C x) (originalObjectVertex D z) where
  hom := CategoryTheory.realizedNerveFunctorMap F
  rootPath := (originalEdgePath p.hom).cast
    (CategoryTheory.realizedNerveFunctorMap_vertex F x) rfl

private def originalNerveWeakMapAtPoints
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (x : C) (z : D) (p : F.obj x ≅ z)
    (a : SSet.toTop.obj (nerve C)) (b : SSet.toTop.obj (nerve D))
    (ha : a = originalObjectVertex C x) (hb : b = originalObjectVertex D z) :
    ContinuousMap.WeaklyPointed a b where
  hom := CategoryTheory.realizedNerveFunctorMap F
  rootPath := (originalEdgePath p.hom).cast
    ((congrArg (CategoryTheory.realizedNerveFunctorMap F) ha).trans
      (CategoryTheory.realizedNerveFunctorMap_vertex F x)) hb

private structure OriginalRootedNerveFamily
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (f g : ContinuousMap.WeaklyPointed x y) where
  homotopy : ContinuousMap.Homotopy f.hom g.hom
  root : f.rootPath.Homotopic ((homotopy.evalAt x).trans g.rootPath)

private def originalNerveRootedNatIso
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F G : C ⥤ D) (alpha : F ≅ G) (x : C) (z : D)
    (p : F.obj x ≅ z) (q : G.obj x ≅ z) (h : alpha.app x ≪≫ q = p) :
    OriginalRootedNerveFamily (originalObjectVertex C x) (originalObjectVertex D z)
      (originalNerveWeakMap F x z p) (originalNerveWeakMap G x z q) where
  homotopy := CategoryTheory.realizedNerveFunctorMapHomotopy alpha.hom
  root := by
    let HF := CategoryTheory.realizedNerveFunctorMap_vertex F x
    let HG := CategoryTheory.realizedNerveFunctorMap_vertex G x
    let H := CategoryTheory.realizedNerveFunctorMapHomotopy alpha.hom
    have hTri := (originalEdgeIsoTriangle (alpha.app x) p q h).pathCast HF rfl
    rw [Path.cast_trans (originalEdgePath (alpha.app x).hom)
      (originalEdgePath q.hom) HF HG rfl] at hTri
    have hTrace := (CategoryTheory.realizedNerveFunctorMapHomotopy_vertex alpha.hom x).pathCast
      HF HG
    have hCast : (((H.evalAt (originalObjectVertex C x)).cast HF.symm HG.symm).cast HF HG) =
        H.evalAt (originalObjectVertex C x) := by
      apply Path.ext
      funext t
      rfl
    rw [hCast] at hTrace
    exact hTri.trans (hTrace.symm.hcomp
      (Path.Homotopic.refl ((originalEdgePath q.hom).cast HG rfl)))

private def originalNerveRootedNatIsoAtPoints
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F G : C ⥤ D) (alpha : F ≅ G) (x : C) (z : D)
    (p : F.obj x ≅ z) (q : G.obj x ≅ z) (h : alpha.app x ≪≫ q = p)
    (a : SSet.toTop.obj (nerve C)) (b : SSet.toTop.obj (nerve D))
    (ha : a = originalObjectVertex C x) (hb : b = originalObjectVertex D z) :
    OriginalRootedNerveFamily a b (originalNerveWeakMapAtPoints F x z p a b ha hb)
      (originalNerveWeakMapAtPoints G x z q a b ha hb) := by
  cases ha
  cases hb
  exact originalNerveRootedNatIso F G alpha x z p q h

private theorem originalMixedNerveMapComposition
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {E : Type uE} [Category.{vE} E] (F : A ⥤ B) (G : B ⥤ E) :
    CategoryTheory.realizedNerveFunctorMap (F ⋙ G) =
      (CategoryTheory.realizedNerveFunctorMap G).comp
        (CategoryTheory.realizedNerveFunctorMap F) := by
  rw [CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uA, vA, uE, vE, max uB vB}
      (F ⋙ G),
    CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uB, vB, uE, vE, max uA vA} G,
    CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uA, vA, uB, vB, max uE vE} F]
  apply ContinuousMap.ext
  intro x
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uB vB uE vE} A
  let HB := SSet.realizedNerveLiftHomeomorph.{uB, vB, max uA vA uB vB uE vE} B
  let HE := SSet.realizedNerveLiftHomeomorph.{uE, vE, max uA vA uB vB uE vE} E
  let LF :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vA, uA} A).inverse ⋙ F ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vB, uB} B).functor
  let LG :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vB, uB} B).inverse ⋙ G ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vE, uE} E).functor
  let LFG :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vA, uA} A).inverse ⋙ (F ⋙ G) ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vE, uE} E).functor
  let z := HA.symm x
  have hFunctor : LFG = LF ⋙ LG := by
    exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
      change LFG.map f = eqToHom (rfl : LFG.obj i = LFG.obj i) ≫ LFG.map f ≫
        eqToHom (rfl : LFG.obj j = LFG.obj j)
      exact CategoryTheory.eq_conj_eqToHom (LFG.map f))
  have hNerve : nerveMap LFG = nerveMap LF ≫ nerveMap LG :=
    (congrArg nerveMap hFunctor).trans (nerveMap_comp LF LG).symm
  have hTop : SSet.toTop.map (nerveMap LFG) =
      SSet.toTop.map (nerveMap LF) ≫ SSet.toTop.map (nerveMap LG) :=
    (SSet.toTop.congr_map hNerve).trans (SSet.toTop.map_comp _ _)
  have hStep : HE (SSet.toTop.map (nerveMap LFG) z) =
      HE (SSet.toTop.map (nerveMap LG) (SSet.toTop.map (nerveMap LF) z)) :=
    congrArg HE ((ConcreteCategory.congr_hom hTop z).trans (TopCat.comp_app _ _ z))
  change HE (SSet.toTop.map (nerveMap LFG) z) =
    HE (SSet.toTop.map (nerveMap LG)
      (HB.symm (HB (SSet.toTop.map (nerveMap LF) z))))
  exact hStep.trans
    ((congrArg (fun y => HE (SSet.toTop.map (nerveMap LG) y))
      (HB.symm_apply_apply (SSet.toTop.map (nerveMap LF) z))).symm)


private theorem originalEdgeIsoSourceTransportValue
    {C : Type uC} [Category.{vC} C] {x x' y : C} (h : x = x') (p : x' ≅ y)
    (t : unitInterval) :
    originalEdgePath (eqToIso h ≪≫ p).hom t = originalEdgePath p.hom t := by
  cases h
  simp only [eqToIso_refl, Iso.refl_trans]

private theorem originalNerveWeakCompositeRoot
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] (F : C ⥤ D) (G : D ⥤ E)
    (x : C) (y : D) (z : E) (p : F.obj x ≅ y) (q : G.obj y ≅ z) :
    (originalNerveWeakMap (F ⋙ G) x z (G.mapIso p ≪≫ q)).rootPath.Homotopic
      (((originalNerveWeakMap F x y p).comp (originalNerveWeakMap G y z q)).rootPath.cast
        (congrArg (fun m => m (originalObjectVertex C x))
          (originalMixedNerveMapComposition F G)) rfl) := by
  let WF := originalNerveWeakMap F x y p
  let WG := originalNerveWeakMap G y z q
  let MG := CategoryTheory.realizedNerveFunctorMap G
  let hs := CategoryTheory.realizedNerveFunctorMap_vertex (F ⋙ G) x
  let ht := CategoryTheory.realizedNerveFunctorMap_vertex G y
  let hMap := congrArg (fun m => m (originalObjectVertex C x))
    (originalMixedNerveMapComposition F G)
  have hEdge := (CategoryTheory.realizedNerveFunctorMap_edge_homotopic G p.hom).pathCast hs ht
  have hFirst :
      ((((originalEdgePath p.hom).map MG.continuous).cast
        (CategoryTheory.realizedNerveFunctorMap_vertex G (F.obj x)).symm ht.symm).cast hs ht) =
        ((WF.rootPath.map MG.continuous).cast hMap rfl) := by
    apply Path.ext
    funext t
    rfl
  have hEdgeValue : ((WF.rootPath.map MG.continuous).cast hMap rfl).Homotopic
      ((originalEdgePath (G.mapIso p).hom).cast hs ht) :=
    (originalPathHomotopicOfEq hFirst.symm).trans hEdge
  have h := hEdgeValue.hcomp (Path.Homotopic.refl WG.rootPath)
  have hTarget :
      ((originalEdgePath (G.mapIso p).hom).cast hs ht).trans WG.rootPath =
        ((originalEdgePath (G.mapIso p).hom).trans (originalEdgePath q.hom)).cast hs rfl := by
    apply Path.ext
    funext t
    rfl
  have hValue := h.trans (originalPathHomotopicOfEq hTarget)
  have hTri := (originalEdgeIsoTriangle (G.mapIso p) (G.mapIso p ≪≫ q) q rfl).pathCast hs rfl
  have hLeft :
      (((WF.comp WG).rootPath).cast hMap rfl) =
        ((WF.rootPath.map MG.continuous).cast hMap rfl).trans WG.rootPath := by
    apply Path.ext
    funext t
    rfl
  exact hTri.trans ((originalPathHomotopicOfEq hLeft).trans hValue).symm

private def originalNerveLoopMapComposition
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] (F : C ⥤ D) (G : D ⥤ E)
    (x : C) (y : D) (z : E) (p : F.obj x ≅ y) (q : G.obj y ≅ z) :
    ContinuousMap.Homotopy
      (originalNerveWeakMap (F ⋙ G) x z (G.mapIso p ≪≫ q)).loopMap
      ((originalNerveWeakMap G y z q).loopMap.comp (originalNerveWeakMap F x y p).loopMap) :=
  (originalLoopMapOfEqualMaps
    (originalNerveWeakMap (F ⋙ G) x z (G.mapIso p ≪≫ q))
    ((originalNerveWeakMap F x y p).comp (originalNerveWeakMap G y z q))
    (originalMixedNerveMapComposition F G) (originalNerveWeakCompositeRoot F G x y z p q)).trans
      (ContinuousMap.WeaklyPointed.loopMapCompHomotopy
        (originalNerveWeakMap F x y p) (originalNerveWeakMap G y z q))

private def originalNerveLoopMapCompositionAtPoints
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] (F : C ⥤ D) (G : D ⥤ E)
    (x : C) (y : D) (z : E) (p : F.obj x ≅ y) (q : G.obj y ≅ z)
    (a : SSet.toTop.obj (nerve C)) (b : SSet.toTop.obj (nerve D))
    (c : SSet.toTop.obj (nerve E))
    (ha : a = originalObjectVertex C x) (hb : b = originalObjectVertex D y)
    (hc : c = originalObjectVertex E z) :
    ContinuousMap.Homotopy
      (originalNerveWeakMapAtPoints (F ⋙ G) x z (G.mapIso p ≪≫ q) a c ha hc).loopMap
      ((originalNerveWeakMapAtPoints G y z q b c hb hc).loopMap.comp
        (originalNerveWeakMapAtPoints F x y p a b ha hb).loopMap) := by
  cases ha
  cases hb
  cases hc
  exact originalNerveLoopMapComposition F G x y z p q

section ActualQMaps

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E]
  [HasBinaryBiproducts E] [ExactCategory E]

private theorem originalNQWeakMapHomValue (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (mixedNQWeaklyPointedMap F).hom = mixedNQRealMap F :=
  congrArg ContinuousMap.WeaklyPointed.hom (mixedNQWeaklyPointedMap_value F)

private theorem originalNQWeakMapRootValue (F : C ⥤ D) [F.Additive] [F.IsExact]
    (t : unitInterval) :
    (mixedNQWeaklyPointedMap F).rootPath t =
      (originalEdgePath (QuillenQ.zeroComparisonIso F).hom) t :=
  by
    rw [mixedNQWeaklyPointedMap_value]
    exact mixedNQRootPath_value F t


private theorem originalNQWeakMapAtPointsValue (F : C ⥤ D) [F.Additive] [F.IsExact] :
    mixedNQWeaklyPointedMap F = originalNerveWeakMapAtPoints (QuillenQ.map F)
      (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D) (QuillenQ.zeroComparisonIso F)
      (NQReal.basepoint C) (NQReal.basepoint D)
      (NQReal.basepoint_eq_realizedVertex C) (NQReal.basepoint_eq_realizedVertex D) := by
  apply originalWeakPointedExt
  · exact (originalNQWeakMapHomValue F).trans (mixedNQRealMap_value F)
  · apply originalPathHEqOfValues
    intro t
    exact originalNQWeakMapRootValue F t

private def originalNQRealMapNatIsoRootedFamilyComputed
    (F G : C ⥤ D) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (alpha : F ≅ G) :
    {H : ContinuousMap.Homotopy (mixedNQRealMap F) (mixedNQRealMap G) //
      (mixedNQRootPath F).Homotopic ((H.evalAt (NQReal.basepoint C)).trans (mixedNQRootPath G))} :=
  by
    let H := originalNerveRootedNatIsoAtPoints (QuillenQ.map F) (QuillenQ.map G)
      (QuillenQ.mapNatIso F G alpha) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D)
      (QuillenQ.zeroComparisonIso F) (QuillenQ.zeroComparisonIso G)
      (QuillenQ.zeroComparisonIso_naturality F G alpha)
      (NQReal.basepoint C) (NQReal.basepoint D)
      (NQReal.basepoint_eq_realizedVertex C) (NQReal.basepoint_eq_realizedVertex D)
    have A : OriginalRootedNerveFamily (NQReal.basepoint C) (NQReal.basepoint D)
        (mixedNQWeaklyPointedMap F) (mixedNQWeaklyPointedMap G) := by
      rw [originalNQWeakMapAtPointsValue F, originalNQWeakMapAtPointsValue G]
      exact H
    rw [mixedNQWeaklyPointedMap_value F, mixedNQWeaklyPointedMap_value G] at A
    exact ⟨A.homotopy, A.root⟩

/-- The actual mixed realized NatIso family retains the canonical zero-root trace. -/
public def mixedNQRealMapNatIsoRootedFamily
    (F G : C ⥤ D) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (alpha : F ≅ G) :
    {H : ContinuousMap.Homotopy (mixedNQRealMap F) (mixedNQRealMap G) //
      (mixedNQRootPath F).Homotopic ((H.evalAt (NQReal.basepoint C)).trans (mixedNQRootPath G))} :=
  originalNQRealMapNatIsoRootedFamilyComputed F G alpha

private theorem originalNQConstructorLoopValue (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (⟨mixedNQRealMap F, mixedNQRootPath F⟩ :
      ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D)).loopMap =
      mixedNQKSpaceMap F := by
  apply ContinuousMap.ext
  intro p
  rw [ContinuousMap.WeaklyPointed.loopMap_apply]
  exact (mixedNQKSpaceMap_value F p).symm

private theorem originalNQKSpaceAsWeakLoopValue (F : C ⥤ D) [F.Additive] [F.IsExact] :
    mixedNQKSpaceMap F = (mixedNQWeaklyPointedMap F).loopMap :=
  (originalNQConstructorLoopValue F).symm.trans
    (congrArg ContinuousMap.WeaklyPointed.loopMap (mixedNQWeaklyPointedMap_value F)).symm

/-- Actual canonical Q zero-Iso coherence gives the whole mixed loop NatIso homotopy. -/
public def mixedNQKSpaceMapNatIsoHomotopy
    (F G : C ⥤ D) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (alpha : F ≅ G) :
    ContinuousMap.Homotopy (mixedNQKSpaceMap F) (mixedNQKSpaceMap G) := by
  let WF : ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D) :=
    ⟨mixedNQRealMap F, mixedNQRootPath F⟩
  let WG : ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D) :=
    ⟨mixedNQRealMap G, mixedNQRootPath G⟩
  let H := mixedNQRealMapNatIsoRootedFamily F G alpha
  let L := ContinuousMap.WeaklyPointed.loopMapHomotopyOfMap WF WG H.val H.property.some
  exact L.cast (originalNQConstructorLoopValue F) (originalNQConstructorLoopValue G)

private theorem originalNQCompositeFunctorMapValue
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    mixedNQRealMap (F ⋙ G) =
      CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F ⋙ QuillenQ.map G) := by
  let A : QuillenQ C ⥤ QuillenQ E := QuillenQ.map (F ⋙ G)
  let B : QuillenQ C ⥤ QuillenQ E := QuillenQ.map F ⋙ QuillenQ.map G
  have hFunctor : A = B := QuillenQ.map_comp F G
  have hOriginal : mixedNQRealMap (F ⋙ G) = CategoryTheory.realizedNerveFunctorMap A :=
    mixedNQRealMap_value (F ⋙ G)
  have hMap : CategoryTheory.realizedNerveFunctorMap A =
      CategoryTheory.realizedNerveFunctorMap B :=
    congrArg (fun H : QuillenQ C ⥤ QuillenQ E => CategoryTheory.realizedNerveFunctorMap H) hFunctor
  exact hOriginal.trans hMap

private theorem originalNQCompositeRootEdgeValue
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t : unitInterval) :
    (originalEdgePath (QuillenQ.zeroComparisonIso (F ⋙ G)).hom) t =
      (originalEdgePath ((QuillenQ.map G).mapIso (QuillenQ.zeroComparisonIso F) ≪≫
        QuillenQ.zeroComparisonIso G).hom) t := by
  let zC : QuillenQ C := ⟨0⟩
  let zE : QuillenQ E := ⟨0⟩
  let p : (QuillenQ.map (F ⋙ G)).obj zC ≅ zE := QuillenQ.zeroComparisonIso (F ⋙ G)
  let q : (QuillenQ.map (F ⋙ G)).obj zC ≅ zE :=
    (QuillenQ.map G).mapIso (QuillenQ.zeroComparisonIso F) ≪≫ QuillenQ.zeroComparisonIso G
  have hRoots : p = q := QuillenQ.zeroComparisonIso_comp F G
  exact congrArg (fun e : (QuillenQ.map (F ⋙ G)).obj zC ≅ zE => originalEdgePath e.hom t) hRoots

private theorem originalNQCompositeWeakMapValue
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    mixedNQWeaklyPointedMap (F ⋙ G) = originalNerveWeakMapAtPoints
      (QuillenQ.map F ⋙ QuillenQ.map G) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ E)
      ((QuillenQ.map G).mapIso (QuillenQ.zeroComparisonIso F) ≪≫ QuillenQ.zeroComparisonIso G)
      (NQReal.basepoint C) (NQReal.basepoint E)
      (NQReal.basepoint_eq_realizedVertex C) (NQReal.basepoint_eq_realizedVertex E) := by
  let WF : ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint E) :=
    mixedNQWeaklyPointedMap (F ⋙ G)
  let WG : ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint E) :=
    originalNerveWeakMapAtPoints
      (QuillenQ.map F ⋙ QuillenQ.map G) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ E)
      ((QuillenQ.map G).mapIso (QuillenQ.zeroComparisonIso F) ≪≫ QuillenQ.zeroComparisonIso G)
      (NQReal.basepoint C) (NQReal.basepoint E)
      (NQReal.basepoint_eq_realizedVertex C) (NQReal.basepoint_eq_realizedVertex E)
  have hHom1 : WF.hom = mixedNQRealMap (F ⋙ G) := originalNQWeakMapHomValue (F ⋙ G)
  have hHom2 : mixedNQRealMap (F ⋙ G) = WG.hom := originalNQCompositeFunctorMapValue F G
  have hHom : WF.hom = WG.hom := hHom1.trans hHom2
  have hRoot : HEq WF.rootPath WG.rootPath := by
    apply originalPathHEqOfValues
    intro t
    have hValue : WF.rootPath t = (originalEdgePath (QuillenQ.zeroComparisonIso (F ⋙ G)).hom) t :=
      originalNQWeakMapRootValue (F ⋙ G) t
    have hEdge : (originalEdgePath (QuillenQ.zeroComparisonIso (F ⋙ G)).hom) t = WG.rootPath t :=
      originalNQCompositeRootEdgeValue F G t
    exact hValue.trans hEdge
  exact originalWeakPointedExt hHom hRoot

/-- Original Q zero-Iso composition derives the whole actual mixed loop composition family. -/
public def mixedNQKSpaceMapCompHomotopy
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    ContinuousMap.Homotopy (mixedNQKSpaceMap (F ⋙ G))
      ((mixedNQKSpaceMap G).comp (mixedNQKSpaceMap F)) := by
  let WFG := originalNerveWeakMapAtPoints (QuillenQ.map F ⋙ QuillenQ.map G)
    (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ E)
    ((QuillenQ.map G).mapIso (QuillenQ.zeroComparisonIso F) ≪≫ QuillenQ.zeroComparisonIso G)
    (NQReal.basepoint C) (NQReal.basepoint E)
    (NQReal.basepoint_eq_realizedVertex C) (NQReal.basepoint_eq_realizedVertex E)
  let H := originalNerveLoopMapCompositionAtPoints (QuillenQ.map F) (QuillenQ.map G)
    (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D) (⟨0⟩ : QuillenQ E)
    (QuillenQ.zeroComparisonIso F) (QuillenQ.zeroComparisonIso G)
    (NQReal.basepoint C) (NQReal.basepoint D) (NQReal.basepoint E)
    (NQReal.basepoint_eq_realizedVertex C) (NQReal.basepoint_eq_realizedVertex D)
    (NQReal.basepoint_eq_realizedVertex E)
  have hSource : WFG.loopMap = mixedNQKSpaceMap (F ⋙ G) :=
    (congrArg ContinuousMap.WeaklyPointed.loopMap (originalNQCompositeWeakMapValue F G)).symm.trans
      (originalNQKSpaceAsWeakLoopValue (F ⋙ G)).symm
  have hTarget :
      (originalNerveWeakMapAtPoints (QuillenQ.map G) (⟨0⟩ : QuillenQ D) (⟨0⟩ : QuillenQ E)
        (QuillenQ.zeroComparisonIso G) (NQReal.basepoint D) (NQReal.basepoint E)
        (NQReal.basepoint_eq_realizedVertex D) (NQReal.basepoint_eq_realizedVertex E)).loopMap.comp
      (originalNerveWeakMapAtPoints (QuillenQ.map F) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D)
        (QuillenQ.zeroComparisonIso F) (NQReal.basepoint C) (NQReal.basepoint D)
        (NQReal.basepoint_eq_realizedVertex C) (NQReal.basepoint_eq_realizedVertex D)).loopMap =
      (mixedNQKSpaceMap G).comp (mixedNQKSpaceMap F) :=
    congrArg₂ (fun f g => f.comp g)
      ((congrArg ContinuousMap.WeaklyPointed.loopMap (originalNQWeakMapAtPointsValue G)).symm.trans
        (originalNQKSpaceAsWeakLoopValue G).symm)
      ((congrArg ContinuousMap.WeaklyPointed.loopMap (originalNQWeakMapAtPointsValue F)).symm.trans
        (originalNQKSpaceAsWeakLoopValue F).symm)
  exact H.cast hSource hTarget

end ActualQMaps

end AlgebraicKTheory.QuillenMixedUniverseTransport

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

namespace AlgebraicKTheory.StableGL

open QuillenMixedUniverseTransport

private abbrev originalWorkingUpR.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] : FGProjectiveCat.{max uR uMR} R ⥤
      mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R :=
  FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} R

private abbrev originalWorkingDownR.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] : mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R ⥤
      FGProjectiveCat.{max uR uMR} R :=
  FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uMR,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} R

private abbrev originalWorkingUpS.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] : FGProjectiveCat.{max uS uMS} S ⥤
      mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S :=
  FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} S

private abbrev originalWorkingDownS.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] : mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S ⥤
      FGProjectiveCat.{max uS uMS} S :=
  FGProjectiveCat.CategoryUniverseLift.downFunctor.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} S

private def originalProjectiveDownSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    originalWorkingDownR.{uR, uS, uMR, uMS, uNR, uNS} R ⋙
        nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ≅
      mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f ⋙
        originalWorkingDownS.{uR, uS, uMR, uMS, uNR, uNS} S := by
  let D := originalWorkingDownR.{uR, uS, uMR, uMS, uNR, uNS} R
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let U := originalWorkingUpS.{uR, uS, uMR, uMS, uNR, uNS} S
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} S
  let A : (F ⋙ U) ⋙ E.inverse ≅ F :=
    Functor.associator F U E.inverse ≪≫
      Functor.isoWhiskerLeft F E.unitIso.symm ≪≫ Functor.rightUnitor F
  exact ((Functor.associator D (F ⋙ U) E.inverse) ≪≫
    Functor.isoWhiskerLeft D A).symm

/-- The actual original scalar/lift NatIso and zero roots give the full up-loop square. -/
public def mixedOriginalQUpLoopScalarSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)).comp
        (mixedOriginalQUpLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} R))
      ((mixedOriginalQUpLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} S).comp
        (mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f))) := by
  let A := originalWorkingUpR.{uR, uS, uMR, uMS, uNR, uNS} R
  let B := originalWorkingUpS.{uR, uS, uMR, uMS, uNR, uNS} S
  let W := mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let alpha := mixedOriginalProjectiveLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f
  let H := (mixedNQKSpaceMapCompHomotopy A W).symm.trans
    ((mixedNQKSpaceMapNatIsoHomotopy (A ⋙ W) (F ⋙ B) alpha).trans
      (mixedNQKSpaceMapCompHomotopy F B))
  have hA : mixedNQKSpaceMap A = mixedOriginalQUpLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} R :=
    (mixedOriginalQUpLoopMapR_value.{uR, uS, uMR, uMS, uNR, uNS} R).symm
  have hB : mixedNQKSpaceMap B = mixedOriginalQUpLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} S :=
    (mixedOriginalQUpLoopMapS_value.{uR, uS, uMR, uMS, uNR, uNS} S).symm
  exact H.cast (congrArg (fun m => (mixedNQKSpaceMap W).comp m) hA)
    (congrArg (fun m => m.comp (mixedNQKSpaceMap F)) hB)

/-- The SAME original target unit derives the full down-loop scalar square. -/
public def mixedOriginalQDownLoopScalarSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
        (mixedOriginalQDownLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} R))
      ((mixedOriginalQDownLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} S).comp
        (mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f))) := by
  let A := originalWorkingDownR.{uR, uS, uMR, uMS, uNR, uNS} R
  let B := originalWorkingDownS.{uR, uS, uMR, uMS, uNR, uNS} S
  let W := mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let alpha := originalProjectiveDownSquare.{uR, uS, uMR, uMS, uNR, uNS} f
  let H := (mixedNQKSpaceMapCompHomotopy A F).symm.trans
    ((mixedNQKSpaceMapNatIsoHomotopy (A ⋙ F) (W ⋙ B) alpha).trans
      (mixedNQKSpaceMapCompHomotopy W B))
  have hA : mixedNQKSpaceMap A = mixedOriginalQDownLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} R :=
    (mixedOriginalQDownLoopMapR_value.{uR, uS, uMR, uMS, uNR, uNS} R).symm
  have hB : mixedNQKSpaceMap B = mixedOriginalQDownLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} S :=
    (mixedOriginalQDownLoopMapS_value.{uR, uS, uMR, uMS, uNR, uNS} S).symm
  exact H.cast (congrArg (fun m => (mixedNQKSpaceMap F).comp m) hA)
    (congrArg (fun m => m.comp (mixedNQKSpaceMap W)) hB)

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uD vD

namespace AlgebraicKTheory.QuillenMixedUniverseTransport

private theorem originalRealizedEquivalenceForwardValue
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (E : C ≌ D) :
    (CategoryTheory.realizedNerveEquivalence E).toFun =
      CategoryTheory.realizedNerveFunctorMap E.functor :=
  (CategoryTheory.realizedNerveEquivalence_toFun_recipe E).trans
    (CategoryTheory.realizedNerveFunctorMap_recipe E.functor).symm

private theorem originalRealizedEquivalenceInverseValue
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (E : C ≌ D) :
    (CategoryTheory.realizedNerveEquivalence E).invFun =
      CategoryTheory.realizedNerveFunctorMap E.inverse :=
  (CategoryTheory.realizedNerveEquivalence_invFun_recipe E).trans
    (CategoryTheory.realizedNerveFunctorMap_recipe E.inverse).symm

private theorem originalQRealizationUpValue.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : QuillenUniverseLift.qRealizationUp.{uR, uM, uObj, uHom} R =
      mixedNQRealMap (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) :=
  (QuillenUniverseLift.qRealizationUp_value.{uR, uM, uObj, uHom} R).trans
    ((originalRealizedEquivalenceForwardValue
      (QuillenUniverseLift.qCategoryEquivalence.{uR, uM, uObj, uHom} R)).trans
      ((congrArg CategoryTheory.realizedNerveFunctorMap
        (QuillenUniverseLift.qCategoryEquivalence_forward_value.{uR, uM, uObj, uHom} R)).trans
        (mixedNQRealMap_value
          (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R)).symm))

private theorem originalQRealizationDownValue.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : QuillenUniverseLift.qRealizationDown.{uR, uM, uObj, uHom} R =
      mixedNQRealMap (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R) :=
  (QuillenUniverseLift.qRealizationDown_value.{uR, uM, uObj, uHom} R).trans
    ((originalRealizedEquivalenceInverseValue
      (QuillenUniverseLift.qCategoryEquivalence.{uR, uM, uObj, uHom} R)).trans
      ((congrArg CategoryTheory.realizedNerveFunctorMap
        (QuillenUniverseLift.qCategoryEquivalence_inverse_value.{uR, uM, uObj, uHom} R)).trans
        (mixedNQRealMap_value
          (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)).symm))

private theorem originalQUpZeroIsoValue.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : QuillenUniverseLift.qUpZeroIso.{uR, uM, uObj, uHom} R =
      eqToIso (QuillenUniverseLift.qUpFunctor_obj.{uR, uM, uObj, uHom} R
        (0 : QuillenUniverseLift.canonicalCategory.{uR, uM} R)) ≪≫
      QuillenQ.zeroComparisonIso
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) := by
  let U := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
  let h0 := QuillenUniverseLift.qUpFunctor_obj.{uR, uM, uObj, uHom} R
    (0 : QuillenUniverseLift.canonicalCategory.{uR, uM} R)
  have hZero : QuillenQ.zeroComparisonIso U = QuillenQ.underlyingIso
      (FGProjectiveCat.CategoryUniverseLift.upZeroIso.{uR, uM, uObj, uHom} R) := by
    change QuillenQ.underlyingIso U.mapZeroObject = _
    exact congrArg QuillenQ.underlyingIso
      (FGProjectiveCat.CategoryUniverseLift.upFunctorMapZeroObject.{uR, uM, uObj, uHom} R)
  exact (QuillenUniverseLift.qUpZeroIso_eq_underlyingIso.{uR, uM, uObj, uHom} R).trans
    (congrArg (fun e => eqToIso h0 ≪≫ e) hZero.symm)

private theorem originalQDownZeroIsoValue.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : QuillenUniverseLift.qDownZeroIso.{uR, uM, uObj, uHom} R =
      eqToIso (QuillenUniverseLift.qDownFunctor_obj.{uR, uM, uObj, uHom} R
        (0 : QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)) ≪≫
      QuillenQ.zeroComparisonIso
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R) := by
  let U := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let h0 := QuillenUniverseLift.qDownFunctor_obj.{uR, uM, uObj, uHom} R
    (0 : QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
  have hZero : QuillenQ.zeroComparisonIso U = QuillenQ.underlyingIso
      (FGProjectiveCat.CategoryUniverseLift.downZeroIso.{uR, uM, uObj, uHom} R) := by
    change QuillenQ.underlyingIso U.mapZeroObject = _
    exact congrArg QuillenQ.underlyingIso
      (FGProjectiveCat.CategoryUniverseLift.downFunctorMapZeroObject.{uR, uM, uObj, uHom} R)
  exact (QuillenUniverseLift.qDownZeroIso_eq_underlyingIso.{uR, uM, uObj, uHom} R).trans
    (congrArg (fun e => eqToIso h0 ≪≫ e) hZero.symm)


private theorem originalQLiteralUpWeakMapValue.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : QuillenUniverseLift.qUpWeaklyPointed.{uR, uM, uObj, uHom} R =
      originalNerveWeakMapAtPoints
        (QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R))
        (⟨0⟩ : QuillenQ (QuillenUniverseLift.canonicalCategory.{uR, uM} R))
        (⟨0⟩ : QuillenQ (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R))
        (QuillenQ.zeroComparisonIso
          (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R))
        (OriginalQZeroComparison.zeroQVertex
          (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R))
        (OriginalQZeroComparison.zeroQVertex
          (C := QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R))
        originalZeroEqNerveZero originalZeroEqNerveZero := by
  rw [QuillenUniverseLift.qUpWeaklyPointed_value]
  apply originalWeakPointedExt
  · exact (originalQRealizationUpValue.{uR, uM, uObj, uHom} R).trans
      (mixedNQRealMap_value
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R))
  · apply originalPathHEqOfValues
    intro t
    let U := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
    let h0 := QuillenUniverseLift.qUpFunctor_obj.{uR, uM, uObj, uHom} R
      (0 : QuillenUniverseLift.canonicalCategory.{uR, uM} R)
    have hRoot := QuillenUniverseLift.qUpZeroPath_value.{uR, uM, uObj, uHom} R t
    have hIso := congrArg
      (fun p : (QuillenUniverseLift.qUpFunctor.{uR, uM, uObj, uHom} R).obj
        (⟨0⟩ : QuillenQ (QuillenUniverseLift.canonicalCategory.{uR, uM} R)) ≅
        (⟨0⟩ : QuillenQ (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)) =>
          originalEdgePath p.hom t) (originalQUpZeroIsoValue.{uR, uM, uObj, uHom} R)
    exact hRoot.trans (hIso.trans
      (originalEdgeIsoSourceTransportValue h0 (QuillenQ.zeroComparisonIso U) t))

private theorem originalQLiteralDownWeakMapValue.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R =
      originalNerveWeakMapAtPoints
        (QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R))
        (⟨0⟩ : QuillenQ (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R))
        (⟨0⟩ : QuillenQ (QuillenUniverseLift.canonicalCategory.{uR, uM} R))
        (QuillenQ.zeroComparisonIso
          (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R))
        (OriginalQZeroComparison.zeroQVertex
          (C := QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R))
        (OriginalQZeroComparison.zeroQVertex
          (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R))
        originalZeroEqNerveZero originalZeroEqNerveZero := by
  rw [QuillenUniverseLift.qDownWeaklyPointed_value]
  apply originalWeakPointedExt
  · exact (originalQRealizationDownValue.{uR, uM, uObj, uHom} R).trans
      (mixedNQRealMap_value
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R))
  · apply originalPathHEqOfValues
    intro t
    let U := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
    let h0 := QuillenUniverseLift.qDownFunctor_obj.{uR, uM, uObj, uHom} R
      (0 : QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
    have hRoot := QuillenUniverseLift.qDownZeroPath_value.{uR, uM, uObj, uHom} R t
    have hIso := congrArg
      (fun p : (QuillenUniverseLift.qDownFunctor.{uR, uM, uObj, uHom} R).obj
        (⟨0⟩ : QuillenQ (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)) ≅
        (⟨0⟩ : QuillenQ (QuillenUniverseLift.canonicalCategory.{uR, uM} R)) =>
          originalEdgePath p.hom t) (originalQDownZeroIsoValue.{uR, uM, uObj, uHom} R)
    exact hRoot.trans (hIso.trans
      (originalEdgeIsoSourceTransportValue h0 (QuillenQ.zeroComparisonIso U) t))


end AlgebraicKTheory.QuillenMixedUniverseTransport

end


noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uD vD uX uY

namespace AlgebraicKTheory.QuillenMixedUniverseTransport

open StableGL OriginalQuillenUnliftedTransport

private def originalWeakPointChange
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x x' : X} {y y' : Y} (f : ContinuousMap.WeaklyPointed x y)
    (hx : x' = x) (hy : y' = y) : ContinuousMap.WeaklyPointed x' y' where
  hom := f.hom
  rootPath := f.rootPath.cast (congrArg f.hom hx) hy

private theorem originalWeakLoopPointChangeValue
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x x' : X} {y y' : Y} (f : ContinuousMap.WeaklyPointed x y)
    (hx : x' = x) (hy : y' = y) (p : LoopSpace X x') :
    (f.loopMap (p.cast hx.symm hx.symm)).cast hy hy =
      (originalWeakPointChange f hx hy).loopMap p := by
  cases hx
  cases hy
  rfl

private theorem originalNQLoopPointHomeomorphCastValue
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (p : NQKSpace C) :
    originalNQLoopPointHomeomorph C p =
      p.cast (originalNQBasepointEqOriginalZero (C := C)).symm
        (originalNQBasepointEqOriginalZero (C := C)).symm := by
  apply Path.ext
  funext t
  exact originalNQLoopPointHomeomorph_value C p t

private theorem originalNQLoopPointHomeomorphSymmCastValue
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    (p : BasedSplitExactQLoop.originalQLoops (C := C)) :
    (originalNQLoopPointHomeomorph C).symm p =
      p.cast (originalNQBasepointEqOriginalZero (C := C))
        (originalNQBasepointEqOriginalZero (C := C)) := by
  apply Path.ext
  funext t
  exact originalNQLoopPointHomeomorph_symm_value C p t

private theorem originalLiteralWeakAtNQPointValue
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] [ExactCategory D] (F : C ⥤ D) [F.Additive] [F.IsExact] :
    originalWeakPointChange
      (originalNerveWeakMapAtPoints (QuillenQ.map F) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D)
        (QuillenQ.zeroComparisonIso F)
        (OriginalQZeroComparison.zeroQVertex (C := C))
        (OriginalQZeroComparison.zeroQVertex (C := D))
        (originalZeroEqNerveZero (C := C)) (originalZeroEqNerveZero (C := D)))
      (originalNQBasepointEqOriginalZero (C := C)) (originalNQBasepointEqOriginalZero (C := D)) =
      mixedNQWeaklyPointedMap F := by
  rw [mixedNQWeaklyPointedMap_value]
  apply originalWeakPointedExt
  · exact (mixedNQRealMap_value F).symm
  · apply originalPathHEqOfValues
    intro t
    exact (mixedNQRootPath_value F t).symm

private theorem originalLiteralLoopAtNQPointValue
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] [ExactCategory D] (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun.comp
      ((originalNerveWeakMapAtPoints (QuillenQ.map F) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D)
        (QuillenQ.zeroComparisonIso F)
        (OriginalQZeroComparison.zeroQVertex (C := C))
        (OriginalQZeroComparison.zeroQVertex (C := D))
        (originalZeroEqNerveZero (C := C)) (originalZeroEqNerveZero (C := D))).loopMap.comp
          (originalNQLoopPointHomeomorph C).toHomotopyEquiv.toFun) = mixedNQKSpaceMap F := by
  apply ContinuousMap.ext
  intro p
  change (originalNQLoopPointHomeomorph D).symm
      ((originalNerveWeakMapAtPoints (QuillenQ.map F) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D)
        (QuillenQ.zeroComparisonIso F)
        (OriginalQZeroComparison.zeroQVertex (C := C))
        (OriginalQZeroComparison.zeroQVertex (C := D))
        (originalZeroEqNerveZero (C := C)) (originalZeroEqNerveZero (C := D))).loopMap
          (originalNQLoopPointHomeomorph C p)) =
      mixedNQKSpaceMap F p
  rw [originalNQLoopPointHomeomorphSymmCastValue, originalNQLoopPointHomeomorphCastValue]
  exact (originalWeakLoopPointChangeValue
    (originalNerveWeakMapAtPoints (QuillenQ.map F) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D)
      (QuillenQ.zeroComparisonIso F)
      (OriginalQZeroComparison.zeroQVertex (C := C))
      (OriginalQZeroComparison.zeroQVertex (C := D))
        (originalZeroEqNerveZero (C := C)) (originalZeroEqNerveZero (C := D)))
    (originalNQBasepointEqOriginalZero (C := C))
    (originalNQBasepointEqOriginalZero (C := D)) p).trans
      ((congrArg (fun f => f.loopMap p) (originalLiteralWeakAtNQPointValue F)).trans
        (ContinuousMap.congr_fun (originalNQKSpaceAsWeakLoopValue F).symm p))

/-- The SAME original down retuning family reaches the actual canonical mixed NQ map. -/
public def originalUnliftedNQdownRetuningToMixed.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ContinuousMap.Homotopy
      (originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R)
      (mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)) := by
  let C := QuillenUniverseLift.canonicalCategory.{uR, uM} R
  let D := QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R
  let A := (originalNQLoopPointHomeomorph D).toHomotopyEquiv.toFun
  let B := (originalNQLoopPointHomeomorph C).symm.toHomotopyEquiv.toFun
  let U := QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R
  let V := QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R
  let Q := QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R
  let F := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let H0 := (QuillenUniverseLift.QdownRetuningHomotopy.{uR, uM, uObj, uHom, uNative}
    R).compContinuousMap (U.comp A)
  let H := (ContinuousMap.Homotopy.refl B).comp H0
  have hSource : B.comp
      ((QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R).comp (U.comp A)) =
      originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R := by
    have hAssoc : B.comp
        ((QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R).comp (U.comp A)) =
        B.comp (((QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R).comp U).comp A) := by
      apply ContinuousMap.ext
      intro p
      rfl
    exact hAssoc.trans (originalUnliftedNQdown_value.{uR, uM, uObj, uHom, uNative} R).symm
  have hCollapse : B.comp ((Q.loopMap.comp V).comp (U.comp A)) =
      B.comp (Q.loopMap.comp A) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg (fun q => B (Q.loopMap q))
      (ContinuousMap.congr_fun
        (QuillenUniverseLift.rawNativeCarrierDown_comp_up.{uR, uM, uObj, uHom, uNative} R)
        (A p))
  have hLiteral : B.comp (Q.loopMap.comp A) = B.comp
      ((originalNerveWeakMapAtPoints (QuillenQ.map F) (⟨0⟩ : QuillenQ D) (⟨0⟩ : QuillenQ C)
        (QuillenQ.zeroComparisonIso F)
        (OriginalQZeroComparison.zeroQVertex (C := D))
        (OriginalQZeroComparison.zeroQVertex (C := C))
        originalZeroEqNerveZero originalZeroEqNerveZero).loopMap.comp A) :=
    congrArg (fun q => B.comp (q.loopMap.comp A))
      (originalQLiteralDownWeakMapValue.{uR, uM, uObj, uHom} R)
  have hTarget : B.comp ((Q.loopMap.comp V).comp (U.comp A)) = mixedNQKSpaceMap F :=
    hCollapse.trans (hLiteral.trans (originalLiteralLoopAtNQPointValue F))
  exact H.cast hSource hTarget

/-- The SAME independently selected up retuning reaches the original mixed NQ map. -/
public def originalUnliftedNQupRetuningToMixed.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ContinuousMap.Homotopy
      (originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R)
      (mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R)) := by
  let C := QuillenUniverseLift.canonicalCategory.{uR, uM} R
  let D := QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R
  let A := (originalNQLoopPointHomeomorph C).toHomotopyEquiv.toFun
  let B := (originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun
  let U := QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R
  let V := QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R
  let Q := QuillenUniverseLift.qUpWeaklyPointed.{uR, uM, uObj, uHom} R
  let F := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
  let H0 := (QuillenUniverseLift.QupRetuningHomotopy.{uR, uM, uObj, uHom, uNative}
    R).compContinuousMap A
  let H := (ContinuousMap.Homotopy.refl (B.comp V)).comp H0
  have hSource : (B.comp V).comp
      ((QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R).comp A) =
      originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R := by
    have hAssoc : (B.comp V).comp
        ((QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R).comp A) =
        B.comp ((V.comp (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R)).comp A) := by
      apply ContinuousMap.ext
      intro p
      rfl
    exact hAssoc.trans (originalUnliftedNQup_value.{uR, uM, uObj, uHom, uNative} R).symm
  have hCollapse : (B.comp V).comp ((U.comp Q.loopMap).comp A) =
      B.comp (Q.loopMap.comp A) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg B
      (ContinuousMap.congr_fun
        (QuillenUniverseLift.rawNativeCarrierDown_comp_up.{uR, uM, uObj, uHom, uNative} R)
        (Q.loopMap (A p)))
  have hLiteral : B.comp (Q.loopMap.comp A) = B.comp
      ((originalNerveWeakMapAtPoints (QuillenQ.map F) (⟨0⟩ : QuillenQ C) (⟨0⟩ : QuillenQ D)
        (QuillenQ.zeroComparisonIso F)
        (OriginalQZeroComparison.zeroQVertex (C := C))
        (OriginalQZeroComparison.zeroQVertex (C := D))
        originalZeroEqNerveZero originalZeroEqNerveZero).loopMap.comp A) :=
    congrArg (fun q => B.comp (q.loopMap.comp A))
      (originalQLiteralUpWeakMapValue.{uR, uM, uObj, uHom} R)
  have hTarget : (B.comp V).comp ((U.comp Q.loopMap).comp A) = mixedNQKSpaceMap F :=
    hCollapse.trans (hLiteral.trans (originalLiteralLoopAtNQPointValue F))
  exact H.cast hSource hTarget

end AlgebraicKTheory.QuillenMixedUniverseTransport

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

namespace AlgebraicKTheory.StableGL

open QuillenMixedUniverseTransport OriginalQuillenUnliftedTransport

private abbrev originalRetunedUpR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :=
  originalUnliftedNQup.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNR} R

private abbrev originalRetunedDownR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :=
  originalUnliftedNQdown.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNR} R

private abbrev originalRetunedUpS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :=
  originalUnliftedNQup.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S

private abbrev originalRetunedDownS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :=
  originalUnliftedNQdown.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S

/-- The original independently retuned Q inclusions satisfy the actual whole scalar loop square. -/
public def mixedOriginalRetunedQUpLoopScalarSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)).comp
        (originalUnliftedNQup.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS, uNR} R))
      ((originalUnliftedNQup.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S).comp
          (mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f))) := by
  let F := mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let W := mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
  let HR := originalUnliftedNQupRetuningToMixed.{uR, uMR,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNR} R
  let HS := originalUnliftedNQupRetuningToMixed.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
  let K := mixedOriginalQUpLoopScalarSquare.{uR, uS, uMR, uMS, uNR, uNS} f
  let C := K.cast
    (congrArg (fun m => W.comp m) (mixedOriginalQUpLoopMapR_value.{uR, uS, uMR, uMS, uNR, uNS} R))
    (congrArg (fun m => m.comp F) (mixedOriginalQUpLoopMapS_value.{uR, uS, uMR, uMS, uNR, uNS} S))
  exact ((ContinuousMap.Homotopy.refl W).comp HR).trans
    (C.trans (HS.symm.compContinuousMap F))

/-- The SAME original independently retuned Q descents satisfy the whole scalar square. -/
public def mixedOriginalRetunedQDownLoopScalarSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
        (originalUnliftedNQdown.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS, uNR} R))
      ((originalUnliftedNQdown.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S).comp
          (mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f))) := by
  let F := mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let W := mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
  let HR := originalUnliftedNQdownRetuningToMixed.{uR, uMR,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNR} R
  let HS := originalUnliftedNQdownRetuningToMixed.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
  let K := mixedOriginalQDownLoopScalarSquare.{uR, uS, uMR, uMS, uNR, uNS} f
  let C := K.cast
    (congrArg (fun m => F.comp m) (mixedOriginalQDownLoopMapR_value.{uR, uS, uMR, uMS, uNR, uNS} R))
    (congrArg (fun m => m.comp W) (mixedOriginalQDownLoopMapS_value.{uR, uS, uMR, uMS, uNR, uNS} S))
  exact ((ContinuousMap.Homotopy.refl F).comp HR).trans
    (C.trans (HS.symm.compContinuousMap W))

/-- Original R-left and S-right FULL inverse families also derive the down square from up. -/
public def mixedOriginalRetunedQDownLoopScalarSquareFromUp.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
        (originalUnliftedNQdown.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS, uNR} R))
      ((originalUnliftedNQdown.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S).comp
          (mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f))) := by
  let F := mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let W := mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
  let UR := originalRetunedUpR.{uR, uS, uMR, uMS, uNR, uNS} R
  let DR := originalRetunedDownR.{uR, uS, uMR, uMS, uNR, uNS} R
  let US := originalRetunedUpS.{uR, uS, uMR, uMS, uNR, uNS} S
  let DS := originalRetunedDownS.{uR, uS, uMR, uMS, uNR, uNS} S
  let LR := originalUnliftedNQleftFamily.{uR, uMR,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNR} R
  let RS := originalUnliftedNQrightFamily.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
  let H0 := RS.toHomotopy.symm.compContinuousMap (F.comp DR)
  let H1 := (ContinuousMap.Homotopy.refl DS).comp
    ((mixedOriginalRetunedQUpLoopScalarSquare.{uR, uS, uMR, uMS, uNR, uNS}
      f).symm.compContinuousMap DR)
  let H2 := (ContinuousMap.Homotopy.refl (DS.comp W)).comp LR.toHomotopy
  let A : ContinuousMap.Homotopy (F.comp DR) (DS.comp ((US.comp F).comp DR)) :=
    H0.cast (by apply ContinuousMap.ext; intro p; rfl)
      (by apply ContinuousMap.ext; intro p; rfl)
  let B : ContinuousMap.Homotopy (DS.comp ((W.comp UR).comp DR)) (DS.comp W) :=
    H2.cast (by apply ContinuousMap.ext; intro p; rfl)
      (by apply ContinuousMap.ext; intro p; rfl)
  exact A.trans (H1.trans B)

/-- Original R-right and S-left FULL inverse families derive the up square back from down. -/
public def mixedOriginalRetunedQUpLoopScalarSquareFromDown.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)).comp
        (originalUnliftedNQup.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS, uNR} R))
      ((originalUnliftedNQup.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S).comp
          (mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f))) := by
  let F := mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let W := mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
  let UR := originalRetunedUpR.{uR, uS, uMR, uMS, uNR, uNS} R
  let DR := originalRetunedDownR.{uR, uS, uMR, uMS, uNR, uNS} R
  let US := originalRetunedUpS.{uR, uS, uMR, uMS, uNR, uNS} S
  let DS := originalRetunedDownS.{uR, uS, uMR, uMS, uNR, uNS} S
  let RR := originalUnliftedNQrightFamily.{uR, uMR,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNR} R
  let LS := originalUnliftedNQleftFamily.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
  let H0 := LS.toHomotopy.symm.compContinuousMap (W.comp UR)
  let H1 := (ContinuousMap.Homotopy.refl US).comp
    ((mixedOriginalRetunedQDownLoopScalarSquareFromUp.{uR, uS, uMR, uMS, uNR, uNS}
      f).symm.compContinuousMap UR)
  let H2 := (ContinuousMap.Homotopy.refl (US.comp F)).comp RR.toHomotopy
  let A : ContinuousMap.Homotopy (W.comp UR) (US.comp ((DS.comp W).comp UR)) :=
    H0.cast (by apply ContinuousMap.ext; intro p; rfl)
      (by apply ContinuousMap.ext; intro p; rfl)
  let B : ContinuousMap.Homotopy (US.comp ((F.comp DR).comp UR)) (US.comp F) :=
    H2.cast (by apply ContinuousMap.ext; intro p; rfl)
      (by apply ContinuousMap.ext; intro p; rfl)
  exact A.trans (H1.trans B)

end AlgebraicKTheory.StableGL

end
