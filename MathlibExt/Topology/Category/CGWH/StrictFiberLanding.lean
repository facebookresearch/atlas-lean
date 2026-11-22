/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.BasedFiber
public import MathlibExt.Topology.Category.CGWH.ClosedSubspace
public import MathlibExt.Topology.Category.TopCat.PointFiber

/-!
# Strict fibers in CGWH and ordinary topological pullbacks

The fiber of a map of compactly generated weak Hausdorff spaces over a chosen
point is a closed subspace.  We use that presentation to identify the chosen
CGWH pullback, after forgetting to `TopCat`, with the ordinary topological
pullback.  The comparison is strictly natural for based squares.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology
open scoped CGWH.limits

namespace CGWH

/-- The fiber over the specified point, as a closed subset of the total space. -/
@[no_expose]
def strictFiberClosedSet {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) : TopologicalSpace.Closeds E := by
  letI : T1Space B := inferInstance
  have hSingleton : IsClosed ({pointHomEquiv B b} : Set B) :=
    isClosed_singleton
  exact ⟨f ⁻¹' {pointHomEquiv B b}, hSingleton.preimage
    (cgwhToTop.map f).hom.continuous⟩

/-- The closed-fiber pullback cone is a limit in CGWH. -/
@[no_expose]
noncomputable def strictFiberClosedConeIsLimit
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    IsLimit (PullbackCone.mk (f := f) (g := b)
      (closedSubspaceι E (strictFiberClosedSet f b))
      (point_isTerminal.from (closedSubspace E (strictFiberClosedSet f b)))
      (by
        apply ConcreteCategory.hom_ext
        intro x
        change f x.1 = b PUnit.unit
        simpa [strictFiberClosedSet] using x.2)) := by
  apply PullbackCone.IsLimit.mk
    (by
      apply ConcreteCategory.hom_ext
      intro x
      change f x.1 = b PUnit.unit
      simpa [strictFiberClosedSet] using x.2)
  case lift =>
    intro s
    let hmem : ∀ q : s.pt, s.fst q ∈ strictFiberClosedSet f b :=
      fun q => by
        have h := ConcreteCategory.congr_hom s.condition q
        rw [point_isTerminal.hom_ext s.snd
          (point_isTerminal.from s.pt)] at h
        have hEq : f (s.fst q) =
            b ((point_isTerminal.from s.pt) q) := h
        have hp : (point_isTerminal.from s.pt) q = PUnit.unit := by
          change PUnit.unit = PUnit.unit
          rfl
        rw [hp] at hEq
        simpa [strictFiberClosedSet] using hEq
    exact ConcreteCategory.ofHom
      (show C(s.pt,
          closedSubspace E (strictFiberClosedSet f b)) from
        ⟨fun q => ⟨s.fst q, hmem q⟩,
          (cgwhToTop.map s.fst).hom.continuous.subtype_mk hmem⟩)
  case fac_left =>
    intro s
    apply ConcreteCategory.hom_ext
    intro q
    rfl
  case fac_right =>
    intro s
    exact point_isTerminal.hom_ext _ _
  case uniq =>
    intro s m hm _
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    have hq := ConcreteCategory.congr_hom hm q
    change (m q).1 = s.fst q at hq
    exact hq

/-- The chosen strict fiber is isomorphic to its closed-subspace presentation. -/
@[no_expose]
noncomputable def strictFiberClosedIso
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    strictFiber f b ≅ closedSubspace E (strictFiberClosedSet f b) :=
  (pullbackIsPullback f b).conePointUniqueUpToIso
    (strictFiberClosedConeIsLimit f b)

/-- The closed-fiber cone is also a limit after forgetting to ordinary topological spaces. -/
@[no_expose]
noncomputable def strictFiberClosedTopConeIsLimit
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    IsLimit (PullbackCone.mk (f := cgwhToTop.map f)
      (g := cgwhToTop.map b)
      (cgwhToTop.map (closedSubspaceι E (strictFiberClosedSet f b)))
      (cgwhToTop.map
        (point_isTerminal.from (closedSubspace E (strictFiberClosedSet f b))))
      (by
        apply TopCat.hom_ext
        ext x
        change f x.1 = b PUnit.unit
        simpa [strictFiberClosedSet] using x.2)) := by
  apply PullbackCone.IsLimit.mk
    (by
      apply TopCat.hom_ext
      ext x
      change f x.1 = b PUnit.unit
      simpa [strictFiberClosedSet] using x.2)
  case lift =>
    intro s
    let hmem : ∀ q : s.pt, s.fst q ∈ strictFiberClosedSet f b :=
      fun q => by
        have h := ConcreteCategory.congr_hom s.condition q
        rw [TopCat.isTerminalPUnit.hom_ext s.snd
          (TopCat.isTerminalPUnit.from s.pt)] at h
        have hEq : (cgwhToTop.map f) (s.fst q) =
            (cgwhToTop.map b)
              ((TopCat.isTerminalPUnit.from s.pt) q) := h
        have hp : (TopCat.isTerminalPUnit.from s.pt) q = PUnit.unit := by
          change PUnit.unit = PUnit.unit
          rfl
        rw [hp] at hEq
        change f (s.fst q) = b PUnit.unit
        exact hEq
    exact TopCat.ofHom
      (show ContinuousMap s.pt
          (cgwhToTop.obj
            (closedSubspace E (strictFiberClosedSet f b))) from
        ⟨fun q => ⟨s.fst q, hmem q⟩,
          s.fst.hom.continuous.subtype_mk hmem⟩)
  case fac_left =>
    intro s
    apply TopCat.hom_ext
    ext q
    rfl
  case fac_right =>
    intro s
    exact TopCat.isTerminalPUnit.hom_ext _ _
  case uniq =>
    intro s m hm _
    apply TopCat.hom_ext
    ext q
    apply Subtype.ext
    have hq := ConcreteCategory.congr_hom hm q
    change (m q).1 = s.fst q at hq
    change (m q).1 = s.fst q
    exact hq

/-- The closed fiber, in TopCat, is isomorphic to the ordinary topological pullback. -/
@[no_expose]
noncomputable def strictFiberClosedTopIso
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    cgwhToTop.obj (closedSubspace E (strictFiberClosedSet f b)) ≅
      pullback (cgwhToTop.map f) (cgwhToTop.map b) := by
  let C := closedSubspace E (strictFiberClosedSet f b)
  let i := cgwhToTop.map
    (closedSubspaceι E (strictFiberClosedSet f b))
  let t := cgwhToTop.map (point_isTerminal.from C)
  let fTop := cgwhToTop.map f
  let bTop := cgwhToTop.map b
  have hsq : i ≫ fTop = t ≫ bTop := by
    apply TopCat.hom_ext
    ext x
    change f x.1 = b PUnit.unit
    simpa [strictFiberClosedSet] using x.2
  let hom : cgwhToTop.obj C ⟶ pullback fTop bTop :=
    pullback.lift i t hsq
  let hmem : ∀ q : (pullback fTop bTop : TopCat.{v}),
      pullback.fst fTop bTop q ∈ strictFiberClosedSet f b :=
    fun q => by
      have h := ConcreteCategory.congr_hom
        (pullback.condition :
          pullback.fst fTop bTop ≫ fTop =
            pullback.snd fTop bTop ≫ bTop) q
      rw [TopCat.isTerminalPUnit.hom_ext (pullback.snd fTop bTop)
        (TopCat.isTerminalPUnit.from (pullback fTop bTop))] at h
      have hEq : fTop (pullback.fst fTop bTop q) =
          bTop ((TopCat.isTerminalPUnit.from
            (pullback fTop bTop)) q) := h
      have hp : (TopCat.isTerminalPUnit.from
          (pullback fTop bTop)) q = PUnit.unit := by
        change PUnit.unit = PUnit.unit
        rfl
      rw [hp] at hEq
      change f (pullback.fst fTop bTop q) = b PUnit.unit
      exact hEq
  let inv : pullback fTop bTop ⟶ cgwhToTop.obj C :=
    TopCat.ofHom
      (show ContinuousMap (pullback fTop bTop : TopCat.{v})
          (cgwhToTop.obj C) from
        ⟨fun q => ⟨pullback.fst fTop bTop q, hmem q⟩,
        (ConcreteCategory.hom
          (pullback.fst fTop bTop)).continuous.subtype_mk hmem⟩)
  have hInvFst : inv ≫ i = pullback.fst fTop bTop := by
    apply TopCat.hom_ext
    ext q
    rfl
  have hInvSnd : inv ≫ t = pullback.snd fTop bTop :=
    TopCat.isTerminalPUnit.hom_ext _ _
  refine
    { hom := hom
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · have hLimit : IsLimit
        (PullbackCone.mk (f := fTop) (g := bTop) i t hsq) :=
      strictFiberClosedTopConeIsLimit f b
    apply PullbackCone.IsLimit.hom_ext hLimit
    · change (pullback.lift i t hsq ≫ inv) ≫ i = 𝟙 _ ≫ i
      rw [Category.assoc, hInvFst, pullback.lift_fst, Category.id_comp]
    · change (pullback.lift i t hsq ≫ inv) ≫ t = 𝟙 _ ≫ t
      rw [Category.assoc, hInvSnd, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · change (inv ≫ pullback.lift i t hsq) ≫
        pullback.fst fTop bTop = pullback.fst fTop bTop
      rw [Category.assoc, pullback.lift_fst, hInvFst]
    · change (inv ≫ pullback.lift i t hsq) ≫
        pullback.snd fTop bTop = pullback.snd fTop bTop
      rw [Category.assoc, pullback.lift_snd, hInvSnd]

private theorem strictFiberClosedTopIso_hom_fst
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    (strictFiberClosedTopIso f b).hom ≫
        pullback.fst (cgwhToTop.map f) (cgwhToTop.map b) =
      cgwhToTop.map
        (closedSubspaceι E (strictFiberClosedSet f b)) := by
  unfold strictFiberClosedTopIso
  exact pullback.lift_fst (f := cgwhToTop.map f)
    (g := cgwhToTop.map b) _ _ _

private theorem strictFiberClosedTopIso_hom_snd
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    (strictFiberClosedTopIso f b).hom ≫
        pullback.snd (cgwhToTop.map f) (cgwhToTop.map b) =
      cgwhToTop.map
        (point_isTerminal.from
          (closedSubspace E (strictFiberClosedSet f b))) := by
  unfold strictFiberClosedTopIso
  exact pullback.lift_snd (f := cgwhToTop.map f)
    (g := cgwhToTop.map b) _ _ _

/-- The native CGWH strict fiber, viewed in `TopCat`, is the ordinary
topological pullback over the chosen point. -/
noncomputable def strictFiberLandingIso
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    cgwhToTop.obj (strictFiber f b) ≅
      pullback (cgwhToTop.map f) (cgwhToTop.map b) :=
  (cgwhToTop.mapIso (strictFiberClosedIso f b)).trans
    (strictFiberClosedTopIso f b)

/-- The landing isomorphism preserves projection to the total space. -/
@[reassoc]
theorem strictFiberLandingIso_hom_fst
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    (strictFiberLandingIso f b).hom ≫
        pullback.fst (cgwhToTop.map f) (cgwhToTop.map b) =
      cgwhToTop.map (strictFiberToTotal f b) := by
  have hNative :
      (strictFiberClosedIso f b).hom ≫
          closedSubspaceι E (strictFiberClosedSet f b) =
        strictFiberToTotal f b :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (pullbackIsPullback f b) (strictFiberClosedConeIsLimit f b)
      WalkingCospan.left
  unfold strictFiberLandingIso
  rw [Iso.trans_hom, Category.assoc, strictFiberClosedTopIso_hom_fst]
  change cgwhToTop.map (strictFiberClosedIso f b).hom ≫
      cgwhToTop.map
        (closedSubspaceι E (strictFiberClosedSet f b)) = _
  rw [
    ← cgwhToTop.map_comp, hNative]

/-- The landing isomorphism preserves projection to the point object. -/
@[reassoc]
theorem strictFiberLandingIso_hom_snd
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    (strictFiberLandingIso f b).hom ≫
        pullback.snd (cgwhToTop.map f) (cgwhToTop.map b) =
      cgwhToTop.map (strictFiberToPoint f b) := by
  have hNative :
      (strictFiberClosedIso f b).hom ≫
          point_isTerminal.from
            (closedSubspace E (strictFiberClosedSet f b)) =
        strictFiberToPoint f b :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (pullbackIsPullback f b) (strictFiberClosedConeIsLimit f b)
      WalkingCospan.right
  unfold strictFiberLandingIso
  rw [Iso.trans_hom, Category.assoc, strictFiberClosedTopIso_hom_snd]
  change cgwhToTop.map (strictFiberClosedIso f b).hom ≫
      cgwhToTop.map
        (point_isTerminal.from
          (closedSubspace E (strictFiberClosedSet f b))) = _
  rw [
    ← cgwhToTop.map_comp, hNative]

private theorem strictFiberLandingIso_hom_eq_pullbackComparison
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    (strictFiberLandingIso f b).hom =
      pullbackComparison cgwhToTop f b := by
  apply pullback.hom_ext
  · rw [strictFiberLandingIso_hom_fst,
      pullbackComparison_comp_fst]
  · rw [strictFiberLandingIso_hom_snd,
      pullbackComparison_comp_snd]

/-- The landing isomorphism is strictly natural for source-first maps of
based arrows. -/
theorem strictFiberLandingIso_naturality
    {E B E' B' : CGWH.{u, v}}
    {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    (eMap : E ⟶ E') (bMap : B ⟶ B')
    (hf : eMap ≫ f' = f ≫ bMap)
    (hb : b ≫ bMap = b') :
    cgwhToTop.map (strictFiberMap eMap bMap hf hb) ≫
        (strictFiberLandingIso f' b').hom =
      (strictFiberLandingIso f b).hom ≫
        pullback.map
          (cgwhToTop.map f) (cgwhToTop.map b)
          (cgwhToTop.map f') (cgwhToTop.map b')
          (cgwhToTop.map eMap) (𝟙 _) (cgwhToTop.map bMap)
          (by
            simpa only [← cgwhToTop.map_comp] using
              congrArg cgwhToTop.map hf.symm)
          (by
            simpa only [← cgwhToTop.map_comp, Category.id_comp] using
              congrArg cgwhToTop.map hb) := by
  let rawMap :=
    pullback.map
      (cgwhToTop.map f) (cgwhToTop.map b)
      (cgwhToTop.map f') (cgwhToTop.map b')
      (cgwhToTop.map eMap) (𝟙 _) (cgwhToTop.map bMap)
      (by
        simpa only [← cgwhToTop.map_comp] using
          congrArg cgwhToTop.map hf.symm)
      (by
        simpa only [← cgwhToTop.map_comp, Category.id_comp] using
          congrArg cgwhToTop.map hb)
  have hRawFst : rawMap ≫
        pullback.fst (cgwhToTop.map f') (cgwhToTop.map b') =
      pullback.fst (cgwhToTop.map f) (cgwhToTop.map b) ≫
        cgwhToTop.map eMap :=
    pullback.lift_fst _ _ _
  have hRawSnd : rawMap ≫
        pullback.snd (cgwhToTop.map f') (cgwhToTop.map b') =
      pullback.snd (cgwhToTop.map f) (cgwhToTop.map b) := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd, Category.comp_id]
  change cgwhToTop.map (strictFiberMap eMap bMap hf hb) ≫
      (strictFiberLandingIso f' b').hom =
    (strictFiberLandingIso f b).hom ≫ rawMap
  apply pullback.hom_ext
  · calc
      (cgwhToTop.map (strictFiberMap eMap bMap hf hb) ≫
          (strictFiberLandingIso f' b').hom) ≫
          pullback.fst (cgwhToTop.map f') (cgwhToTop.map b') =
        cgwhToTop.map (strictFiberMap eMap bMap hf hb) ≫
          cgwhToTop.map (strictFiberToTotal f' b') := by
            rw [Category.assoc, strictFiberLandingIso_hom_fst]
      _ = cgwhToTop.map
          (strictFiberMap eMap bMap hf hb ≫
            strictFiberToTotal f' b') := by
            rw [cgwhToTop.map_comp]
      _ = cgwhToTop.map (strictFiberToTotal f b ≫ eMap) := by
            rw [strictFiberMap_toTotal]
      _ = cgwhToTop.map (strictFiberToTotal f b) ≫
          cgwhToTop.map eMap := cgwhToTop.map_comp _ _
      _ = ((strictFiberLandingIso f b).hom ≫
          pullback.fst (cgwhToTop.map f) (cgwhToTop.map b)) ≫
          cgwhToTop.map eMap := by
            rw [strictFiberLandingIso_hom_fst]
      _ = (strictFiberLandingIso f b).hom ≫
          (pullback.fst (cgwhToTop.map f) (cgwhToTop.map b) ≫
            cgwhToTop.map eMap) := Category.assoc _ _ _
      _ = (strictFiberLandingIso f b).hom ≫
          (rawMap ≫
            pullback.fst (cgwhToTop.map f') (cgwhToTop.map b')) := by
            rw [hRawFst]
      _ = ((strictFiberLandingIso f b).hom ≫ rawMap) ≫
          pullback.fst (cgwhToTop.map f') (cgwhToTop.map b') :=
            (Category.assoc _ _ _).symm
  · calc
      (cgwhToTop.map (strictFiberMap eMap bMap hf hb) ≫
          (strictFiberLandingIso f' b').hom) ≫
          pullback.snd (cgwhToTop.map f') (cgwhToTop.map b') =
        cgwhToTop.map (strictFiberMap eMap bMap hf hb) ≫
          cgwhToTop.map (strictFiberToPoint f' b') := by
            rw [Category.assoc, strictFiberLandingIso_hom_snd]
      _ = cgwhToTop.map
          (strictFiberMap eMap bMap hf hb ≫
            strictFiberToPoint f' b') := by
            rw [cgwhToTop.map_comp]
      _ = cgwhToTop.map (strictFiberToPoint f b) := by
            rw [strictFiberMap_toPoint]
      _ = (strictFiberLandingIso f b).hom ≫
          pullback.snd (cgwhToTop.map f) (cgwhToTop.map b) :=
            (strictFiberLandingIso_hom_snd f b).symm
      _ = (strictFiberLandingIso f b).hom ≫
          (rawMap ≫
            pullback.snd (cgwhToTop.map f') (cgwhToTop.map b')) := by
            rw [hRawSnd]
      _ = ((strictFiberLandingIso f b).hom ≫ rawMap) ≫
          pullback.snd (cgwhToTop.map f') (cgwhToTop.map b') :=
            (Category.assoc _ _ _).symm

/-- Dropping the unique point-coordinate identifies the pullback subtype with the
literal point fiber; the inverse inserts that same point-coordinate. -/
noncomputable def pullbackPointFiberHomeomorph
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    {q : E × PUnit.{v + 1} //
        (CGWH.cgwhToTop.map p) q.fst =
          (CGWH.cgwhToTop.map b) q.snd} ≃ₜ
      TopCat.pointFiber (CGWH.cgwhToTop.map p)
        ((CGWH.cgwhToTop.map b) PUnit.unit) where
  toFun q := by
    have hp : q.val.snd = PUnit.unit := Subsingleton.elim _ _
    exact ⟨q.val.fst, q.property.trans (congrArg b hp)⟩
  invFun x := ⟨(x.1, PUnit.unit), x.2⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _

/-- The ordinary topological pullback over the specified point is isomorphic to
the literal point fiber. -/
noncomputable def pullbackPointFiberIso
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    pullback (CGWH.cgwhToTop.map p) (CGWH.cgwhToTop.map b) ≅
      TopCat.of (TopCat.pointFiber (CGWH.cgwhToTop.map p)
        ((CGWH.cgwhToTop.map b) PUnit.unit)) :=
  TopCat.pullbackIsoProdSubtype
      (CGWH.cgwhToTop.map p) (CGWH.cgwhToTop.map b) ≪≫
    TopCat.isoOfHomeo (pullbackPointFiberHomeomorph p b)

/-- Forgetting the chosen CGWH strict fiber gives its literal topological point fiber. -/
noncomputable def strictFiberPointFiberIso
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    CGWH.cgwhToTop.obj (CGWH.strictFiber p b) ≅
      TopCat.of (TopCat.pointFiber (CGWH.cgwhToTop.map p)
        ((CGWH.cgwhToTop.map b) PUnit.unit)) :=
  CGWH.strictFiberLandingIso p b ≪≫ pullbackPointFiberIso p b

/-- The forward comparison retains the strict fiber's total-space projection. -/
theorem strictFiberPointFiberIso_hom_val
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) (x : CGWH.strictFiber p b) :
    ((strictFiberPointFiberIso p b).hom x).1 =
      (CGWH.cgwhToTop.map (CGWH.strictFiberToTotal p b)) x := by
  change pullback.fst (CGWH.cgwhToTop.map p) (CGWH.cgwhToTop.map b)
      ((CGWH.strictFiberLandingIso p b).hom x) = _
  exact ConcreteCategory.congr_hom
    (CGWH.strictFiberLandingIso_hom_fst p b) x

/-- The forward comparison sends the specified strict-fiber point to its original
total-space point, with the supplied equation over the base. -/
theorem strictFiberPointFiberIso_hom_point
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b) :
    (strictFiberPointFiberIso p b).hom
        (CGWH.pointHomEquiv (CGWH.strictFiber p b)
          (CGWH.strictFiberPoint p b e over)) =
      (⟨CGWH.pointHomEquiv E e,
        (by
          change p (e PUnit.unit) = b PUnit.unit
          have h := ConcreteCategory.congr_hom over PUnit.unit
          change p (e PUnit.unit) = b PUnit.unit at h
          exact h)⟩ :
        TopCat.pointFiber (CGWH.cgwhToTop.map p)
          (CGWH.pointHomEquiv B b)) := by
  apply Subtype.ext
  rw [strictFiberPointFiberIso_hom_val]
  change CGWH.strictFiberToTotal p b
      (CGWH.strictFiberPoint p b e over PUnit.unit) = e PUnit.unit
  have h := ConcreteCategory.congr_hom
    (CGWH.strictFiberPoint_toTotal p b e over) PUnit.unit
  change CGWH.strictFiberToTotal p b
      (CGWH.strictFiberPoint p b e over PUnit.unit) = e PUnit.unit at h
  exact h

/-- The inverse comparison retains the same total-space projection. -/
theorem strictFiberPointFiberIso_inv_val {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (x : {x : CGWH.cgwhToTop.obj E //
      (CGWH.cgwhToTop.map p) x = CGWH.pointHomEquiv B b}) :
    (CGWH.cgwhToTop.map (CGWH.strictFiberToTotal p b))
      ((strictFiberPointFiberIso p b).inv x) = x.1 := by
  have hVal := strictFiberPointFiberIso_hom_val p b ((strictFiberPointFiberIso p b).inv x)
  have h := ConcreteCategory.congr_hom (strictFiberPointFiberIso p b).inv_hom_id x
  exact hVal.symm.trans (congrArg Subtype.val h)

/-- The specified original native strict-fiber point maps to its original
total-space point in the raw point fiber. -/
theorem strictFiberPointFiberIso_hom_point_val {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b) :
    ((strictFiberPointFiberIso p b).hom (CGWH.pointHomEquiv (CGWH.strictFiber p b)
      (CGWH.strictFiberPoint p b e over))).1 = CGWH.pointHomEquiv E e := by
  rw [strictFiberPointFiberIso_hom_val]
  exact ConcreteCategory.congr_hom (CGWH.strictFiberPoint_toTotal p b e over) PUnit.unit

end CGWH
