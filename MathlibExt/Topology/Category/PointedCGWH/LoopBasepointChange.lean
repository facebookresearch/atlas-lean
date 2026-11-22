/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.Repointing
import MathlibExt.Topology.Category.PointedCGWH.LoopComparison
import MathlibExt.Topology.Homotopy.LoopBasepointChange
import MathlibExt.Topology.Homotopy.WeaklyPointedHomotopyRel
import MathlibExt.Topology.Compactness.CompactlyGeneratedProduct

/-!
# Basepoint change for native pointed CGWH loops

Path conjugation gives carrier maps between native loop objects based at
different points.  These maps are homotopy equivalences and are weakly
pointed, but they do not preserve the constant loop strictly in general.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap

namespace PointedCGWH

private noncomputable def NativeLoopAt
    (B : CGWH.{u, v}) (b : B) : CGWH.{u, v} :=
  (PointedCGWH.loop.obj (pointedAt B b)).right

private def RawLoopAt (B : CGWH.{u, v}) (b : B) : TopCat.{v} :=
  TopCat.of (LoopSpace B b)

private noncomputable def CoreLoopAt
    (B : CGWH.{u, v}) (b : B) : CGWH.{u, v} :=
  (PointedCGWH.compactOpenLoopCoreflection.obj
    (pointedAt B b)).right

/-- The native loop carrier based at an arbitrary point. -/
noncomputable abbrev loopAt (B : CGWH.{u, v}) (b : B) : CGWH.{u, v} :=
  NativeLoopAt B b

private noncomputable def loopLandingAt
    (B : CGWH.{u, v}) (b : B) :
    C(NativeLoopAt B b, RawLoopAt B b) :=
  ConcreteCategory.hom
    (PointedCGWH.loopLanding (pointedAt B b))

private noncomputable def rawStrictLoopAtMap
    {B C : CGWH.{u, v}} (f : B ⟶ C) (b : B) :
    C(RawLoopAt B b, RawLoopAt C (f b)) :=
  ContinuousMap.strictLoopMap
    (ConcreteCategory.hom f : C(B, C)) b

/-- Strict postcomposition on native loops based at an arbitrary point. -/
noncomputable def loopAtMap {B C : CGWH.{u, v}} (f : B ⟶ C) (b : B) :
    loopAt B b ⟶ loopAt C (f b) :=
  (PointedCGWH.loop.map (pointedAtMap f b (f b) rfl)).right

/-- Landing a strict native loop map gives ordinary strict
postcomposition. -/
theorem loopAtMap_landing {B C : CGWH.{u, v}} (f : B ⟶ C) (b : B)
    (gamma : loopAt B b) :
    loopLandingAt C (f b) (loopAtMap f b gamma) =
      rawStrictLoopAtMap f b (loopLandingAt B b gamma) := by
  have h := ConcreteCategory.congr_hom
    (PointedCGWH.loopLanding_naturality (pointedAtMap f b (f b) rfl)) gamma
  change PointedCGWH.loopLanding (pointedAt C (f b))
      (loopAtMap f b gamma) =
    PointedCGWH.strictLoopMap (pointedAtMap f b (f b) rfl)
      (PointedCGWH.loopLanding (pointedAt B b) gamma) at h
  have hs : PointedCGWH.strictLoopMap (pointedAtMap f b (f b) rfl) =
      rawStrictLoopAtMap f b := by
    apply ContinuousMap.ext
    intro delta
    apply Path.ext
    funext t
    rfl
  exact h.trans (congrArg
    (fun k => k (loopLandingAt B b gamma)) hs)

private noncomputable def loopAtComparisonIso
    (B : CGWH.{u, v}) (b : B) :
    loopAt B b ≅ CoreLoopAt B b :=
  (Under.forget CGWH.point.{u, v}).mapIso
    (PointedCGWH.loopIsoCompactOpenCoreflection.app (pointedAt B b))

private noncomputable def loopAtComparisonHomeomorph
    (B : CGWH.{u, v}) (b : B) :
    NativeLoopAt B b ≃ₜ CoreLoopAt B b :=
  TopCat.homeoOfIso
    (CGWH.cgwhToTop.mapIso (loopAtComparisonIso B b))

private noncomputable def coreflectedLoopBasepointChange
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    CoreLoopAt B x ⟶ CoreLoopAt B y :=
  CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage (by
    change
      TopCat.toCompactlyGenerated.{u, v}.obj
          (TopCat.of (LoopSpace B x)) ⟶
        TopCat.toCompactlyGenerated.{u, v}.obj
          (TopCat.of (LoopSpace B y))
    exact TopCat.toCompactlyGenerated.{u, v}.map
      (TopCat.ofHom (ContinuousMap.loopBasepointChange p)))

private theorem coreflectedLoopBasepointChange_apply
    (B : CGWH.{u, v}) {x y : B} (p : Path x y)
    (gamma : CoreLoopAt B x) :
    coreflectedLoopBasepointChange B p gamma =
      ContinuousMap.loopBasepointChange p gamma := by
  let gC :
      CGWH.cgwhToCompactlyGenerated.obj
          (PointedCGWH.compactOpenLoopCoreflection.obj
            (pointedAt B x)).right ⟶
        CGWH.cgwhToCompactlyGenerated.obj
          (PointedCGWH.compactOpenLoopCoreflection.obj
            (pointedAt B y)).right := by
    change
      TopCat.toCompactlyGenerated.{u, v}.obj
          (TopCat.of (LoopSpace B x)) ⟶
        TopCat.toCompactlyGenerated.{u, v}.obj
          (TopCat.of (LoopSpace B y))
    exact TopCat.toCompactlyGenerated.{u, v}.map
      (TopCat.ofHom (ContinuousMap.loopBasepointChange p))
  have h := ConcreteCategory.congr_hom
    (CGWH.fullyFaithfulCgwhToCompactlyGenerated.map_preimage gC) gamma
  change coreflectedLoopBasepointChange B p gamma =
    ContinuousMap.loopBasepointChange p gamma
  exact h

private theorem loopLandingAt_comparison
    (B : CGWH.{u, v}) (b : B) (gamma : NativeLoopAt B b) :
    loopLandingAt B b gamma =
      loopAtComparisonHomeomorph B b gamma :=
  CompactlyGenerated.adjCounit_apply _ _

private noncomputable def rawLoopBasepointChangeAt
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    C(RawLoopAt B x, RawLoopAt B y) :=
  ContinuousMap.loopBasepointChange p

private def HasLoopBasepointChangeLanding
    (B : CGWH.{u, v}) (x y : B) (p : Path x y)
    (f : NativeLoopAt B x ⟶ NativeLoopAt B y) : Prop :=
  ∀ gamma : NativeLoopAt B x,
    loopLandingAt B y
        ((ConcreteCategory.hom f :
          C(NativeLoopAt B x, NativeLoopAt B y)) gamma) =
      rawLoopBasepointChangeAt B p
        (loopLandingAt B x gamma)

/-- Change the basepoint of a native loop by conjugation in the order
path inverse, loop, path.  This is a carrier map, not generally a pointed
morphism. -/
noncomputable def loopBasepointChange
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    NativeLoopAt B x ⟶ NativeLoopAt B y :=
  (loopAtComparisonIso B x).hom ≫
    coreflectedLoopBasepointChange B p ≫
      (loopAtComparisonIso B y).inv

private theorem loopBasepointChange_apply_core
    (B : CGWH.{u, v}) {x y : B} (p : Path x y)
    (gamma : NativeLoopAt B x) :
    loopBasepointChange B p gamma =
      (loopAtComparisonHomeomorph B y).symm
        (coreflectedLoopBasepointChange B p
          (loopAtComparisonHomeomorph B x gamma)) :=
  rfl

private theorem loopBasepointChange_hasLanding
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    HasLoopBasepointChangeLanding B x y p
      (loopBasepointChange B p) := by
  unfold HasLoopBasepointChangeLanding
  intro gamma
  rw [loopBasepointChange_apply_core,
    loopLandingAt_comparison, loopLandingAt_comparison]
  rw [Homeomorph.apply_symm_apply]
  exact coreflectedLoopBasepointChange_apply B p
    (loopAtComparisonHomeomorph B x gamma)

/-- Native basepoint change lands as literal compact-open conjugation. -/
@[simp]
theorem loopBasepointChange_landing
    (B : CGWH.{u, v}) {x y : B} (p : Path x y)
    (gamma : NativeLoopAt B x) :
    loopLandingAt B y
        ((ConcreteCategory.hom (loopBasepointChange B p) :
          C(NativeLoopAt B x, NativeLoopAt B y)) gamma) =
      ContinuousMap.loopBasepointChange p
        (loopLandingAt B x gamma) := by
  change loopLandingAt B y
      ((ConcreteCategory.hom (loopBasepointChange B p) :
        C(NativeLoopAt B x, NativeLoopAt B y)) gamma) =
    rawLoopBasepointChangeAt B p (loopLandingAt B x gamma)
  exact loopBasepointChange_hasLanding B p gamma

private theorem loopLanding_injective
    (B : CGWH.{u, v}) (b : B) :
    Function.Injective (loopLandingAt B b) := by
  intro a c h
  let e := loopAtComparisonHomeomorph B b
  have ha : loopLandingAt B b a = e a :=
    loopLandingAt_comparison B b a
  have hc : loopLandingAt B b c = e c :=
    loopLandingAt_comparison B b c
  exact e.injective (ha.symm.trans (h.trans hc))

private noncomputable def rawLoopJoinedPath
    (B : CGWH.{u, v}) (b : B)
    {alpha beta : NativeLoopAt B b}
    (h : (loopLandingAt B b alpha).Homotopic
      (loopLandingAt B b beta)) :
    Path alpha beta := by
  let H := h.some
  let Raw := RawLoopAt B b
  let rawPath : C(unitInterval, Raw) :=
    { toFun := H.eval
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        exact H.continuous }
  let down : C(ULift.{v} unitInterval, unitInterval) :=
    ⟨ULift.down, continuous_uliftDown⟩
  let rawPathUp : C(ULift.{v} unitInterval, Raw) :=
    rawPath.comp down
  let D : CompactlyGenerated.{u, v} :=
    CompactlyGenerated.of (ULift.{v} unitInterval)
  let lifted : D ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw :=
    CompactlyGenerated.adj.{u, v}.homEquiv D Raw
      (TopCat.ofHom rawPathUp)
  let liftedCore : D ⟶
      CGWH.cgwhToCompactlyGenerated.obj (CoreLoopAt B b) := by
    change D ⟶ TopCat.toCompactlyGenerated.{u, v}.obj Raw
    exact lifted
  let e := loopAtComparisonIso B b
  let nativeC : D ⟶
      CGWH.cgwhToCompactlyGenerated.obj (NativeLoopAt B b) :=
    liftedCore ≫ CGWH.cgwhToCompactlyGenerated.map e.inv
  let nativeTop :=
    CompactlyGenerated.compactlyGeneratedToTop.map nativeC
  let up : C(unitInterval, ULift.{v} unitInterval) :=
    ⟨ULift.up, continuous_uliftUp⟩
  let q : C(unitInterval, NativeLoopAt B b) :=
    nativeTop.hom.comp up
  have hLift :=
    (CompactlyGenerated.adj.{u, v}.homEquiv D Raw).symm_apply_apply
      (TopCat.ofHom rawPathUp)
  rw [CompactlyGenerated.adj.{u, v}.homEquiv_counit] at hLift
  have hLanding (s : unitInterval) :
      loopLandingAt B b (q s) = H.eval s := by
    let z : CoreLoopAt B b := liftedCore (ULift.up s)
    have hq : q s = (loopAtComparisonHomeomorph B b).symm z := rfl
    rw [hq, loopLandingAt_comparison,
      Homeomorph.apply_symm_apply]
    change lifted (ULift.up s) = H.eval s
    have hs := ConcreteCategory.congr_hom hLift (ULift.up s)
    change CompactlyGenerated.adj.{u, v}.counit.app Raw
        (lifted (ULift.up s)) = rawPathUp (ULift.up s) at hs
    exact (CompactlyGenerated.adjCounit_apply.{v, u} Raw
      (lifted (ULift.up s))).symm.trans hs
  exact
    { toFun := q
      continuous_toFun := q.continuous
      source' := by
        apply loopLanding_injective B b
        rw [hLanding]
        simpa only [RawLoopAt] using H.eval_zero
      target' := by
        apply loopLanding_injective B b
        rw [hLanding]
        simpa only [RawLoopAt] using H.eval_one }

private theorem liftRawLoopJoined
    (B : CGWH.{u, v}) (b : B)
    {alpha beta : NativeLoopAt B b}
    (h : (loopLandingAt B b alpha).Homotopic
      (loopLandingAt B b beta)) :
    Joined alpha beta :=
  ⟨rawLoopJoinedPath B b h⟩

private theorem liftRawLoopJoinedFor
    (X : PointedCGWH.{u, v})
    {alpha beta : (PointedCGWH.loop.obj X).right}
    (h : (PointedCGWH.loopLanding X alpha).Homotopic
      (PointedCGWH.loopLanding X beta)) :
    Joined alpha beta := by
  let e := pointedAtBasepointIso X
  let le := PointedCGWH.loop.mapIso e
  have hLanding (gamma : (PointedCGWH.loop.obj X).right) :
      loopLandingAt X.right (basepoint X) (le.inv.right gamma) =
        PointedCGWH.loopLanding X gamma := by
    have hn := ConcreteCategory.congr_hom
      (PointedCGWH.loopLanding_naturality e.inv) gamma
    change loopLandingAt X.right (basepoint X) (le.inv.right gamma) =
      PointedCGWH.strictLoopMap e.inv
        (PointedCGWH.loopLanding X gamma) at hn
    calc
      _ = PointedCGWH.strictLoopMap e.inv
          (PointedCGWH.loopLanding X gamma) := hn
      _ = _ := by
        apply Path.ext
        funext t
        rw [PointedCGWH.strictLoopMap_apply]
        rfl
  have hAt :
      (loopLandingAt X.right (basepoint X)
          (le.inv.right alpha)).Homotopic
        (loopLandingAt X.right (basepoint X)
          (le.inv.right beta)) := by
    rw [hLanding, hLanding]
    exact h
  let j := (liftRawLoopJoined X.right (basepoint X) hAt).somePath
  let j' := j.map (ConcreteCategory.hom le.hom.right).continuous
  have ha : le.hom.right (le.inv.right alpha) = alpha := by
    have h := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right le.inv_hom_id) alpha
    simpa only [Under.comp_right, Under.id_right,
      ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  have hb : le.hom.right (le.inv.right beta) = beta := by
    have h := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right le.inv_hom_id) beta
    simpa only [Under.comp_right, Under.id_right,
      ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  exact ⟨j'.cast ha.symm hb.symm⟩

private noncomputable def coreLoopLandingAt
    (B : CGWH.{u, v}) (b : B) :
    C(CoreLoopAt B b, RawLoopAt B b) :=
  (CompactlyGenerated.adj.{u, v}.counit.app (RawLoopAt B b)).hom

private theorem coreLoopLandingAt_apply
    (B : CGWH.{u, v}) (b : B) (gamma : CoreLoopAt B b) :
    coreLoopLandingAt B b gamma = gamma :=
  CompactlyGenerated.adjCounit_apply.{v, u} _ _

private noncomputable def coreflectedLoopHomotopy
    (B : CGWH.{u, v}) {a b : B}
    {fRaw gRaw : C(RawLoopAt B a, RawLoopAt B b)}
    {fNative gNative : C(CoreLoopAt B a, CoreLoopAt B b)}
    (H : fRaw.Homotopy gRaw)
    (hf : ∀ gamma, fNative gamma =
      fRaw (coreLoopLandingAt B a gamma))
    (hg : ∀ gamma, gNative gamma =
      gRaw (coreLoopLandingAt B a gamma)) :
    fNative.Homotopy gNative := by
  let hCore : UCompactlyGeneratedSpace.{u}
      (CoreLoopAt B a) :=
    (CoreLoopAt B a).toCompactlyGenerated.is_compactly_generated
  letI : UCompactlyGeneratedSpace.{u}
      (unitInterval × CoreLoopAt B a) :=
    @uCompactlyGeneratedSpace_prod_of_locallyCompact_left
      (A := unitInterval) (B := CoreLoopAt B a)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance hCore
  let D : CompactlyGenerated.{u, v} :=
    CompactlyGenerated.of (unitInterval × CoreLoopAt B a)
  let pre : C(unitInterval × CoreLoopAt B a,
      unitInterval × RawLoopAt B a) :=
    (ContinuousMap.id unitInterval).prodMap (coreLoopLandingAt B a)
  let rawH : C(unitInterval × CoreLoopAt B a, RawLoopAt B b) :=
    H.toContinuousMap.comp pre
  let lifted : D ⟶
      TopCat.toCompactlyGenerated.{u, v}.obj (RawLoopAt B b) :=
    CompactlyGenerated.adj.{u, v}.homEquiv D (RawLoopAt B b)
      (TopCat.ofHom rawH)
  let liftedCore : D ⟶
      CGWH.cgwhToCompactlyGenerated.obj (CoreLoopAt B b) := by
    change D ⟶ TopCat.toCompactlyGenerated.{u, v}.obj (RawLoopAt B b)
    exact lifted
  let nativeTop :=
    CompactlyGenerated.compactlyGeneratedToTop.map liftedCore
  let m : C(unitInterval × CoreLoopAt B a, CoreLoopAt B b) :=
    nativeTop.hom
  have hLift :=
    (CompactlyGenerated.adj.{u, v}.homEquiv
      D (RawLoopAt B b)).symm_apply_apply (TopCat.ofHom rawH)
  rw [CompactlyGenerated.adj.{u, v}.homEquiv_counit] at hLift
  have hValue (z : unitInterval × CoreLoopAt B a) :
      m z = H (z.1, coreLoopLandingAt B a z.2) := by
    change lifted z = rawH z
    have hz := ConcreteCategory.congr_hom hLift z
    change CompactlyGenerated.adj.{u, v}.counit.app (RawLoopAt B b)
        (lifted z) = rawH z at hz
    exact (CompactlyGenerated.adjCounit_apply.{v, u}
      (RawLoopAt B b) (lifted z)).symm.trans hz
  exact
    { toContinuousMap := m
      map_zero_left := fun gamma =>
        (hValue (0, gamma)).trans
          ((H.map_zero_left
            (coreLoopLandingAt B a gamma)).trans (hf gamma).symm)
      map_one_left := fun gamma =>
        (hValue (1, gamma)).trans
          ((H.map_one_left
            (coreLoopLandingAt B a gamma)).trans (hg gamma).symm) }

private noncomputable def coreflectedLoopBasepointChangeHomotopyEquiv
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    CoreLoopAt B x ≃ₕ CoreLoopAt B y := by
  let eRaw := ContinuousMap.loopBasepointChangeHomotopyEquiv p
  let f : C(CoreLoopAt B x, CoreLoopAt B y) :=
    ConcreteCategory.hom (coreflectedLoopBasepointChange B p)
  let g : C(CoreLoopAt B y, CoreLoopAt B x) :=
    ConcreteCategory.hom (coreflectedLoopBasepointChange B p.symm)
  refine
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_ }
  · rcases eRaw.left_inv with ⟨H⟩
    refine ⟨coreflectedLoopHomotopy B H ?_ ?_⟩
    · intro gamma
      change coreflectedLoopBasepointChange B p.symm
          (coreflectedLoopBasepointChange B p gamma) =
        eRaw.invFun
          (eRaw.toFun (coreLoopLandingAt B x gamma))
      rw [coreflectedLoopBasepointChange_apply,
        coreflectedLoopBasepointChange_apply,
        coreLoopLandingAt_apply]
      rfl
    · intro gamma
      change gamma =
        ContinuousMap.id (RawLoopAt B x)
          (coreLoopLandingAt B x gamma)
      rw [coreLoopLandingAt_apply]
      rfl
  · rcases eRaw.right_inv with ⟨H⟩
    refine ⟨coreflectedLoopHomotopy B H ?_ ?_⟩
    · intro gamma
      change coreflectedLoopBasepointChange B p
          (coreflectedLoopBasepointChange B p.symm gamma) =
        eRaw.toFun
          (eRaw.invFun (coreLoopLandingAt B y gamma))
      rw [coreflectedLoopBasepointChange_apply,
        coreflectedLoopBasepointChange_apply,
        coreLoopLandingAt_apply]
      rfl
    · intro gamma
      change gamma =
        ContinuousMap.id (RawLoopAt B y)
          (coreLoopLandingAt B y gamma)
      rw [coreLoopLandingAt_apply]
      rfl

/-- Native basepoint change is a genuine homotopy equivalence. -/
noncomputable def loopBasepointChangeHomotopyEquiv
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    (loopAt B x : Type v) ≃ₕ (loopAt B y : Type v) :=
  (loopAtComparisonHomeomorph B x).toHomotopyEquiv |>.trans
    (coreflectedLoopBasepointChangeHomotopyEquiv B p) |>.trans
      (loopAtComparisonHomeomorph B y).symm.toHomotopyEquiv

/-- The forward map of native basepoint change is the carrier
conjugation map. -/
@[simp]
theorem loopBasepointChangeHomotopyEquiv_toFun
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    (loopBasepointChangeHomotopyEquiv B p).toFun =
      (ConcreteCategory.hom (loopBasepointChange B p) :
        C(loopAt B x, loopAt B y)) :=
  rfl

/-- The inverse map is native conjugation along the reversed path. -/
@[simp]
theorem loopBasepointChangeHomotopyEquiv_invFun
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    (loopBasepointChangeHomotopyEquiv B p).invFun =
      (ConcreteCategory.hom (loopBasepointChange B p.symm) :
        C(loopAt B y, loopAt B x)) :=
  rfl

/-- Conjugation sends the constant loop to a loop joined to the constant
loop at the new basepoint. -/
theorem loopBasepointChange_basepoint_joined
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    Joined
      (loopBasepointChange B p
        (PointedCGWH.basepoint
          (PointedCGWH.loop.obj (pointedAt B x))))
      (PointedCGWH.basepoint
        (PointedCGWH.loop.obj (pointedAt B y))) := by
  let sx : NativeLoopAt B x :=
    PointedCGWH.basepoint
      (PointedCGWH.loop.obj (pointedAt B x))
  let sy : NativeLoopAt B y :=
    PointedCGWH.basepoint
      (PointedCGWH.loop.obj (pointedAt B y))
  change Joined (loopBasepointChange B p sx) sy
  apply liftRawLoopJoined B y
  have hx : loopLandingAt B x sx = Path.refl x := by
    change PointedCGWH.loopLanding (pointedAt B x)
        ((PointedCGWH.loop.obj (pointedAt B x)).hom PUnit.unit) =
      Path.refl (basepoint (pointedAt B x))
    exact PointedCGWH.loopLanding_basepoint (pointedAt B x)
  have hy : loopLandingAt B y sy = Path.refl y := by
    change PointedCGWH.loopLanding (pointedAt B y)
        ((PointedCGWH.loop.obj (pointedAt B y)).hom PUnit.unit) =
      Path.refl (basepoint (pointedAt B y))
    exact PointedCGWH.loopLanding_basepoint (pointedAt B y)
  rw [loopBasepointChange_landing, hx, hy]
  change
    (p.symm.trans ((Path.refl x).trans p)).Homotopic
      (Path.refl y)
  exact
    ((Path.Homotopic.refl p.symm).hcomp
      (Path.Homotopic.refl_trans p)).trans
        (Path.Homotopic.symm_trans p)

/-- Basepoint change along the reflexive path is pointwise joined to the
identity. -/
theorem loopBasepointChange_refl_joined
    (B : CGWH.{u, v}) (x : B) (gamma : loopAt B x) :
    Joined
      (loopBasepointChange B (Path.refl x) gamma)
      gamma := by
  apply liftRawLoopJoined B x
  rw [loopBasepointChange_landing]
  let delta := loopLandingAt B x gamma
  change
    ((Path.refl x).symm.trans
      (delta.trans (Path.refl x))).Homotopic delta
  have hsymm : (Path.refl x).symm = Path.refl x := by
    apply Path.ext
    rfl
  rw [hsymm]
  exact
    (Path.Homotopic.refl_trans
      (delta.trans (Path.refl x))).trans
        (Path.Homotopic.trans_refl delta)

/-- Changing along a path and then along its reverse is pointwise joined
to the identity. -/
theorem loopBasepointChange_symm_left_joined
    (B : CGWH.{u, v}) {x y : B} (p : Path x y)
    (gamma : loopAt B x) :
    Joined
      (loopBasepointChange B p.symm
        (loopBasepointChange B p gamma))
      gamma := by
  let e := loopBasepointChangeHomotopyEquiv B p
  exact ⟨e.left_inv.some.evalAt gamma⟩

/-- Changing along a reversed path and then along the original path is
pointwise joined to the identity. -/
theorem loopBasepointChange_symm_right_joined
    (B : CGWH.{u, v}) {x y : B} (p : Path x y)
    (delta : loopAt B y) :
    Joined
      (loopBasepointChange B p
        (loopBasepointChange B p.symm delta))
      delta := by
  let e := loopBasepointChangeHomotopyEquiv B p
  exact ⟨e.right_inv.some.evalAt delta⟩

/-- Basepoint change along concatenated paths agrees pointwise, up to a
path, with the composite basepoint changes. -/
theorem loopBasepointChange_trans_joined
    (B : CGWH.{u, v}) {x y z : B} (p : Path x y) (q : Path y z)
    (gamma : loopAt B x) :
    Joined
      (loopBasepointChange B q
        (loopBasepointChange B p gamma))
      (loopBasepointChange B (p.trans q) gamma) := by
  apply liftRawLoopJoined B z
  rw [loopBasepointChange_landing, loopBasepointChange_landing,
    loopBasepointChange_landing]
  let fp : ContinuousMap.WeaklyPointed x y :=
    { hom := ContinuousMap.id B
      rootPath := p }
  let gq : ContinuousMap.WeaklyPointed y z :=
    { hom := ContinuousMap.id B
      rootPath := q }
  have h :=
    ContinuousMap.WeaklyPointed.loopMap_comp_homotopic
      fp gq (loopLandingAt B x gamma)
  convert h.symm using 1 <;> apply Path.ext <;> rfl

/-- Basepoint change is strictly natural under an ordinary CGWH map. -/
theorem loopBasepointChange_naturality
    {B C : CGWH.{u, v}} (f : B ⟶ C) {x y : B}
    (p : Path x y) :
    loopBasepointChange B p ≫ loopAtMap f y =
      loopAtMap f x ≫
        loopBasepointChange C
          (p.map (ConcreteCategory.hom f : C(B, C)).continuous) := by
  apply ConcreteCategory.hom_ext
  intro gamma
  apply loopLanding_injective C (f y)
  simp only [ConcreteCategory.comp_apply]
  rw [loopAtMap_landing, loopBasepointChange_landing,
    loopBasepointChange_landing, loopAtMap_landing]
  let delta : LoopSpace B x := loopLandingAt B x gamma
  let cf : C(B, C) := ConcreteCategory.hom f
  have hmap :
      (p.symm.trans (delta.trans p)).map cf.continuous =
        (p.map cf.continuous).symm.trans
          ((delta.map cf.continuous).trans
            (p.map cf.continuous)) := by
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
  calc
    _ = (ContinuousMap.loopBasepointChange p delta).map cf.continuous := by
      apply Path.ext
      rfl
    _ = ContinuousMap.loopBasepointChange
        (p.map cf.continuous) (delta.map cf.continuous) := by
      exact hmap
    _ = _ := by
      apply Path.ext
      rfl

/-- Homotopic basepoint paths induce pointwise joined native loop maps. -/
theorem loopBasepointChange_homotopic_joined
    (B : CGWH.{u, v}) {x y : B} {p q : Path x y}
    (hp : p.Homotopic q) (gamma : loopAt B x) :
    Joined
      (loopBasepointChange B p gamma)
      (loopBasepointChange B q gamma) := by
  apply liftRawLoopJoined B y
  rw [loopBasepointChange_landing, loopBasepointChange_landing]
  exact hp.symm₂.hcomp ((Path.Homotopic.refl _).hcomp hp)

/-- A native CGWH carrier map equipped with a chosen path from the image of
the source point to the target point. -/
structure WeaklyPointedMap
    (X Y : PointedCGWH.{u, v}) where
  /-- The underlying native CGWH map. -/
  hom : X.right ⟶ Y.right
  /-- The chosen path from the mapped source point to the target point. -/
  rootPath : Path (hom (basepoint X)) (basepoint Y)

namespace WeaklyPointedMap

variable {X Y Z : PointedCGWH.{u, v}}

/-- Forget a native weakly pointed map to the raw continuous-map packet. -/
def toContinuousMap (f : WeaklyPointedMap X Y) :
    ContinuousMap.WeaklyPointed (basepoint X) (basepoint Y) where
  hom := ConcreteCategory.hom f.hom
  rootPath := f.rootPath

/-- The weakly pointed identity. -/
def id (X : PointedCGWH.{u, v}) : WeaklyPointedMap X X where
  hom := 𝟙 X.right
  rootPath := Path.refl (basepoint X)

/-- Composition of weakly pointed maps. -/
def comp (f : WeaklyPointedMap X Y) (g : WeaklyPointedMap Y Z) :
    WeaklyPointedMap X Z where
  hom := f.hom ≫ g.hom
  rootPath :=
    (f.rootPath.map
      (ConcreteCategory.hom g.hom :
        C(Y.right, Z.right)).continuous).trans g.rootPath

/-- A strictly pointed morphism as a weakly pointed carrier map. -/
noncomputable def ofHom (f : X ⟶ Y) : WeaklyPointedMap X Y where
  hom := f.right
  rootPath :=
    (Path.refl (basepoint Y)).cast (map_basepoint f) rfl

/-- Regard a weakly pointed map as a strict pointed map into the target
repointed at the image of the source point. -/
noncomputable def toPointedAt (f : WeaklyPointedMap X Y) :
    X ⟶ pointedAt Y.right (f.hom (basepoint X)) :=
  Under.homMk f.hom (by
    apply ConcreteCategory.hom_ext
    intro p
    change f.hom (X.hom p) = f.hom (basepoint X)
    cases p
    rfl)

/-- The native loop map of a weakly pointed map. -/
noncomputable def loopMap (f : WeaklyPointedMap X Y) :
    WeaklyPointedMap (PointedCGWH.loop.obj X)
      (PointedCGWH.loop.obj Y) := by
  let A := pointedAt Y.right (f.hom (basepoint X))
  let B0 := pointedAt Y.right (basepoint Y)
  let first : PointedCGWH.loop.obj X ⟶ PointedCGWH.loop.obj A :=
    PointedCGWH.loop.map f.toPointedAt
  let middle : NativeLoopAt Y.right (f.hom (basepoint X)) ⟶
      NativeLoopAt Y.right (basepoint Y) :=
    loopBasepointChange Y.right f.rootPath
  let last : PointedCGWH.loop.obj B0 ⟶ PointedCGWH.loop.obj Y :=
    PointedCGWH.loop.map (pointedAtBasepointIso Y).hom
  let hom : (PointedCGWH.loop.obj X).right ⟶
      (PointedCGWH.loop.obj Y).right :=
    first.right ≫ middle ≫ last.right
  let sx := basepoint (PointedCGWH.loop.obj X)
  let sa := basepoint (PointedCGWH.loop.obj A)
  let sb := basepoint (PointedCGWH.loop.obj B0)
  let sy := basepoint (PointedCGWH.loop.obj Y)
  have hFirst : first.right sx = sa := map_basepoint first
  have hLast : last.right sb = sy := map_basepoint last
  let q := (loopBasepointChange_basepoint_joined
    Y.right f.rootPath).somePath
  let q' := q.map
    (ConcreteCategory.hom last.right).continuous
  have hSource : hom sx = last.right (middle sa) := by
    change last.right (middle (first.right sx)) =
      last.right (middle sa)
    rw [hFirst]
  exact
    { hom := hom
      rootPath := q'.cast hSource hLast.symm }

/-- The underlying weak loop map has its exact strict-map/basepoint-change
factorization. -/
theorem loopMap_factorization (f : WeaklyPointedMap X Y) :
    f.loopMap.hom =
      (PointedCGWH.loop.map f.toPointedAt).right ≫
        loopBasepointChange Y.right f.rootPath ≫
          (PointedCGWH.loop.map
            (pointedAtBasepointIso Y).hom).right :=
  rfl

/-- Normalized continuous-map form of weak-loop landing. -/
private theorem loopMap_landing_normal (f : WeaklyPointedMap X Y)
    (gamma : CompactlyGenerated.compactlyGeneratedToTop.obj
      (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj X).right)) :
    @DFunLike.coe
      C(CompactlyGenerated.compactlyGeneratedToTop.obj
        (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj Y).right),
        LoopSpace Y.right (basepoint Y))
      (CompactlyGenerated.compactlyGeneratedToTop.obj
        (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj Y).right))
      (fun _ => LoopSpace Y.right (basepoint Y)) ContinuousMap.instFunLike
      (ConcreteCategory.hom (PointedCGWH.loopLanding Y))
      (@DFunLike.coe
        C(CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj X).right),
          CompactlyGenerated.compactlyGeneratedToTop.obj
            (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj Y).right))
        (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj X).right))
        (fun _ => CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj Y).right))
        ContinuousMap.instFunLike (ConcreteCategory.hom f.loopMap.hom) gamma) =
      f.toContinuousMap.loopMap
        (PointedCGWH.loopLanding X gamma) := by
  let A := pointedAt Y.right (f.hom (basepoint X))
  let B0 := pointedAt Y.right (basepoint Y)
  let first : PointedCGWH.loop.obj X ⟶ PointedCGWH.loop.obj A :=
    PointedCGWH.loop.map f.toPointedAt
  let middle : NativeLoopAt Y.right (f.hom (basepoint X)) ⟶
      NativeLoopAt Y.right (basepoint Y) :=
    loopBasepointChange Y.right f.rootPath
  let last : PointedCGWH.loop.obj B0 ⟶ PointedCGWH.loop.obj Y :=
    PointedCGWH.loop.map (pointedAtBasepointIso Y).hom
  let eta : NativeLoopAt Y.right (f.hom (basepoint X)) :=
    first.right gamma
  let delta : NativeLoopAt Y.right (basepoint Y) :=
    middle eta
  have hFac := ConcreteCategory.congr_hom
    (loopMap_factorization f) gamma
  have hMap : f.loopMap.hom gamma =
      last.right delta := by
    change f.loopMap.hom gamma =
      last.right delta at hFac
    exact hFac
  have hFirst :
      loopLandingAt Y.right (f.hom (basepoint X))
          eta =
        ContinuousMap.strictLoopMap
          (ConcreteCategory.hom f.hom :
            C(X.right, Y.right)) (basepoint X)
          (PointedCGWH.loopLanding X gamma) := by
    have hn := ConcreteCategory.congr_hom
      (PointedCGWH.loopLanding_naturality f.toPointedAt) gamma
    change loopLandingAt Y.right (f.hom (basepoint X))
        eta =
      PointedCGWH.strictLoopMap f.toPointedAt
        (PointedCGWH.loopLanding X gamma) at hn
    calc
      _ = PointedCGWH.strictLoopMap f.toPointedAt
          (PointedCGWH.loopLanding X gamma) := hn
      _ = _ := by
        apply Path.ext
        funext t
        rfl
  have hLast (zeta : NativeLoopAt Y.right (basepoint Y)) :
      PointedCGWH.loopLanding Y (last.right zeta) =
        loopLandingAt Y.right (basepoint Y) zeta := by
    have hn := ConcreteCategory.congr_hom
      (PointedCGWH.loopLanding_naturality
        (pointedAtBasepointIso Y).hom) zeta
    change PointedCGWH.loopLanding Y (last.right zeta) =
      PointedCGWH.strictLoopMap (pointedAtBasepointIso Y).hom
        (loopLandingAt Y.right (basepoint Y) zeta) at hn
    calc
      _ = PointedCGWH.strictLoopMap (pointedAtBasepointIso Y).hom
          (loopLandingAt Y.right (basepoint Y) zeta) := hn
      _ = _ := by
        apply Path.ext
        funext t
        rfl
  have hL := congrArg (fun z : CompactlyGenerated.compactlyGeneratedToTop.obj
      (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj Y).right) =>
        @DFunLike.coe
          C(CompactlyGenerated.compactlyGeneratedToTop.obj
            (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj Y).right),
            LoopSpace Y.right (basepoint Y))
          (CompactlyGenerated.compactlyGeneratedToTop.obj
            (CGWH.cgwhToCompactlyGenerated.obj (PointedCGWH.loop.obj Y).right))
          (fun _ => LoopSpace Y.right (basepoint Y)) ContinuousMap.instFunLike
          (ConcreteCategory.hom (PointedCGWH.loopLanding Y)) z) hMap
  have hMid := loopBasepointChange_landing Y.right f.rootPath eta
  have hFirstMap := congrArg (ContinuousMap.loopBasepointChange f.rootPath) hFirst
  have hRaw :
      ContinuousMap.loopBasepointChange f.rootPath
        (ContinuousMap.strictLoopMap (ConcreteCategory.hom f.hom : C(X.right, Y.right))
          (basepoint X) (PointedCGWH.loopLanding X gamma)) =
        f.toContinuousMap.loopMap (PointedCGWH.loopLanding X gamma) := by
    apply Path.ext
    rfl
  exact hL.trans ((hLast delta).trans (hMid.trans (hFirstMap.trans hRaw)))

/-- Landing a native weak loop map gives the existing raw weakly pointed
loop map. -/
@[simp]
theorem loopMap_landing (f : WeaklyPointedMap X Y)
    (gamma : (PointedCGWH.loop.obj X).right) :
    PointedCGWH.loopLanding Y (f.loopMap.hom gamma) =
      f.toContinuousMap.loopMap
        (PointedCGWH.loopLanding X gamma) :=
  loopMap_landing_normal f gamma

/-- The weak loop map of the weakly pointed identity is pointwise joined
to the identity. -/
theorem loopMap_id_joined (X : PointedCGWH.{u, v})
    (gamma : (PointedCGWH.loop.obj X).right) :
    Joined ((WeaklyPointedMap.id X).loopMap.hom gamma) gamma := by
  apply liftRawLoopJoinedFor X
  have hL := loopMap_landing (WeaklyPointedMap.id X) gamma
  have hRaw := ContinuousMap.WeaklyPointed.loopMap_id_homotopic
    (basepoint X) (PointedCGWH.loopLanding X gamma)
  exact (congrArg (fun delta =>
    Path.Homotopic delta (PointedCGWH.loopLanding X gamma)) hL).mpr hRaw

/-- Native weak loop-map composition retains the same complete raw homotopy. -/
theorem loopMap_comp_joined
    (f : WeaklyPointedMap X Y) (g : WeaklyPointedMap Y Z)
    (gamma : (PointedCGWH.loop.obj X).right) :
    Joined ((f.comp g).loopMap.hom gamma)
      (g.loopMap.hom (f.loopMap.hom gamma)) := by
  apply liftRawLoopJoinedFor Z
  let delta := PointedCGWH.loopLanding X gamma
  have hL := loopMap_landing (f.comp g) gamma
  have hF := loopMap_landing f gamma
  have hG := loopMap_landing g (f.loopMap.hom gamma)
  have hR := hG.trans (congrArg g.toContinuousMap.loopMap hF)
  have hEq : (f.comp g).toContinuousMap =
      f.toContinuousMap.comp g.toContinuousMap := rfl
  have hRaw := (congrArg (fun k : ContinuousMap.WeaklyPointed
      (basepoint X) (basepoint Z) =>
        Path.Homotopic (k.loopMap delta)
          (g.toContinuousMap.loopMap (f.toContinuousMap.loopMap delta))) hEq).mpr
    (ContinuousMap.WeaklyPointed.loopMap_comp_homotopic
      f.toContinuousMap g.toContinuousMap delta)
  exact (congrArg₂ (fun a b => Path.Homotopic a b) hL hR).mpr hRaw

/-- The weak loop map of a strictly pointed morphism reduces pointwise,
up to a path, to the strict native loop map. -/
theorem loopMap_ofHom_joined (f : X ⟶ Y)
    (gamma : (PointedCGWH.loop.obj X).right) :
    Joined ((WeaklyPointedMap.ofHom f).loopMap.hom gamma)
      ((PointedCGWH.loop.map f).right gamma) := by
  apply liftRawLoopJoinedFor Y
  have hL := loopMap_landing (WeaklyPointedMap.ofHom f) gamma
  have hR := ConcreteCategory.congr_hom
    (PointedCGWH.loopLanding_naturality f) gamma
  change PointedCGWH.loopLanding Y ((PointedCGWH.loop.map f).right gamma) =
    PointedCGWH.strictLoopMap f (PointedCGWH.loopLanding X gamma) at hR
  let delta := PointedCGWH.loopLanding X gamma
  let cf : C(X.right, Y.right) := ConcreteCategory.hom f.right
  have hConj {a y : Y.right} (hay : a = y)
      (eta : Path a a) :
      let r : Path a y := (Path.refl y).cast hay rfl
      (r.symm.trans (eta.trans r)).Homotopic
        (eta.cast hay.symm hay.symm) := by
    subst y
    change
      ((Path.refl a).symm.trans
        (eta.trans (Path.refl a))).Homotopic eta
    have hsymm : (Path.refl a).symm = Path.refl a := by
      apply Path.ext
      rfl
    rw [hsymm]
    exact
      (Path.Homotopic.refl_trans
        (eta.trans (Path.refl a))).trans
        (Path.Homotopic.trans_refl eta)
  have hRaw :
      ((WeaklyPointedMap.ofHom f).toContinuousMap.loopMap delta).Homotopic
        (PointedCGWH.strictLoopMap f delta) := by
    change
      let r : Path (f.right (basepoint X)) (basepoint Y) :=
        (Path.refl (basepoint Y)).cast (map_basepoint f) rfl
      (r.symm.trans ((delta.map cf.continuous).trans r)).Homotopic
        ((delta.map cf.continuous).cast
          (map_basepoint f).symm (map_basepoint f).symm)
    exact hConj (map_basepoint f) (delta.map cf.continuous)
  exact (congrArg₂ (fun a b => Path.Homotopic a b) hL hR).mpr hRaw

/-- A relative homotopy of carrier maps and a compatible root-path
homotopy induce pointwise joined native weak loop maps. -/
theorem loopMap_homotopic_of_homotopyRel
    (f g : WeaklyPointedMap X Y)
    (H : ContinuousMap.HomotopyRel
      f.toContinuousMap.hom g.toContinuousMap.hom
      {basepoint X})
    (hp : f.rootPath.Homotopic
      (g.rootPath.cast (H.fst_eq_snd (by simp)) rfl))
    (gamma : (PointedCGWH.loop.obj X).right) :
    Joined (f.loopMap.hom gamma) (g.loopMap.hom gamma) := by
  apply liftRawLoopJoinedFor Y
  have hL := loopMap_landing f gamma
  have hR := loopMap_landing g gamma
  have hRaw := ContinuousMap.WeaklyPointed.loopMap_homotopic_of_homotopyRel
    f.toContinuousMap g.toContinuousMap H hp (PointedCGWH.loopLanding X gamma)
  exact (congrArg₂ (fun a b => Path.Homotopic a b) hL hR).mpr hRaw

end WeaklyPointedMap

end PointedCGWH
