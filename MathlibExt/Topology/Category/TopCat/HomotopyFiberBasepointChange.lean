/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import Mathlib.Topology.Homotopy.Path

import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Basepoint change for compact-open homotopy fibers

A path from `b` to `b'` changes the selected endpoint of the compact-open
homotopy fiber of `f : X ⟶ B` by appending that path to every carried
fiber path. The construction is continuous in the entire homotopy-fiber
point.

Ordinary path concatenation is parametrized on half intervals. Consequently,
basepoint change along a constant path is homotopic, but not definitionally
equal, to the identity; two successive changes are homotopic, but not
definitionally equal, to change along the concatenated path.

No fibration, weak-equivalence, properness, bar construction, or model-
category assertion is made here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

namespace TopCat

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! ## The basepoint-change map -/

/-- The ordinary path carried by a point of a compact-open homotopy fiber. -/
private def fiberRootPath
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (z : homotopyFiber f b) :
    Path (f (homotopyFiberToTotal f b z)) b where
  toFun t := homotopyFiberPath f b z (TopCat.I.homeomorph.symm t)
  continuous_toFun :=
    (homotopyFiberPath f b z).continuous.comp
      TopCat.I.homeomorph.symm.continuous
  source' := by
    have h := ConcreteCategory.congr_hom
      (homotopyPullbackPath_evalZero f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    exact h
  target' := by
    have hOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    have h := ConcreteCategory.congr_hom
      (homotopyPullbackPath_evalOne f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    change homotopyFiberPath f b z
      (TopCat.I.homeomorph.symm 1) = b
    rw [hOne]
    change pathEvalOne B (homotopyFiberPath f b z) = b
    change pathEvalOne B (homotopyFiberPath f b z) = b at h
    exact h

/-- The input paths vary continuously with the homotopy-fiber point. -/
private theorem fiberRootPath_continuous_family
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    Continuous (fun z : homotopyFiber f b × unitInterval =>
      fiberRootPath f b z.1 z.2) := by
  exact continuous_eval.comp
    (((homotopyFiberPath f b).hom.continuous.comp continuous_fst).prodMk
      (TopCat.I.homeomorph.symm.continuous.comp continuous_snd))

/-- Append a chosen path to every path in a homotopy fiber. -/
private def appendFiberPath
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    homotopyFiber f b ⟶ pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z =>
        ((fiberRootPath f b z.1).trans q) (TopCat.I.homeomorph z.2)
      continuous_toFun := by
        have htrans := Path.trans_continuous_family
            (fun z : homotopyFiber f b => fiberRootPath f b z)
            (fiberRootPath_continuous_family f b)
            (fun _ : homotopyFiber f b => q)
            (q.continuous.comp continuous_snd)
        exact htrans.comp
          (continuous_fst.prodMk
            (TopCat.I.homeomorph.continuous.comp continuous_snd)) }

@[reassoc]
private theorem appendFiberPath_evalZero
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    appendFiberPath f q ≫ pathEvalZero B =
      homotopyFiberToTotal f b ≫ f := by
  apply TopCat.ext
  intro z
  change ((fiberRootPath f b z).trans q)
    (TopCat.I.homeomorph (0 : TopCat.I.{u})) =
      f (homotopyFiberToTotal f b z)
  rw [TopCat.I.homeomorph_zero]
  exact ((fiberRootPath f b z).trans q).source'

@[reassoc]
private theorem appendFiberPath_evalOne
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    appendFiberPath f q ≫ pathEvalOne B =
      TopCat.const (X := homotopyFiber f b) b' := by
  apply TopCat.ext
  intro z
  change ((fiberRootPath f b z).trans q)
    (TopCat.I.homeomorph (1 : TopCat.I.{u})) = b'
  rw [TopCat.I.homeomorph_one]
  exact ((fiberRootPath f b z).trans q).target'

/-- Change the selected endpoint of a compact-open homotopy fiber by
concatenating every carried path with the chosen path. -/
def homotopyFiberBasepointChange
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    homotopyFiber f b ⟶ homotopyFiber f b' :=
  pullback.lift
    (Limits.prod.lift (homotopyFiberToTotal f b)
      (homotopyPullbackRight f
        (TopCat.const (X := TopCat.of PUnit) b)))
    (appendFiberPath f q)
    (by
      apply Limits.prod.hom_ext
      · simpa [pathEndpoints] using
          (appendFiberPath_evalZero f q).symm
      · calc
          (Limits.prod.lift (homotopyFiberToTotal f b)
                (homotopyPullbackRight f (TopCat.const b)) ≫
              Limits.prod.map f (TopCat.const b')) ≫ Limits.prod.snd =
              TopCat.const b' := by
                rw [Category.assoc, Limits.prod.map_snd]
                rw [← Category.assoc, Limits.prod.lift_snd]
                apply TopCat.ext
                intro z
                exact congrArg (fun _ : PUnit => b')
                  (Subsingleton.elim
                    (homotopyPullbackRight f
                      (TopCat.const (X := TopCat.of PUnit) b) z)
                    PUnit.unit)
          _ = (appendFiberPath f q ≫ pathEndpoints B) ≫
              Limits.prod.snd := by
                simpa [pathEndpoints] using
                  (appendFiberPath_evalOne f q).symm)

/-- Basepoint change does not alter the total-space coordinate. -/
@[reassoc (attr := simp)]
theorem homotopyFiberBasepointChange_toTotal
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    homotopyFiberBasepointChange f q ≫ homotopyFiberToTotal f b' =
      homotopyFiberToTotal f b := by
  change homotopyFiberBasepointChange f q ≫
      homotopyPullbackLeft f (TopCat.const b') =
    homotopyPullbackLeft f (TopCat.const b)
  rw [homotopyFiberBasepointChange, homotopyPullbackLeft,
    ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc]
private theorem homotopyFiberBasepointChange_path_map
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    homotopyFiberBasepointChange f q ≫ homotopyFiberPath f b' =
      appendFiberPath f q := by
  change homotopyFiberBasepointChange f q ≫
      homotopyPullbackPath f (TopCat.const b') = _
  rw [homotopyFiberBasepointChange, homotopyPullbackPath,
    pullback.lift_snd]

/-- Literal full-path formula for basepoint change. -/
@[simp]
theorem homotopyFiberBasepointChange_path
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b')
    (z : homotopyFiber f b) (t : TopCat.I.{u}) :
    homotopyFiberPath f b' (homotopyFiberBasepointChange f q z) t =
      let p : Path (f (homotopyFiberToTotal f b z)) b :=
        { toFun := fun s => homotopyFiberPath f b z (TopCat.I.homeomorph.symm s)
          continuous_toFun :=
            (homotopyFiberPath f b z).continuous.comp
              TopCat.I.homeomorph.symm.continuous
          source' := by
            have h := ConcreteCategory.congr_hom
              (homotopyPullbackPath_evalZero f
                (TopCat.const (X := TopCat.of PUnit) b)) z
            exact h
          target' := by
            have hOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
                (1 : TopCat.I.{u}) := by
              apply TopCat.I.homeomorph.injective
              simp
            have h := ConcreteCategory.congr_hom
              (homotopyPullbackPath_evalOne f
                (TopCat.const (X := TopCat.of PUnit) b)) z
            change homotopyFiberPath f b z
              (TopCat.I.homeomorph.symm 1) = b
            rw [hOne]
            exact h }
      (p.trans q) (TopCat.I.homeomorph t) := by
  change (homotopyFiberBasepointChange f q ≫
      homotopyPullbackPath f (TopCat.const b')) z t = _
  rw [homotopyFiberBasepointChange_path_map]
  rfl

/-! ## Uniform path reparametrization -/

private def blendReparam (r : unitInterval → unitInterval)
    (s t : unitInterval) : unitInterval :=
  ⟨(unitInterval.symm s : ℝ) • (r t : ℝ) + (s : ℝ) • (t : ℝ),
    convex_Icc _ _ (r t).2 t.2 (by unit_interval) (by unit_interval)
      (by simp) ⟩

private theorem blendReparam_continuous (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    Continuous (fun st : unitInterval × unitInterval =>
      blendReparam r st.1 st.2) := by
  apply Continuous.subtype_mk
  fun_prop

private theorem blendReparam_zero (r : unitInterval → unitInterval)
    (t : unitInterval) : blendReparam r 0 t = r t := by
  apply Subtype.ext
  simp [blendReparam]

private theorem blendReparam_one (r : unitInterval → unitInterval)
    (t : unitInterval) : blendReparam r 1 t = t := by
  apply Subtype.ext
  simp [blendReparam]

private theorem blendReparam_left (r : unitInterval → unitInterval)
    (hr0 : r 0 = 0) (s : unitInterval) :
    blendReparam r s 0 = 0 := by
  apply Subtype.ext
  simp [blendReparam, hr0]

private theorem blendReparam_right (r : unitInterval → unitInterval)
    (hr1 : r 1 = 1) (s : unitInterval) :
    blendReparam r s 1 = 1 := by
  apply Subtype.ext
  simp [blendReparam, hr1]

private def intervalZero (A : TopCat.{u}) :
    A ⟶ TopCat.of (unitInterval × (A : Type u)) :=
  TopCat.ofHom
    { toFun := fun a => (0, a)
      continuous_toFun := continuous_const.prodMk continuous_id }

private def intervalOne (A : TopCat.{u}) :
    A ⟶ TopCat.of (unitInterval × (A : Type u)) :=
  TopCat.ofHom
    { toFun := fun a => (1, a)
      continuous_toFun := continuous_const.prodMk continuous_id }

private def intervalSnd (A : TopCat.{u}) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ A :=
  TopCat.ofHom ContinuousMap.snd

@[simp]
private theorem intervalZero_snd (A : TopCat.{u}) :
    intervalZero A ≫ intervalSnd A = 𝟙 A := by
  rfl

@[simp]
private theorem intervalOne_snd (A : TopCat.{u}) :
    intervalOne A ≫ intervalSnd A = 𝟙 A := by
  rfl

/-- Reparametrize a whole compact-open path family, blending from `r` to the
identity as the outer parameter runs from zero to one. -/
private def reparamPathFamily {A B : TopCat.{u}}
    (p : A ⟶ pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z =>
        p z.1.2
          (TopCat.I.homeomorph.symm
            (blendReparam r z.1.1 (TopCat.I.homeomorph z.2)))
      continuous_toFun := by
        have hp : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            p z.1.2) :=
          p.hom.continuous.comp (continuous_snd.comp continuous_fst)
        have htI : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            TopCat.I.homeomorph z.2) :=
          TopCat.I.homeomorph.continuous.comp continuous_snd
        have hs : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            z.1.1) := continuous_fst.comp continuous_fst
        have hblend : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            blendReparam r z.1.1 (TopCat.I.homeomorph z.2)) :=
          (blendReparam_continuous r hr).comp (hs.prodMk htI)
        exact continuous_eval.comp
          (hp.prodMk (TopCat.I.homeomorph.symm.continuous.comp hblend)) }

private theorem reparamPathFamily_evalZero {A B : TopCat.{u}}
    (p : A ⟶ pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) (hr0 : r 0 = 0) :
    reparamPathFamily p r hr ≫ pathEvalZero B =
      intervalSnd A ≫ p ≫ pathEvalZero B := by
  apply TopCat.ext
  rintro ⟨s, a⟩
  have hTopZero : TopCat.I.homeomorph.symm (0 : unitInterval) =
      (0 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r s (TopCat.I.homeomorph (0 : TopCat.I.{u})))) = p a 0
  rw [TopCat.I.homeomorph_zero, blendReparam_left r hr0, hTopZero]

private theorem reparamPathFamily_evalOne {A B : TopCat.{u}}
    (p : A ⟶ pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) (hr1 : r 1 = 1) :
    reparamPathFamily p r hr ≫ pathEvalOne B =
      intervalSnd A ≫ p ≫ pathEvalOne B := by
  apply TopCat.ext
  rintro ⟨s, a⟩
  have hTopOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
      (1 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r s (TopCat.I.homeomorph (1 : TopCat.I.{u})))) = p a 1
  rw [TopCat.I.homeomorph_one, blendReparam_right r hr1, hTopOne]

private theorem intervalOne_comp_reparamPathFamily {A B : TopCat.{u}}
    (p : A ⟶ pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    intervalOne A ≫ reparamPathFamily p r hr = p := by
  apply TopCat.ext
  intro a
  apply ContinuousMap.ext
  intro t
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r 1 (TopCat.I.homeomorph t))) = p a t
  rw [blendReparam_one, TopCat.I.homeomorph.symm_apply_apply]

/-! ## Reparametrization inside a homotopy fiber -/

private def homotopyFiberReparamLift
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ homotopyFiber f b :=
  pullback.lift
    (Limits.prod.lift
      (intervalSnd A ≫ target ≫ homotopyFiberToTotal f b)
      (intervalSnd A ≫ target ≫
        homotopyPullbackRight f (TopCat.const b)))
    (reparamPathFamily (target ≫ homotopyFiberPath f b) r hr)
    (by
      apply Limits.prod.hom_ext
      · calc
          (Limits.prod.lift
                (intervalSnd A ≫ target ≫ homotopyFiberToTotal f b)
                (intervalSnd A ≫ target ≫
                  homotopyPullbackRight f (TopCat.const b)) ≫
              Limits.prod.map f (TopCat.const b)) ≫ Limits.prod.fst =
              intervalSnd A ≫ target ≫
                homotopyFiberToTotal f b ≫ f := by
                  simp [Category.assoc]
          _ = reparamPathFamily
                (target ≫ homotopyFiberPath f b) r hr ≫
              pathEvalZero B := by
                rw [reparamPathFamily_evalZero _ _ _ hr0]
                have h := congrArg
                  (fun k => intervalSnd A ≫ target ≫ k)
                  (homotopyPullbackPath_evalZero f
                    (TopCat.const (X := TopCat.of PUnit) b))
                simpa [Category.assoc] using h.symm
          _ = (reparamPathFamily
                (target ≫ homotopyFiberPath f b) r hr ≫
              pathEndpoints B) ≫ Limits.prod.fst := by
                simp [pathEndpoints]
      · calc
          (Limits.prod.lift
                (intervalSnd A ≫ target ≫ homotopyFiberToTotal f b)
                (intervalSnd A ≫ target ≫
                  homotopyPullbackRight f (TopCat.const b)) ≫
              Limits.prod.map f (TopCat.const b)) ≫ Limits.prod.snd =
              intervalSnd A ≫ target ≫
                homotopyPullbackRight f (TopCat.const b) ≫
                  TopCat.const b := by
                    simp [Category.assoc]
          _ = reparamPathFamily
                (target ≫ homotopyFiberPath f b) r hr ≫
              pathEvalOne B := by
                rw [reparamPathFamily_evalOne _ _ _ hr1]
                have h := congrArg
                  (fun k => intervalSnd A ≫ target ≫ k)
                  (homotopyPullbackPath_evalOne f
                    (TopCat.const (X := TopCat.of PUnit) b))
                simpa [Category.assoc] using h.symm
          _ = (reparamPathFamily
                (target ≫ homotopyFiberPath f b) r hr ≫
              pathEndpoints B) ≫ Limits.prod.snd := by
                simp [pathEndpoints])

private theorem homotopyFiberReparamLift_toTotal
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
        homotopyFiberToTotal f b =
      intervalSnd A ≫ target ≫ homotopyFiberToTotal f b := by
  change homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
      homotopyPullbackLeft f (TopCat.const b) = _
  rw [homotopyFiberReparamLift,
    ← Category.assoc, pullback.lift_fst]
  simp

private theorem homotopyFiberReparamLift_path
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
        homotopyFiberPath f b =
      reparamPathFamily (target ≫ homotopyFiberPath f b) r hr := by
  change homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
      homotopyPullbackPath f (TopCat.const b) = _
  rw [homotopyFiberReparamLift, homotopyPullbackPath,
    pullback.lift_snd]

private theorem intervalOne_comp_homotopyFiberReparamLift
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    intervalOne A ≫ homotopyFiberReparamLift f b target r hr hr0 hr1 =
      target := by
  apply homotopyPullback_hom_ext
  · rw [Category.assoc, homotopyFiberReparamLift_toTotal]
    rw [← Category.assoc, intervalOne_snd, Category.id_comp]
  · apply TopCat.isTerminalPUnit.hom_ext
  · rw [Category.assoc, homotopyFiberReparamLift_path,
      intervalOne_comp_reparamPathFamily]

private def homotopyFiberReparamHomotopyAux
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (source target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : source ≫ homotopyFiberToTotal f b =
      target ≫ homotopyFiberToTotal f b)
    (hpath : source ≫ homotopyFiberPath f b =
      intervalZero A ≫
        reparamPathFamily (target ≫ homotopyFiberPath f b) r hr) :
    ContinuousMap.Homotopy source.hom target.hom := by
  let lift := homotopyFiberReparamLift f b target r hr hr0 hr1
  have hzero : intervalZero A ≫ lift = source := by
    apply homotopyPullback_hom_ext
    · rw [Category.assoc, homotopyFiberReparamLift_toTotal]
      rw [← Category.assoc, intervalZero_snd, Category.id_comp]
      exact htotal.symm
    · apply TopCat.isTerminalPUnit.hom_ext
    · rw [Category.assoc, homotopyFiberReparamLift_path]
      exact hpath.symm
  have hone : intervalOne A ≫ lift = target :=
    intervalOne_comp_homotopyFiberReparamLift f b target r hr hr0 hr1
  exact
    { toContinuousMap := lift.hom
      map_zero_left := fun a => by
        simpa [intervalZero] using ConcreteCategory.congr_hom hzero a
      map_one_left := fun a => by
        simpa [intervalOne] using ConcreteCategory.congr_hom hone a }

/-- Reparametrizing every path in a homotopy fiber, while preserving the
total coordinate, gives a homotopy to the original fiber map. -/
def homotopyFiberReparamHomotopy
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (source target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : source ≫ homotopyFiberToTotal f b =
      target ≫ homotopyFiberToTotal f b)
    (hpath : ∀ (a : A) (t : TopCat.I.{u}),
      (source ≫ homotopyFiberPath f b) a t =
        (target ≫ homotopyFiberPath f b) a
          (TopCat.I.homeomorph.symm (r (TopCat.I.homeomorph t)))) :
    ContinuousMap.Homotopy source.hom target.hom := by
  apply homotopyFiberReparamHomotopyAux f b source target r hr hr0 hr1 htotal
  apply TopCat.ext
  intro a
  apply ContinuousMap.ext
  intro t
  change (source ≫ homotopyFiberPath f b) a t =
    (target ≫ homotopyFiberPath f b) a
      (TopCat.I.homeomorph.symm
        (blendReparam r 0 (TopCat.I.homeomorph t)))
  rw [blendReparam_zero]
  exact hpath a t

/-! ## Homotopy-coherent identity and composition -/

private def transReflReparam : unitInterval → unitInterval := fun t =>
  ⟨Path.Homotopy.transReflReparamAux t,
    Path.Homotopy.transReflReparamAux_mem_I t⟩

private theorem transReflReparam_continuous :
    Continuous transReflReparam := by
  apply Continuous.subtype_mk
  exact Path.Homotopy.continuous_transReflReparamAux

private theorem transReflReparam_zero : transReflReparam 0 = 0 := by
  apply Subtype.ext
  exact Path.Homotopy.transReflReparamAux_zero

private theorem transReflReparam_one : transReflReparam 1 = 1 := by
  apply Subtype.ext
  exact Path.Homotopy.transReflReparamAux_one

private theorem trans_refl_eq_reparam {B : TopCat.{u}} {x y : B}
    (p : Path x y) :
    p.trans (Path.refl y) =
      p.reparam transReflReparam transReflReparam_continuous
        transReflReparam_zero transReflReparam_one := by
  calc
    p.trans (Path.refl y) =
        p.reparam
          (fun t => ⟨Path.Homotopy.transReflReparamAux t,
            Path.Homotopy.transReflReparamAux_mem_I t⟩)
          (by fun_prop)
          (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
          (Subtype.ext Path.Homotopy.transReflReparamAux_one) :=
      Path.Homotopy.trans_refl_reparam p
    _ = p.reparam transReflReparam transReflReparam_continuous
          transReflReparam_zero transReflReparam_one := by
      apply Path.ext
      rfl

/-- Basepoint change along the constant path is homotopic to the identity. -/
def homotopyFiberBasepointChangeIdHomotopy
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    ContinuousMap.Homotopy
      (homotopyFiberBasepointChange f (Path.refl b)).hom
      ((𝟙 (homotopyFiber f b) :
        homotopyFiber f b ⟶ homotopyFiber f b).hom) := by
  apply homotopyFiberReparamHomotopy f b
    (homotopyFiberBasepointChange f (Path.refl b))
    (𝟙 (homotopyFiber f b)) transReflReparam
    transReflReparam_continuous transReflReparam_zero
    transReflReparam_one
  · exact homotopyFiberBasepointChange_toTotal f (Path.refl b)
  · intro z t
    rw [homotopyFiberBasepointChange_path_map]
    have h := congrArg
      (fun p : Path (f (homotopyFiberToTotal f b z)) b =>
        p (TopCat.I.homeomorph t))
      (trans_refl_eq_reparam (fiberRootPath f b z))
    change ((fiberRootPath f b z).trans (Path.refl b))
        (TopCat.I.homeomorph t) =
      fiberRootPath f b z (transReflReparam (TopCat.I.homeomorph t))
    exact h

private def assocReparam : unitInterval → unitInterval := fun t =>
  ⟨Path.Homotopy.transAssocReparamAux t,
    Path.Homotopy.transAssocReparamAux_mem_I t⟩

private theorem assocReparam_continuous : Continuous assocReparam := by
  apply Continuous.subtype_mk
  exact Path.Homotopy.continuous_transAssocReparamAux

private theorem assocReparam_zero : assocReparam 0 = 0 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_zero

private theorem assocReparam_one : assocReparam 1 = 1 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_one

private theorem trans_assoc_eq_reparam {B : TopCat.{u}}
    {x₀ x₁ x₂ x₃ : B} (p : Path x₀ x₁)
    (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam assocReparam assocReparam_continuous
        assocReparam_zero assocReparam_one := by
  calc
    (p.trans q).trans r =
        (p.trans (q.trans r)).reparam
          (fun t => ⟨Path.Homotopy.transAssocReparamAux t,
            Path.Homotopy.transAssocReparamAux_mem_I t⟩)
          (by fun_prop)
          (Subtype.ext Path.Homotopy.transAssocReparamAux_zero)
          (Subtype.ext Path.Homotopy.transAssocReparamAux_one) :=
      Path.Homotopy.trans_assoc_reparam p q r
    _ = (p.trans (q.trans r)).reparam assocReparam
          assocReparam_continuous assocReparam_zero assocReparam_one := by
      apply Path.ext
      rfl

/-- Two successive basepoint changes are homotopic to change along the
concatenated path. -/
def homotopyFiberBasepointChangeCompHomotopy
    {X B : TopCat.{u}} (f : X ⟶ B) {b₀ b₁ b₂ : B}
    (q₀₁ : Path b₀ b₁) (q₁₂ : Path b₁ b₂) :
    ContinuousMap.Homotopy
      (homotopyFiberBasepointChange f q₀₁ ≫
        homotopyFiberBasepointChange f q₁₂).hom
      (homotopyFiberBasepointChange f (q₀₁.trans q₁₂)).hom := by
  apply homotopyFiberReparamHomotopy f b₂
    (homotopyFiberBasepointChange f q₀₁ ≫
      homotopyFiberBasepointChange f q₁₂)
    (homotopyFiberBasepointChange f (q₀₁.trans q₁₂))
    assocReparam assocReparam_continuous assocReparam_zero
      assocReparam_one
  · simp
  · intro z t
    rw [Category.assoc, homotopyFiberBasepointChange_path_map]
    have h := congrArg
      (fun p : Path (f (homotopyFiberToTotal f b₀ z)) b₂ =>
        p (TopCat.I.homeomorph t))
      (trans_assoc_eq_reparam
        (fiberRootPath f b₀ z) q₀₁ q₁₂)
    have hTotal := ConcreteCategory.congr_hom
      (homotopyFiberBasepointChange_toTotal f q₀₁) z
    have hx : f (homotopyFiberToTotal f b₀ z) =
        f (homotopyFiberToTotal f b₁
          (homotopyFiberBasepointChange f q₀₁ z)) :=
      congrArg f hTotal.symm
    have hroot :
        (fiberRootPath f b₁
          (homotopyFiberBasepointChange f q₀₁ z)).cast hx rfl =
          (fiberRootPath f b₀ z).trans q₀₁ := by
      apply Path.ext
      funext s
      have hs := homotopyFiberBasepointChange_path f q₀₁ z
        (TopCat.I.homeomorph.symm s)
      change homotopyFiberPath f b₁
          (homotopyFiberBasepointChange f q₀₁ z)
            (TopCat.I.homeomorph.symm s) =
        ((fiberRootPath f b₀ z).trans q₀₁) s
      change homotopyFiberPath f b₁
          (homotopyFiberBasepointChange f q₀₁ z)
            (TopCat.I.homeomorph.symm s) =
        ((fiberRootPath f b₀ z).trans q₀₁) s at hs
      exact hs
    have hleftPath :
        ((fiberRootPath f b₁
          (homotopyFiberBasepointChange f q₀₁ z)).trans q₁₂).cast
            hx rfl =
          ((fiberRootPath f b₀ z).trans q₀₁).trans q₁₂ := by
      simp only [Path.cast_trans, Path.cast_rfl_rfl, hroot]
    have hleft := congrArg
      (fun p : Path (f (homotopyFiberToTotal f b₀ z)) b₂ =>
        p (TopCat.I.homeomorph t)) hleftPath
    have hcanonical :
        (((fiberRootPath f b₀ z).trans q₀₁).trans q₁₂)
            (TopCat.I.homeomorph t) =
          ((fiberRootPath f b₀ z).trans (q₀₁.trans q₁₂))
            (assocReparam (TopCat.I.homeomorph t)) := by
      change (((fiberRootPath f b₀ z).trans q₀₁).trans q₁₂)
          (TopCat.I.homeomorph t) =
        ((fiberRootPath f b₀ z).trans (q₀₁.trans q₁₂))
          (assocReparam (TopCat.I.homeomorph t)) at h
      exact h
    change ((fiberRootPath f b₁
        (homotopyFiberBasepointChange f q₀₁ z)).trans q₁₂)
        (TopCat.I.homeomorph t) =
      homotopyFiberPath f b₂
        (homotopyFiberBasepointChange f (q₀₁.trans q₁₂) z)
        (TopCat.I.homeomorph.symm
          (assocReparam (TopCat.I.homeomorph t)))
    have htarget := homotopyFiberBasepointChange_path f
      (q₀₁.trans q₁₂) z
      (TopCat.I.homeomorph.symm
        (assocReparam (TopCat.I.homeomorph t)))
    rw [htarget]
    simp only [TopCat.I.homeomorph.apply_symm_apply]
    change ((fiberRootPath f b₁
        (homotopyFiberBasepointChange f q₀₁ z)).trans q₁₂)
        (TopCat.I.homeomorph t) = _ at hleft
    exact hleft.trans hcanonical

section

-- Retain the original qualified constructor names as aliases of the same definitions.
open TopCat renaming
  homotopyFiberBasepointChangeIdHomotopy → homotopyFiberBasepointChange_id_homotopy,
  homotopyFiberBasepointChangeCompHomotopy → homotopyFiberBasepointChange_comp_homotopy

export _root_ (homotopyFiberBasepointChange_id_homotopy
  homotopyFiberBasepointChange_comp_homotopy)

end

end TopCat


public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe uReparam

namespace TopCat

/-- The affine clock used by the actual compact-open fiber reparameterization. -/
@[no_expose]
def homotopyFiberReparamClock (r : unitInterval → unitInterval)
    (s t : unitInterval) : unitInterval := by
  exact blendReparam r s t

private theorem homotopyFiberReparamClockValueComputed (r : unitInterval → unitInterval)
    (s t : unitInterval) :
    (homotopyFiberReparamClock r s t : ℝ) =
      (1 - (s : ℝ)) * (r t : ℝ) + (s : ℝ) * (t : ℝ) := rfl

/-- Both independent clock coordinates retain their exact affine scalar values. -/
theorem homotopyFiberReparamClock_value (r : unitInterval → unitInterval)
    (s t : unitInterval) :
    (homotopyFiberReparamClock r s t : ℝ) =
      (1 - (s : ℝ)) * (r t : ℝ) + (s : ℝ) * (t : ℝ) :=
  homotopyFiberReparamClockValueComputed r s t

/-- The original pullback lift reparameterizes every entire carried path. -/
@[no_expose]
def homotopyFiberReparamFamily {A X B : TopCat.{uReparam}} (f : X ⟶ B) (b : B)
    (target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    TopCat.of (unitInterval × (A : Type uReparam)) ⟶ homotopyFiber f b :=
  by exact homotopyFiberReparamLift f b target r hr hr0 hr1

/-- Every family time retains the actual target total coordinate. -/
theorem homotopyFiberReparamFamily_toTotal {A X B : TopCat.{uReparam}}
    (f : X ⟶ B) (b : B) (target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) (s : unitInterval) (a : A) :
    homotopyFiberToTotal f b (homotopyFiberReparamFamily f b target r hr hr0 hr1 (s, a)) =
      homotopyFiberToTotal f b (target a) :=
  ConcreteCategory.congr_hom
    (TopCat.homotopyFiberReparamLift_toTotal f b target r hr hr0 hr1) (s, a)

/-- Every carried-path time uses the same original affine clock. -/
theorem homotopyFiberReparamFamily_path_apply {A X B : TopCat.{uReparam}}
    (f : X ⟶ B) (b : B) (target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) (s : unitInterval) (a : A) (t : TopCat.I.{uReparam}) :
    homotopyFiberPath f b (homotopyFiberReparamFamily f b target r hr hr0 hr1 (s, a)) t =
      homotopyFiberPath f b (target a)
        (TopCat.I.homeomorph.symm (homotopyFiberReparamClock r s (TopCat.I.homeomorph t))) :=
  congrArg (fun gamma : pathObject B => gamma t)
    (ConcreteCategory.congr_hom
      (TopCat.homotopyFiberReparamLift_path f b target r hr hr0 hr1) (s, a))

private theorem homotopyFiberReparamHomotopyToFamilyComputed {A X B : TopCat.{uReparam}}
    (f : X ⟶ B) (b : B) (source target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : source ≫ homotopyFiberToTotal f b = target ≫ homotopyFiberToTotal f b)
    (hpath : ∀ (a : A) (t : TopCat.I.{uReparam}),
      (source ≫ homotopyFiberPath f b) a t =
        (target ≫ homotopyFiberPath f b) a
          (TopCat.I.homeomorph.symm (r (TopCat.I.homeomorph t)))) :
    (homotopyFiberReparamHomotopy f b source target r hr hr0 hr1 htotal hpath).toContinuousMap =
      (homotopyFiberReparamFamily f b target r hr hr0 hr1).hom := rfl

/-- The constructed homotopy has exactly the original reparameterization family as its whole map. -/
theorem homotopyFiberReparamHomotopy_toFamily {A X B : TopCat.{uReparam}}
    (f : X ⟶ B) (b : B) (source target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : source ≫ homotopyFiberToTotal f b = target ≫ homotopyFiberToTotal f b)
    (hpath : ∀ (a : A) (t : TopCat.I.{uReparam}),
      (source ≫ homotopyFiberPath f b) a t =
        (target ≫ homotopyFiberPath f b) a
          (TopCat.I.homeomorph.symm (r (TopCat.I.homeomorph t)))) :
    (homotopyFiberReparamHomotopy f b source target r hr hr0 hr1 htotal hpath).toContinuousMap =
      (homotopyFiberReparamFamily f b target r hr hr0 hr1).hom :=
  homotopyFiberReparamHomotopyToFamilyComputed f b source target r hr hr0 hr1 htotal hpath

end TopCat

end
