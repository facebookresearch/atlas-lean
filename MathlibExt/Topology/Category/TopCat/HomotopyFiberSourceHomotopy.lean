/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberPathFamily
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberHomotopySquare
public import MathlibExt.Topology.Category.TopCat.EndpointFixedCorrection

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberReparametrizationFixedPoint

/-!
# Source homotopies acting on the full original homotopy fiber

A homotopy from a source map to the identity gives an endomorphism of the
original homotopy fiber: prepend its projected path to the entire carried
path. Restricting the source homotopy to each remaining tail gives the
two-parameter deformation to a constant prefix. Removing that prefix by
endpoint-preserving reparameterization gives a homotopy to the identity.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

namespace TopCat

private def sourceTailParameter (s t : unitInterval) : unitInterval :=
  Set.Icc.convexComb s 1 t

private theorem sourceTailParameter_continuous :
    Continuous (fun z : unitInterval × unitInterval => sourceTailParameter z.1 z.2) :=
  Set.Icc.continuous_convexComb_prod.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))

private theorem sourceTailParameter_zero_right (s : unitInterval) :
    sourceTailParameter s 0 = s :=
  Set.Icc.convexComb_zero _ _

private theorem sourceTailParameter_one_right (s : unitInterval) :
    sourceTailParameter s 1 = 1 :=
  Set.Icc.convexComb_one _ _

private theorem sourceTailParameter_zero_left (t : unitInterval) :
    sourceTailParameter 0 t = t :=
  Set.Icc.convexComb_zero_one _

private theorem sourceTailParameter_one_left (t : unitInterval) :
    sourceTailParameter 1 t = 1 :=
  Set.Icc.convexComb_eq _ _

private def sourceFiberProjection {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    TopCat.of (unitInterval × homotopyFiber p b) ⟶ E :=
  TopCat.ofHom
    { toFun := fun z => homotopyFiberToTotal p b z.2
      continuous_toFun := (homotopyFiberToTotal p b).hom.continuous.comp continuous_snd }

private def sourceFiberTotal {E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (h : E ⟶ E) (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E)) :
    TopCat.of (unitInterval × homotopyFiber p b) ⟶ E :=
  TopCat.ofHom
    { toFun := fun z => H.toContinuousMap (z.1, homotopyFiberToTotal p b z.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk
          ((homotopyFiberToTotal p b).hom.continuous.comp continuous_snd)) }

private def sourceFiberPrefix {E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (h : E ⟶ E) (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E)) :
    ContinuousMap.Homotopy (sourceFiberTotal p b h H ≫ p).hom
      (sourceFiberProjection p b ≫ p).hom where
  toFun z := p (H.toContinuousMap
    (sourceTailParameter z.2.1 z.1, homotopyFiberToTotal p b z.2.2))
  continuous_toFun := by
    exact p.hom.continuous.comp (H.continuous.comp
      ((sourceTailParameter_continuous.comp
        ((continuous_fst.comp continuous_snd).prodMk continuous_fst)).prodMk
        ((homotopyFiberToTotal p b).hom.continuous.comp
          (continuous_snd.comp continuous_snd))))
  map_zero_left z := by
    exact congrArg
      (fun t : unitInterval => p (H.toContinuousMap (t, homotopyFiberToTotal p b z.2)))
      (sourceTailParameter_zero_right z.1)
  map_one_left z := by
    exact (congrArg
      (fun t : unitInterval => p (H.toContinuousMap (t, homotopyFiberToTotal p b z.2)))
      (sourceTailParameter_one_right z.1)).trans
      (congrArg (fun e : E => p e) (H.map_one_left (homotopyFiberToTotal p b z.2)))

private def sourceFiberCarried {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    ContinuousMap.Homotopy (sourceFiberProjection p b ≫ p).hom
      (TopCat.const b : TopCat.of (unitInterval × homotopyFiber p b) ⟶ B).hom where
  toFun z := homotopyFiberPath p b z.2.2 (TopCat.I.homeomorph.symm z.1)
  continuous_toFun := by
    exact continuous_eval.comp
      (((homotopyFiberPath p b).hom.continuous.comp
        (continuous_snd.comp continuous_snd)).prodMk
        (TopCat.I.homeomorph.symm.continuous.comp continuous_fst))
  map_zero_left z := by
    have ht : TopCat.I.homeomorph.symm (0 : unitInterval) = (0 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => homotopyFiberPath p b z.2 t) ht).trans
      (ConcreteCategory.congr_hom (homotopyPullbackPath_evalZero p (TopCat.const b)) z.2)
  map_one_left z := by
    have ht : TopCat.I.homeomorph.symm (1 : unitInterval) = (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => homotopyFiberPath p b z.2 t) ht).trans
      (ConcreteCategory.congr_hom (homotopyPullbackPath_evalOne p (TopCat.const b)) z.2)

private def sourceFiberFamily {E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (h : E ⟶ E) (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E)) :
    TopCat.of (unitInterval × homotopyFiber p b) ⟶ homotopyFiber p b :=
  homotopyFiberMapOfPathFamily p b (sourceFiberTotal p b h H)
    ((sourceFiberPrefix p b h H).trans (sourceFiberCarried p b))

private def sourceFiberSlice {E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (h : E ⟶ E) (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E))
    (s : unitInterval) : homotopyFiber p b ⟶ homotopyFiber p b :=
  TopCat.ofHom
    { toFun := fun z => sourceFiberFamily p b h H (s, z)
      continuous_toFun := (sourceFiberFamily p b h H).hom.continuous.comp
        (continuous_const.prodMk continuous_id) }

private theorem sourceFiberSlice_toTotal_apply {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E))
    (s : unitInterval) (z : homotopyFiber p b) :
    homotopyFiberToTotal p b (sourceFiberSlice p b h H s z) =
      H.toContinuousMap (s, homotopyFiberToTotal p b z) :=
  ConcreteCategory.congr_hom
    (homotopyFiberMapOfPathFamily_toTotal p b (sourceFiberTotal p b h H)
      ((sourceFiberPrefix p b h H).trans (sourceFiberCarried p b))) (s, z)

private theorem sourceFiberSlice_path_apply {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E))
    (s : unitInterval) (z : homotopyFiber p b) (t : TopCat.I.{u}) :
    homotopyFiberPath p b (sourceFiberSlice p b h H s z) t =
      if ht : ((TopCat.I.homeomorph t : unitInterval) : ℝ) ≤ 1 / 2 then
        p (H.toContinuousMap
          (sourceTailParameter s
            ⟨2 * TopCat.I.homeomorph t,
              (unitInterval.mul_pos_mem_iff zero_lt_two).2
                ⟨(TopCat.I.homeomorph t).2.1, ht⟩⟩,
            homotopyFiberToTotal p b z))
      else
        homotopyFiberPath p b z
          (TopCat.I.homeomorph.symm
            ⟨2 * TopCat.I.homeomorph t - 1,
              unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 ht).le, (TopCat.I.homeomorph t).2.2⟩⟩) := by
  exact (homotopyFiberMapOfPathFamily_path_apply p b (sourceFiberTotal p b h H)
    ((sourceFiberPrefix p b h H).trans (sourceFiberCarried p b)) (s, z) t).trans
    (ContinuousMap.Homotopy.trans_apply (sourceFiberPrefix p b h H)
      (sourceFiberCarried p b) (TopCat.I.homeomorph t, (s, z)))

/-- Prepend the projected original source homotopy to every entire carried fiber path. -/
def homotopyFiberSourceMap {E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (h : E ⟶ E) (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E)) :
    homotopyFiber p b ⟶ homotopyFiber p b :=
  homotopyFiberMapOfHomotopy h p p b
    ((ContinuousMap.Homotopy.refl p.hom).comp H)

/-- The map retains the original source-map total coordinate. -/
theorem homotopyFiberSourceMap_toTotal {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E)) :
    homotopyFiberSourceMap p b h H ≫ homotopyFiberToTotal p b =
      homotopyFiberToTotal p b ≫ h :=
  homotopyFiberMapOfHomotopy_toTotal h p p b
    ((ContinuousMap.Homotopy.refl p.hom).comp H)

/-- The full path is the source-homotopy prefix followed by the original path. -/
theorem homotopyFiberSourceMap_path_apply {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E))
    (z : homotopyFiber p b) (t : TopCat.I.{u}) :
    homotopyFiberPath p b (homotopyFiberSourceMap p b h H z) t =
      if ht : ((TopCat.I.homeomorph t : unitInterval) : ℝ) ≤ 1 / 2 then
        p (H.toContinuousMap
          (⟨2 * TopCat.I.homeomorph t,
            (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨(TopCat.I.homeomorph t).2.1, ht⟩⟩,
            homotopyFiberToTotal p b z))
      else
        homotopyFiberPath p b z
          (TopCat.I.homeomorph.symm
            ⟨2 * TopCat.I.homeomorph t - 1,
              unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 ht).le, (TopCat.I.homeomorph t).2.2⟩⟩) := by
  exact homotopyFiberMapOfHomotopy_path h p p b
    ((ContinuousMap.Homotopy.refl p.hom).comp H) z t

private theorem sourceFiberSlice_one_toTotal {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E)) :
    sourceFiberSlice p b h H 1 ≫ homotopyFiberToTotal p b =
      (𝟙 (homotopyFiber p b)) ≫ homotopyFiberToTotal p b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact (sourceFiberSlice_toTotal_apply p b h H 1 z).trans
    (H.map_one_left (homotopyFiberToTotal p b z))

private theorem sourceFiberSlice_one_path {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E))
    (z : homotopyFiber p b) (t : TopCat.I.{u}) :
    (sourceFiberSlice p b h H 1 ≫ homotopyFiberPath p b) z t =
      ((𝟙 (homotopyFiber p b)) ≫ homotopyFiberPath p b) z
        (TopCat.I.homeomorph.symm (homotopyReflTransReparam (TopCat.I.homeomorph t))) := by
  have hp := sourceFiberSlice_path_apply p b h H 1 z t
  change homotopyFiberPath p b (sourceFiberSlice p b h H 1 z) t =
    homotopyFiberPath p b z
      (TopCat.I.homeomorph.symm (homotopyReflTransReparam (TopCat.I.homeomorph t)))
  by_cases ht : ((TopCat.I.homeomorph t : unitInterval) : ℝ) ≤ 1 / 2
  · rw [dite_eq_left ht] at hp
    have hparam := homotopyReflTransReparam_eq_zero_of_le (TopCat.I.homeomorph t) ht
    rw [sourceTailParameter_one_left] at hp
    have hOne : H.toContinuousMap (1, homotopyFiberToTotal p b z) =
        homotopyFiberToTotal p b z :=
      H.map_one_left (homotopyFiberToTotal p b z)
    have hStart := ConcreteCategory.congr_hom
      (homotopyPullbackPath_evalZero p (TopCat.const b)) z
    have ht0 : TopCat.I.homeomorph.symm (0 : unitInterval) = (0 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    change homotopyFiberPath p b (sourceFiberSlice p b h H 1 z) t = _
    rw [hp, hOne, hparam, ht0]
    exact hStart.symm
  · rw [dite_eq_right ht] at hp
    have hparam : homotopyReflTransReparam (TopCat.I.homeomorph t) =
        ⟨2 * TopCat.I.homeomorph t - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, (TopCat.I.homeomorph t).2.2⟩⟩ :=
      homotopyReflTransReparam_eq_of_not_le (TopCat.I.homeomorph t) ht
    change homotopyFiberPath p b (sourceFiberSlice p b h H 1 z) t = _
    rw [hp, hparam]

/-- The genuine two-parameter full-path deformation makes the source action
homotopic to identity. -/
def homotopyFiberSourceMapHomotopy {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E)) :
    ContinuousMap.Homotopy (homotopyFiberSourceMap p b h H).hom
      ((𝟙 (homotopyFiber p b) : homotopyFiber p b ⟶ homotopyFiber p b).hom) := by
  have hzero : sourceFiberSlice p b h H 0 = homotopyFiberSourceMap p b h H := by
    apply homotopyPullback_hom_ext
    · rw [homotopyFiberSourceMap_toTotal]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      exact (sourceFiberSlice_toTotal_apply p b h H 0 z).trans
        (H.map_zero_left (homotopyFiberToTotal p b z))
    · exact TopCat.isTerminalPUnit.hom_ext _ _
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      apply ContinuousMap.ext
      intro t
      change homotopyFiberPath p b (sourceFiberSlice p b h H 0 z) t =
        homotopyFiberPath p b (homotopyFiberSourceMap p b h H z) t
      rw [homotopyFiberSourceMap_path_apply]
      simpa only [sourceTailParameter_zero_left] using
        sourceFiberSlice_path_apply p b h H 0 z t
  let first : ContinuousMap.Homotopy (homotopyFiberSourceMap p b h H).hom
      (sourceFiberSlice p b h H 1).hom :=
    { toContinuousMap := (sourceFiberFamily p b h H).hom
      map_zero_left z := ConcreteCategory.congr_hom hzero z
      map_one_left z := rfl }
  let last := homotopyFiberReparamHomotopy p b (sourceFiberSlice p b h H 1)
    (𝟙 (homotopyFiber p b)) homotopyReflTransReparam homotopyReflTransReparam.continuous
    homotopyReflTransReparam_zero homotopyReflTransReparam_one
    (sourceFiberSlice_one_toTotal p b h H) (sourceFiberSlice_one_path p b h H)
  exact first.trans last

/-- The actual source-action homotopy fixes a full constant-path fiber point
when the original source homotopy fixes its total point at every time. -/
theorem homotopyFiberSourceMapHomotopy_fixed_of_path_eq_const
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E))
    (z0 : homotopyFiber p b)
    (hconst : homotopyFiberPath p b z0 = ContinuousMap.const TopCat.I.{u} b)
    (hfixed : ∀ t : unitInterval,
      H.toContinuousMap (t, homotopyFiberToTotal p b z0) = homotopyFiberToTotal p b z0)
    (s : unitInterval) :
    homotopyFiberSourceMapHomotopy p b h H (s, z0) = z0 := by
  have hvalue : ∀ t : TopCat.I.{u}, homotopyFiberPath p b z0 t = b := by
    intro t
    exact congrArg (fun q : pathObject B => q t) hconst
  have hbase : p (homotopyFiberToTotal p b z0) = b := by
    have hstart := ConcreteCategory.congr_hom
      (homotopyPullbackPath_evalZero p (TopCat.const b)) z0
    change homotopyFiberPath p b z0 (0 : TopCat.I.{u}) =
      p (homotopyFiberToTotal p b z0) at hstart
    exact hstart.symm.trans (hvalue 0)
  have hslice : ∀ a : unitInterval, sourceFiberSlice p b h H a z0 = z0 := by
    intro a
    let T : TopCat.{u} := TopCat.of PUnit.{u + 1}
    let c : T ⟶ homotopyFiber p b := TopCat.const (sourceFiberSlice p b h H a z0)
    let d : T ⟶ homotopyFiber p b := TopCat.const z0
    have hcd : c = d := by
      apply homotopyPullback_hom_ext
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro _
        change homotopyFiberToTotal p b (sourceFiberSlice p b h H a z0) =
          homotopyFiberToTotal p b z0
        exact (sourceFiberSlice_toTotal_apply p b h H a z0).trans (hfixed a)
      · exact TopCat.isTerminalPUnit.hom_ext _ _
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro _
        apply ContinuousMap.ext
        intro t
        change homotopyFiberPath p b (sourceFiberSlice p b h H a z0) t =
          homotopyFiberPath p b z0 t
        have hp := sourceFiberSlice_path_apply p b h H a z0 t
        by_cases ht : ((TopCat.I.homeomorph t : unitInterval) : ℝ) ≤ 1 / 2
        · rw [dite_eq_left ht, hfixed] at hp
          exact hp.trans (hbase.trans (hvalue t).symm)
        · rw [dite_eq_right ht] at hp
          exact hp.trans ((hvalue _).trans (hvalue t).symm)
    exact ConcreteCategory.congr_hom hcd (PUnit.unit : PUnit.{u + 1})
  unfold homotopyFiberSourceMapHomotopy
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with hs
  · exact hslice _
  · exact homotopyFiberReparamHomotopy_fixed_of_path_eq_const p b
      (sourceFiberSlice p b h H 1) (𝟙 (homotopyFiber p b))
      homotopyReflTransReparam homotopyReflTransReparam.continuous
      homotopyReflTransReparam_zero homotopyReflTransReparam_one
      (sourceFiberSlice_one_toTotal p b h H) (sourceFiberSlice_one_path p b h H)
      z0 hconst _

end TopCat

end


/-!
## Exact phase and clock data of the original source-action factory
-/

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe uClock

namespace TopCat.HomotopyFiberSourceMapClockData

private theorem homApply {X Y : TopCat.{uClock}} (f : X ⟶ Y) (x : X) : f.hom x = f x := rfl

variable {E B : TopCat.{uClock}} (p : E ⟶ B) (b : B) (h : E ⟶ E)
  (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E))

/-- The actual first-stage map is the original remaining-tail pullback lift. -/
@[no_expose]
def tailFamily : TopCat.of (unitInterval × TopCat.homotopyFiber p b) ⟶ TopCat.homotopyFiber p b :=
  by exact sourceFiberFamily p b h H

/-- The actual unit-stage scalar clock is the original constant-prefix interpolation. -/
def unitClock (s t : unitInterval) : unitInterval :=
  homotopyFiberReparamClock homotopyReflTransReparam s t

private theorem unitClockValueComputed (s t : unitInterval) :
    (unitClock s t : ℝ) =
      (1 - (s : ℝ)) * (homotopyReflTransReparam t : ℝ) + (s : ℝ) * (t : ℝ) :=
  homotopyFiberReparamClock_value homotopyReflTransReparam s t

/-- The whole scalar unit clock displays both independent original time coordinates. -/
theorem unitClock_value (s t : unitInterval) :
    (unitClock s t : ℝ) =
      (1 - (s : ℝ)) * (homotopyReflTransReparam t : ℝ) + (s : ℝ) * (t : ℝ) :=
  unitClockValueComputed s t

/-- The actual unit-stage point map is the original endpoint-preserving pullback lift. -/
def unitFamily : TopCat.of (unitInterval × TopCat.homotopyFiber p b) ⟶ TopCat.homotopyFiber p b :=
  homotopyFiberReparamFamily p b (𝟙 (TopCat.homotopyFiber p b))
    homotopyReflTransReparam homotopyReflTransReparam.continuous
    homotopyReflTransReparam_zero homotopyReflTransReparam_one

private theorem factoryPhaseComputed (s : unitInterval) (z : homotopyFiber p b) :
    homotopyFiberSourceMapHomotopy p b h H (s, z) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        tailFamily p b h H
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).mpr
            ⟨s.property.1, hs⟩⟩, z)
      else unitFamily p b
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
          ⟨(not_le.mp hs).le, s.property.2⟩⟩, z) := by
  unfold homotopyFiberSourceMapHomotopy
  rw [ContinuousMap.Homotopy.trans_apply]
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · rw [dite_eq_left hs, dite_eq_left hs]
    exact homApply (TopCat.sourceFiberFamily p b h H) _
  · rw [dite_eq_right hs, dite_eq_right hs]
    let v : unitInterval := ⟨2 * s - 1,
      unitInterval.two_mul_sub_one_mem_iff.mpr
        ⟨(not_le.mp hs).le, s.property.2⟩⟩
    have hMap := homotopyFiberReparamHomotopy_toFamily p b (sourceFiberSlice p b h H 1)
      (𝟙 (homotopyFiber p b)) homotopyReflTransReparam
      homotopyReflTransReparam.continuous homotopyReflTransReparam_zero
      homotopyReflTransReparam_one (sourceFiberSlice_one_toTotal p b h H)
      (sourceFiberSlice_one_path p b h H)
    exact (DFunLike.congr_fun hMap (v, z)).trans
      (homApply (homotopyFiberReparamFamily p b (𝟙 (homotopyFiber p b))
        homotopyReflTransReparam homotopyReflTransReparam.continuous
        homotopyReflTransReparam_zero homotopyReflTransReparam_one) (v, z))

/-- The whole source-action map data displays the two original point-map phases.
Its displayed `toFun` is checked against the exact existing factory in its owning module. -/
def family (h : E ⟶ E)
    (H : ContinuousMap.Homotopy h.hom (ContinuousMap.id E)) :
    C(unitInterval × TopCat.homotopyFiber p b, TopCat.homotopyFiber p b) :=
  (homotopyFiberSourceMapHomotopy p b h H).toContinuousMap.copy
    (fun z =>
      if hs : (z.1 : ℝ) ≤ 1 / 2 then
        tailFamily p b h H
          (⟨2 * z.1, (unitInterval.mul_pos_mem_iff zero_lt_two).mpr ⟨z.1.property.1, hs⟩⟩, z.2)
      else unitFamily p b
        (⟨2 * z.1 - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
          ⟨(not_le.mp hs).le, z.1.property.2⟩⟩, z.2))
    (by
      funext z
      exact (factoryPhaseComputed p b h H z.1 z.2).symm)

private theorem familyApplyComputed (s : unitInterval) (z : TopCat.homotopyFiber p b) :
    family p b h H (s, z) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        tailFamily p b h H
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).mpr ⟨s.property.1, hs⟩⟩, z)
      else unitFamily p b
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
          ⟨(not_le.mp hs).le, s.property.2⟩⟩, z) := rfl

/-- The exact complete point-map program is available through its owning phase readout. -/
theorem family_apply (s : unitInterval) (z : TopCat.homotopyFiber p b) :
    family p b h H (s, z) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        tailFamily p b h H
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).mpr ⟨s.property.1, hs⟩⟩, z)
      else unitFamily p b
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
          ⟨(not_le.mp hs).le, s.property.2⟩⟩, z) := familyApplyComputed p b h H s z

private theorem factoryMapComputed :
    (homotopyFiberSourceMapHomotopy p b h H).toContinuousMap = family p b h H := by
  unfold family
  exact (ContinuousMap.copy_eq _ _ _).symm

/-- The unchanged original source-action factory has this exact whole map of actual point data. -/
theorem factory_toContinuousMap :
    (homotopyFiberSourceMapHomotopy p b h H).toContinuousMap = family p b h H :=
  factoryMapComputed p b h H

private theorem tailTotalComputed (s : unitInterval) (z : TopCat.homotopyFiber p b) :
    TopCat.homotopyFiberToTotal p b (tailFamily p b h H (s, z)) =
      H (s, TopCat.homotopyFiberToTotal p b z) :=
  sourceFiberSlice_toTotal_apply p b h H s z

/-- Every first-stage total point is the original source homotopy at the actual family time. -/
theorem tail_toTotal (s : unitInterval) (z : TopCat.homotopyFiber p b) :
    TopCat.homotopyFiberToTotal p b (tailFamily p b h H (s, z)) =
      H (s, TopCat.homotopyFiberToTotal p b z) := tailTotalComputed p b h H s z

private theorem tailPathComputed (s : unitInterval) (z : TopCat.homotopyFiber p b)
    (t : TopCat.I.{uClock}) :
    TopCat.homotopyFiberPath p b (tailFamily p b h H (s, z)) t =
      if ht : (TopCat.I.homeomorph t : ℝ) ≤ 1 / 2 then
        p (H (Set.Icc.convexComb s 1
          ⟨2 * TopCat.I.homeomorph t, (unitInterval.mul_pos_mem_iff zero_lt_two).mpr
            ⟨(TopCat.I.homeomorph t).property.1, ht⟩⟩,
          TopCat.homotopyFiberToTotal p b z))
      else TopCat.homotopyFiberPath p b z
        (TopCat.I.homeomorph.symm
          ⟨2 * TopCat.I.homeomorph t - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
            ⟨(not_le.mp ht).le, (TopCat.I.homeomorph t).property.2⟩⟩) :=
  sourceFiberSlice_path_apply p b h H s z t

/-- Every first-stage path time follows the full remaining source tail and
the entire carried curve. -/
theorem tail_path_apply (s : unitInterval) (z : TopCat.homotopyFiber p b) (t : TopCat.I.{uClock}) :
    TopCat.homotopyFiberPath p b (tailFamily p b h H (s, z)) t =
      if ht : (TopCat.I.homeomorph t : ℝ) ≤ 1 / 2 then
        p (H (Set.Icc.convexComb s 1
          ⟨2 * TopCat.I.homeomorph t, (unitInterval.mul_pos_mem_iff zero_lt_two).mpr
            ⟨(TopCat.I.homeomorph t).property.1, ht⟩⟩,
          TopCat.homotopyFiberToTotal p b z))
      else TopCat.homotopyFiberPath p b z
        (TopCat.I.homeomorph.symm
          ⟨2 * TopCat.I.homeomorph t - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
            ⟨(not_le.mp ht).le, (TopCat.I.homeomorph t).property.2⟩⟩) :=
  tailPathComputed p b h H s z t

private theorem unitTotalComputed (s : unitInterval) (z : TopCat.homotopyFiber p b) :
    TopCat.homotopyFiberToTotal p b (unitFamily p b (s, z)) =
      TopCat.homotopyFiberToTotal p b z :=
  homotopyFiberReparamFamily_toTotal p b (𝟙 (TopCat.homotopyFiber p b))
    homotopyReflTransReparam homotopyReflTransReparam.continuous
    homotopyReflTransReparam_zero homotopyReflTransReparam_one s z

/-- Every unit-stage total point is the original total point. -/
theorem unit_toTotal (s : unitInterval) (z : TopCat.homotopyFiber p b) :
    TopCat.homotopyFiberToTotal p b (unitFamily p b (s, z)) =
      TopCat.homotopyFiberToTotal p b z := unitTotalComputed p b s z

private theorem unitPathComputed (s : unitInterval) (z : TopCat.homotopyFiber p b)
    (t : TopCat.I.{uClock}) :
    TopCat.homotopyFiberPath p b (unitFamily p b (s, z)) t =
      TopCat.homotopyFiberPath p b z
        (TopCat.I.homeomorph.symm (unitClock s (TopCat.I.homeomorph t))) :=
  homotopyFiberReparamFamily_path_apply p b (𝟙 (TopCat.homotopyFiber p b))
    homotopyReflTransReparam homotopyReflTransReparam.continuous
    homotopyReflTransReparam_zero homotopyReflTransReparam_one s z t

/-- Every unit-stage path time has the exact original endpoint-preserving scalar clock. -/
theorem unit_path_apply (s : unitInterval) (z : TopCat.homotopyFiber p b) (t : TopCat.I.{uClock}) :
    TopCat.homotopyFiberPath p b (unitFamily p b (s, z)) t =
      TopCat.homotopyFiberPath p b z
        (TopCat.I.homeomorph.symm (unitClock s (TopCat.I.homeomorph t))) :=
  unitPathComputed p b s z t

end TopCat.HomotopyFiberSourceMapClockData
end
