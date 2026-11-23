/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberSourceHomotopy
public import MathlibExt.Topology.Category.TopCat.ContractionLoopHomotopyEquiv
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoops
public import MathlibExt.Topology.Category.TopCat.LoopReparametrization

/-!
# The full original homotopy fiber and loops from a based contraction

A based contraction on an arbitrary total space gives the continuous return
from the full homotopy fiber to raw compact-open based loops. It prepends the
reverse projected contraction to the entire original carried path. The
inverse is the existing selected-loop inclusion. The same full source-action
and loop reparameterization families prove both inverse laws relative to the
independently constructed fiber point and literal constant loop.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval Topology.Homotopy

universe u

namespace TopCat

private def fixedTotalLoopMap {Z E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (f : Z ⟶ homotopyFiber p b) (e : E) (he : p e = b)
    (hf : f ≫ homotopyFiberToTotal p b = TopCat.const e) :
    Z ⟶ TopCat.of (LoopSpace B b) :=
  TopCat.ofHom
    { toFun := fun z =>
        { toContinuousMap :=
            (homotopyFiberPath p b (f z)).comp
              ⟨(TopCat.I.homeomorph.{u}).symm, (TopCat.I.homeomorph.{u}).symm.continuous⟩
          source' := by
            have ht : (TopCat.I.homeomorph.{u}).symm (0 : unitInterval) = (0 : TopCat.I.{u}) := by
              apply (TopCat.I.homeomorph.{u}).injective
              simp
            have hs := ConcreteCategory.congr_hom
              (homotopyPullbackPath_evalZero p (TopCat.const b)) (f z)
            have htot : homotopyFiberToTotal p b (f z) = e :=
              ConcreteCategory.congr_hom hf z
            exact (congrArg (fun t : TopCat.I.{u} => homotopyFiberPath p b (f z) t) ht).trans
              (hs.trans ((congrArg (fun q : E => p q) htot).trans he))
          target' := by
            have ht : (TopCat.I.homeomorph.{u}).symm (1 : unitInterval) = (1 : TopCat.I.{u}) := by
              apply (TopCat.I.homeomorph.{u}).injective
              simp
            exact (congrArg (fun t : TopCat.I.{u} => homotopyFiberPath p b (f z) t) ht).trans
              (ConcreteCategory.congr_hom
                (homotopyPullbackPath_evalOne p (TopCat.const b)) (f z)) }
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        exact continuous_eval.comp
          (((homotopyFiberPath p b).hom.continuous.comp
            (f.hom.continuous.comp continuous_fst)).prodMk
            ((TopCat.I.homeomorph.{u}).symm.continuous.comp continuous_snd)) }

private theorem fixedTotalLoopMap_path {Z E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (f : Z ⟶ homotopyFiber p b) (e : E) (he : p e = b)
    (hf : f ≫ homotopyFiberToTotal p b = TopCat.const e) :
    fixedTotalLoopMap p b f e he hf ≫ loopPathObjectMap B b =
      f ≫ homotopyFiberPath p b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply ContinuousMap.ext
  intro t
  change homotopyFiberPath p b (f z)
      ((TopCat.I.homeomorph.{u}).symm ((TopCat.I.homeomorph.{u}) t)) = homotopyFiberPath p b (f z) t
  rw [(TopCat.I.homeomorph.{u}).symm_apply_apply]

private theorem fixedTotalLoopMap_factor {Z E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (f : Z ⟶ homotopyFiber p b) (e : E) (he : p e = b)
    (hf : f ≫ homotopyFiberToTotal p b = TopCat.const e) :
    fixedTotalLoopMap p b f e he hf ≫ loopToHomotopyFiber p e b he = f := by
  apply homotopyPullback_hom_ext
  · calc
      _ = fixedTotalLoopMap p b f e he hf ≫
          (loopToHomotopyFiber p e b he ≫ homotopyFiberToTotal p b) :=
        Category.assoc _ _ _
      _ = fixedTotalLoopMap p b f e he hf ≫ TopCat.const e :=
        congrArg (fun m => fixedTotalLoopMap p b f e he hf ≫ m)
          (loopToHomotopyFiber_toTotal p e b he)
      _ = TopCat.const e := rfl
      _ = f ≫ homotopyFiberToTotal p b := hf.symm
  · exact isTerminalPUnit.hom_ext _ _
  · calc
      _ = fixedTotalLoopMap p b f e he hf ≫
          (loopToHomotopyFiber p e b he ≫ homotopyFiberPath p b) :=
        Category.assoc _ _ _
      _ = fixedTotalLoopMap p b f e he hf ≫ loopPathObjectMap B b :=
        congrArg (fun m => fixedTotalLoopMap p b f e he hf ≫ m)
          (loopToHomotopyFiber_path p e b he)
      _ = f ≫ homotopyFiberPath p b := fixedTotalLoopMap_path p b f e he hf

private def contractionSourceHomotopy {E : TopCat.{u}} (e : E) (C : BasedContraction E e) :
    ContinuousMap.Homotopy
      (TopCat.const e : E ⟶ E).hom
      (ContinuousMap.id E) :=
  C.homotopy.symm

private theorem contractionSourceHomotopy_fixed {E : TopCat.{u}} (e : E) (C : BasedContraction E e)
    (t : unitInterval) :
    C.homotopy.symm.toContinuousMap
        (t, e) = e := by
  change C.homotopy
      (unitInterval.symm t, e) = e
  exact C.fixed (unitInterval.symm t)

private def contractionFiberMap {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (C : BasedContraction E e) :
    homotopyFiber p b ⟶ homotopyFiber p b :=
  homotopyFiberSourceMap p b (TopCat.const e)
    (contractionSourceHomotopy e C)

private theorem contractionFiberMap_toTotal {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (C : BasedContraction E e) :
    contractionFiberMap p e b C ≫ homotopyFiberToTotal p b =
      TopCat.const e := by
  exact (homotopyFiberSourceMap_toTotal p b (TopCat.const e)
    (contractionSourceHomotopy e C)).trans (by rfl)

/-- The full-path return from the original homotopy fiber, using the given based contraction. -/
def homotopyFiberToLoopsOfBasedContraction {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    homotopyFiber p b ⟶ TopCat.of (LoopSpace B b) :=
  fixedTotalLoopMap p b (contractionFiberMap p e b C) e he
    (contractionFiberMap_toTotal p e b C)

/-- The reverse projected contraction is followed by the whole original carried fiber path. -/
theorem homotopyFiberToLoopsOfBasedContraction_apply {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e)
    (z : homotopyFiber p b) (t : unitInterval) :
    homotopyFiberToLoopsOfBasedContraction p e b he C z t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        p (C.homotopy.symm.toContinuousMap
          (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
            homotopyFiberToTotal p b z))
      else
        homotopyFiberPath p b z
          ((TopCat.I.homeomorph.{u}).symm
            ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩) := by
  have h := homotopyFiberSourceMap_path_apply p b (TopCat.const e)
    (contractionSourceHomotopy e C) z ((TopCat.I.homeomorph.{u}).symm t)
  change homotopyFiberPath p b
    (homotopyFiberSourceMap p b (TopCat.const e)
      (contractionSourceHomotopy e C) z) ((TopCat.I.homeomorph.{u}).symm t) = _
  simpa only [contractionSourceHomotopy, (TopCat.I.homeomorph.{u}).apply_symm_apply] using h

private theorem contraction_return_comp {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    homotopyFiberToLoopsOfBasedContraction p e b he C ≫
        loopToHomotopyFiber p e b he =
      contractionFiberMap p e b C :=
  fixedTotalLoopMap_factor p b (contractionFiberMap p e b C)
    e he (contractionFiberMap_toTotal p e b C)

private theorem contraction_inclusion_comp {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    loopToHomotopyFiber p e b he ≫
        homotopyFiberToLoopsOfBasedContraction p e b he C =
      loopReparamMap B b homotopyReflTransReparam homotopyReflTransReparam.continuous
        homotopyReflTransReparam_zero homotopyReflTransReparam_one := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro gamma
  apply _root_.Path.ext
  funext t
  rw [loopReparamMap_apply]
  have hp := homotopyFiberToLoopsOfBasedContraction_apply p e b he C
    (loopToHomotopyFiber p e b he gamma) t
  have htot : homotopyFiberToTotal p b
      (loopToHomotopyFiber p e b he gamma) = e :=
    ConcreteCategory.congr_hom (loopToHomotopyFiber_toTotal p e b he) gamma
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [dite_eq_left ht, htot, contractionSourceHomotopy_fixed, he] at hp
    have hparam := homotopyReflTransReparam_eq_zero_of_le t ht
    change homotopyFiberToLoopsOfBasedContraction p e b he C
        (loopToHomotopyFiber p e b he gamma) t = _
    exact hp.trans ((congrArg (fun s => gamma s) hparam).trans gamma.source).symm
  · rw [dite_eq_right ht] at hp
    have hPath := ConcreteCategory.congr_hom
      (loopToHomotopyFiber_path p e b he) gamma
    let s : unitInterval :=
      ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
    have hEval : homotopyFiberPath p b
        (loopToHomotopyFiber p e b he gamma)
        ((TopCat.I.homeomorph.{u}).symm s) = gamma s := by
      exact (congrArg (fun q : pathObject B => q ((TopCat.I.homeomorph.{u}).symm s)) hPath).trans
        (by change gamma ((TopCat.I.homeomorph.{u}) ((TopCat.I.homeomorph.{u}).symm s)) = gamma s
            rw [(TopCat.I.homeomorph.{u}).apply_symm_apply])
    have hparam : homotopyReflTransReparam t = s :=
      homotopyReflTransReparam_eq_of_not_le t ht
    change homotopyFiberToLoopsOfBasedContraction p e b he C
        (loopToHomotopyFiber p e b he gamma) t = _
    exact hp.trans (hEval.trans (congrArg (fun r => gamma r) hparam.symm))

/-- The actual independently selected constant-path fiber point maps to the literal constant
loop. -/
theorem homotopyFiberToLoopsOfBasedContraction_selectedPoint
    {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    homotopyFiberSelectedPointMap p e b he ≫
        homotopyFiberToLoopsOfBasedContraction p e b he C =
      (TopCat.const (Path.refl b) : TopCat.of PUnit.{u + 1} ⟶ TopCat.of (LoopSpace B b)) := by
  let c : TopCat.of PUnit.{u + 1} ⟶ TopCat.of (LoopSpace B b) := TopCat.const (Path.refl b)
  let i := loopToHomotopyFiber p e b he
  let r := homotopyFiberToLoopsOfBasedContraction p e b he C
  calc
    _ = (c ≫ i) ≫ r :=
      congrArg (· ≫ r) (loopToHomotopyFiber_constant_point p e b he).symm
    _ = c ≫ (i ≫ r) := Category.assoc _ _ _
    _ = c ≫ loopReparamMap B b homotopyReflTransReparam homotopyReflTransReparam.continuous
        homotopyReflTransReparam_zero homotopyReflTransReparam_one :=
      congrArg (c ≫ ·) (contraction_inclusion_comp p e b he C)
    _ = c := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      apply _root_.Path.ext
      funext t
      change loopReparamMap B b homotopyReflTransReparam homotopyReflTransReparam.continuous
        homotopyReflTransReparam_zero homotopyReflTransReparam_one (Path.refl b) t = b
      exact loopReparamMap_apply B b homotopyReflTransReparam
        homotopyReflTransReparam.continuous homotopyReflTransReparam_zero
        homotopyReflTransReparam_one (Path.refl b) t

private def contraction_fiberInverseHomotopy {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    ContinuousMap.Homotopy
      ((loopToHomotopyFiber p e b he).hom.comp
        (homotopyFiberToLoopsOfBasedContraction p e b he C).hom)
      (ContinuousMap.id (homotopyFiber p b)) := by
  let back := homotopyFiberToLoopsOfBasedContraction p e b he C
  let forward := loopToHomotopyFiber p e b he
  let H := homotopyFiberSourceMapHomotopy p b (TopCat.const e)
    (contractionSourceHomotopy e C)
  have hEq := contraction_return_comp p e b he C
  have hStart : (contractionFiberMap p e b C).hom =
      forward.hom.comp back.hom :=
    (congrArg TopCat.Hom.hom hEq.symm).trans (TopCat.hom_comp back forward)
  exact H.cast hStart rfl

private def contraction_loopInverseHomotopy {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    ContinuousMap.Homotopy
      ((homotopyFiberToLoopsOfBasedContraction p e b he C).hom.comp
        (loopToHomotopyFiber p e b he).hom)
      (ContinuousMap.id (LoopSpace B b)) := by
  let back := homotopyFiberToLoopsOfBasedContraction p e b he C
  let forward := loopToHomotopyFiber p e b he
  let H := loopReparamHomotopy B b homotopyReflTransReparam
    homotopyReflTransReparam.continuous homotopyReflTransReparam_zero
    homotopyReflTransReparam_one
  have hEq := contraction_inclusion_comp p e b he C
  have hStart :
      (loopReparamMap B b homotopyReflTransReparam homotopyReflTransReparam.continuous
        homotopyReflTransReparam_zero homotopyReflTransReparam_one).hom =
      back.hom.comp forward.hom :=
    (congrArg TopCat.Hom.hom hEq.symm).trans (TopCat.hom_comp forward back)
  exact H.cast hStart rfl

/-- The full original homotopy fiber is homotopy equivalent to raw based loops. -/
def homotopyFiberLoopEquivOfBasedContraction {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    ContinuousMap.HomotopyEquiv (homotopyFiber p b) (LoopSpace B b) := by
  let back := homotopyFiberToLoopsOfBasedContraction p e b he C
  let forward := loopToHomotopyFiber p e b he
  exact
    { toFun := back.hom
      invFun := forward.hom
      left_inv := ⟨contraction_fiberInverseHomotopy p e b he C⟩
      right_inv := ⟨contraction_loopInverseHomotopy p e b he C⟩ }

/-- The forward map is exactly the full-path return constructed from the based contraction. -/
theorem homotopyFiberLoopEquivOfBasedContraction_toFun
    {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    (homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun =
      (homotopyFiberToLoopsOfBasedContraction p e b he C).hom := (rfl)

/-- The inverse is exactly the original selected-loop inclusion. -/
theorem homotopyFiberLoopEquivOfBasedContraction_invFun
    {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    (homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun =
      (loopToHomotopyFiber p e b he).hom := (rfl)

/-- The actual fiber inverse family fixes its original constant-path selected point at all times. -/
@[nolint defsWithUnderscore] -- component name of the equivalence; used downstream
def homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel
    {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    ContinuousMap.HomotopyRel
      ((homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun.comp
        (homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun)
      (ContinuousMap.id (homotopyFiber p b))
      {homotopyFiberSelectedPointMap p e b he PUnit.unit} := by
  let z0 : homotopyFiber p b := homotopyFiberSelectedPointMap p e b he PUnit.unit
  let H := contraction_fiberInverseHomotopy p e b he C
  have hconst : homotopyFiberPath p b z0 = ContinuousMap.const TopCat.I.{u} b :=
    ConcreteCategory.congr_hom (homotopyFiberSelectedPointMap_path p e b he) PUnit.unit
  have htotal : homotopyFiberToTotal p b z0 = e :=
    ConcreteCategory.congr_hom (homotopyFiberSelectedPointMap_toTotal p e b he) PUnit.unit
  have hfixedTotal : ∀ t : unitInterval,
      (contractionSourceHomotopy e C).toContinuousMap
        (t, homotopyFiberToTotal p b z0) = homotopyFiberToTotal p b z0 := by
    intro t
    rw [htotal]
    exact contractionSourceHomotopy_fixed e C t
  have hfixed : ∀ t : unitInterval, H (t, z0) = z0 := by
    intro t
    change homotopyFiberSourceMapHomotopy p b (TopCat.const e)
      (contractionSourceHomotopy e C) (t, z0) = z0
    exact homotopyFiberSourceMapHomotopy_fixed_of_path_eq_const p b (TopCat.const e)
      (contractionSourceHomotopy e C) z0 hconst hfixedTotal t
  change ContinuousMap.HomotopyRel
    ((loopToHomotopyFiber p e b he).hom.comp
      (homotopyFiberToLoopsOfBasedContraction p e b he C).hom)
    (ContinuousMap.id (homotopyFiber p b)) ({z0} : Set (homotopyFiber p b))
  refine { toHomotopy := H, prop' := ?_ }
  intro t z hz
  obtain rfl := Set.mem_singleton_iff.mp hz
  exact (hfixed t).trans ((hfixed 0).symm.trans (H.map_zero_left z0))

/-- The actual loop inverse family fixes the literal constant loop at every time. -/
@[nolint defsWithUnderscore] -- component name of the equivalence; used downstream
def homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel
    {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    ContinuousMap.HomotopyRel
      ((homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun.comp
        (homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun)
      (ContinuousMap.id (LoopSpace B b)) {Path.refl b} := by
  let H := contraction_loopInverseHomotopy p e b he C
  have hfixed : ∀ t : unitInterval, H (t, Path.refl b) = Path.refl b := by
    intro t
    change loopReparamHomotopy B b homotopyReflTransReparam
      homotopyReflTransReparam.continuous homotopyReflTransReparam_zero
      homotopyReflTransReparam_one (t, Path.refl b) = Path.refl b
    exact loopReparamHomotopy_fixed_constant_loop B b homotopyReflTransReparam
      homotopyReflTransReparam.continuous homotopyReflTransReparam_zero
      homotopyReflTransReparam_one t
  change ContinuousMap.HomotopyRel
    ((homotopyFiberToLoopsOfBasedContraction p e b he C).hom.comp
      (loopToHomotopyFiber p e b he).hom)
    (ContinuousMap.id (LoopSpace B b)) ({Path.refl b} : Set (LoopSpace B b))
  refine { toHomotopy := H, prop' := ?_ }
  intro t gamma hgamma
  obtain rfl := Set.mem_singleton_iff.mp hgamma
  exact (hfixed t).trans ((hfixed 0).symm.trans (H.map_zero_left (Path.refl b)))

end TopCat

end
