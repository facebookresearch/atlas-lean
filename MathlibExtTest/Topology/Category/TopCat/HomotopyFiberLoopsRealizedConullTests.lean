/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopsRealizedConull
import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopPointPairEquivalence

/-! Genuine consumers of the full raw homotopy-fiber/loop inverse. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval Topology.Homotopy Simplicial

universe u

#check TopCat.homotopyFiberToLoopsOfRealizedConull
#print axioms TopCat.homotopyFiberToLoopsOfRealizedConull
#check TopCat.homotopyFiberToLoopsOfRealizedConull_apply
#print axioms TopCat.homotopyFiberToLoopsOfRealizedConull_apply
#check TopCat.homotopyFiberToLoopsOfRealizedConull_selectedPoint
#print axioms TopCat.homotopyFiberToLoopsOfRealizedConull_selectedPoint
#check TopCat.realizedConullHomotopyFiberLoopEquiv
#print axioms TopCat.realizedConullHomotopyFiberLoopEquiv
#check TopCat.realizedConullHomotopyFiberLoopEquiv_toFun
#print axioms TopCat.realizedConullHomotopyFiberLoopEquiv_toFun
#check TopCat.realizedConullHomotopyFiberLoopEquiv_invFun
#print axioms TopCat.realizedConullHomotopyFiberLoopEquiv_invFun

section
variable (K : SSet.{u}) (x : K _⦋0⦌) {B : TopCat.{u}}
  (p : SSet.toTop.obj K ⟶ B) (b : B)
  (he : p (SSet.realizedVertex x) = b)
  (hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)))

example :
    (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).invFun =
      (TopCat.loopToHomotopyFiber p (SSet.realizedVertex x) b he).hom :=
  TopCat.realizedConullHomotopyFiberLoopEquiv_invFun K x p b he hK

example (z : TopCat.homotopyFiber p b) (t : unitInterval) :
    (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun z t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        p ((SSet.basedContractionAtRealizedVertex K x hK).homotopy.symm.toContinuousMap
          (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
            TopCat.homotopyFiberToTotal p b z))
      else
        TopCat.homotopyFiberPath p b z
          ((TopCat.I.homeomorph.{u}).symm
            ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩) := by
  rw [TopCat.realizedConullHomotopyFiberLoopEquiv_toFun]
  exact TopCat.homotopyFiberToLoopsOfRealizedConull_apply K x p b he hK z t

example : Continuous (fun z : TopCat.homotopyFiber p b × unitInterval =>
    (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun z.1 z.2) :=
  Path.continuous_uncurry_iff.mpr
    (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun.continuous

example : Nonempty (ContinuousMap.Homotopy
    ((TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).invFun.comp
      (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun)
    (ContinuousMap.id (TopCat.homotopyFiber p b))) :=
  (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).left_inv

example : Nonempty (ContinuousMap.Homotopy
    ((TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun.comp
      (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).invFun)
    (ContinuousMap.id (LoopSpace B b))) :=
  (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).right_inv

example :
    (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun
        (TopCat.homotopyFiberSelectedPointMap p (SSet.realizedVertex x) b he PUnit.unit) =
      Path.refl b := by
  rw [TopCat.realizedConullHomotopyFiberLoopEquiv_toFun]
  exact ConcreteCategory.congr_hom
    (TopCat.homotopyFiberToLoopsOfRealizedConull_selectedPoint K x p b he hK) PUnit.unit

example :
    (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).invFun (Path.refl b) =
      TopCat.homotopyFiberSelectedPointMap p (SSet.realizedVertex x) b he PUnit.unit := by
  rw [TopCat.realizedConullHomotopyFiberLoopEquiv_invFun]
  exact ConcreteCategory.congr_hom
    (TopCat.loopToHomotopyFiber_constant_point p (SSet.realizedVertex x) b he) PUnit.unit
end
#check TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel
#print axioms TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel
#check TopCat.realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel
#print axioms TopCat.realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel
#check TopCat.realizedConullHomotopyFiberLoopPointPairEquiv
#print axioms TopCat.realizedConullHomotopyFiberLoopPointPairEquiv

section
variable (K : SSet.{u}) (x : K _⦋0⦌) {B : TopCat.{u}}
  (p : SSet.toTop.obj K ⟶ B) (b : B)
  (he : p (SSet.realizedVertex x) = b)
  (hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)))

example (s : unitInterval) :
    TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel K x p b he hK
        (s, TopCat.homotopyFiberSelectedPointMap p (SSet.realizedVertex x) b he PUnit.unit) =
      TopCat.homotopyFiberSelectedPointMap p (SSet.realizedVertex x) b he PUnit.unit :=
  (TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel K x p b he hK).eq_snd
    s (Set.mem_singleton_iff.mpr rfl)

example (s : unitInterval) :
    TopCat.homotopyFiberPath p b
        (TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel K x p b he hK
          (s, TopCat.homotopyFiberSelectedPointMap p (SSet.realizedVertex x) b he PUnit.unit)) =
      ContinuousMap.const TopCat.I.{u} b := by
  have fixed :=
    (TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel K x p b he hK).eq_snd
      s (Set.mem_singleton_iff.mpr rfl)
  exact (congrArg (TopCat.homotopyFiberPath p b) fixed).trans
    (ConcreteCategory.congr_hom
      (TopCat.homotopyFiberSelectedPointMap_path p (SSet.realizedVertex x) b he) PUnit.unit)

example (s : unitInterval) :
    TopCat.realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel K x p b he hK
      (s, Path.refl b) = Path.refl b :=
  (TopCat.realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel K x p b he hK).eq_snd
    s (Set.mem_singleton_iff.mpr rfl)

example (z : TopCat.homotopyFiber p b) :
    TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel K x p b he hK (1, z) = z :=
  (TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel K x p b he hK).toHomotopy.apply_one z

example (gamma : LoopSpace B b) :
    TopCat.realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel K x p b he hK (1, gamma) =
      gamma :=
  (TopCat.realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel K x p b he hK).toHomotopy.apply_one gamma

example :
    (TopPair.Hom.fst
      (TopCat.realizedConullHomotopyFiberLoopPointPairEquiv K x p b he hK).hom).hom =
      (TopCat.realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun := by
  change (TopPair.Hom.fst
    (TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction p (SSet.realizedVertex x) b he
      (SSet.basedContractionAtRealizedVertex K x hK)).hom).hom = _
  rw [TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_hom_fst,
    TopCat.homotopyFiberLoopEquivOfBasedContraction_toFun,
    TopCat.realizedConullHomotopyFiberLoopEquiv_toFun]
  apply ContinuousMap.ext
  intro z
  apply _root_.Path.ext
  funext t
  rw [TopCat.homotopyFiberToLoopsOfBasedContraction_apply,
    TopCat.homotopyFiberToLoopsOfRealizedConull_apply]

example :
    (TopPair.Hom.fst
      (TopCat.realizedConullHomotopyFiberLoopPointPairEquiv K x p b he hK).inv).hom =
      (TopCat.loopToHomotopyFiber p (SSet.realizedVertex x) b he).hom := by
  change (TopPair.Hom.fst
    (TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction p (SSet.realizedVertex x) b he
      (SSet.basedContractionAtRealizedVertex K x hK)).inv).hom = _
  exact TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_inv_fst
    p (SSet.realizedVertex x) b he (SSet.basedContractionAtRealizedVertex K x hK)
end
