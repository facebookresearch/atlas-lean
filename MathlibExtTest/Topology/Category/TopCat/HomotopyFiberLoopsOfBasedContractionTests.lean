/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopsOfBasedContraction
import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopPointPairEquivalence

/-! Actual arbitrary-total-space consumers of the full homotopy-fiber/loop inverse. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval Topology.Homotopy

universe u

#check TopCat.homotopyFiberToLoopsOfBasedContraction
#print axioms TopCat.homotopyFiberToLoopsOfBasedContraction
#check TopCat.homotopyFiberToLoopsOfBasedContraction_apply
#print axioms TopCat.homotopyFiberToLoopsOfBasedContraction_apply
#check TopCat.homotopyFiberToLoopsOfBasedContraction_selectedPoint
#print axioms TopCat.homotopyFiberToLoopsOfBasedContraction_selectedPoint
#check TopCat.homotopyFiberLoopEquivOfBasedContraction
#print axioms TopCat.homotopyFiberLoopEquivOfBasedContraction
#check TopCat.homotopyFiberLoopEquivOfBasedContraction_toFun
#print axioms TopCat.homotopyFiberLoopEquivOfBasedContraction_toFun
#check TopCat.homotopyFiberLoopEquivOfBasedContraction_invFun
#print axioms TopCat.homotopyFiberLoopEquivOfBasedContraction_invFun

section
variable {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
  (he : p e = b) (C : TopCat.BasedContraction E e)

example :
    (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun =
      (TopCat.loopToHomotopyFiber p e b he).hom :=
  TopCat.homotopyFiberLoopEquivOfBasedContraction_invFun p e b he C

example (z : TopCat.homotopyFiber p b) (t : unitInterval) :
    (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun z t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        p (C.homotopy.symm.toContinuousMap
          (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
            TopCat.homotopyFiberToTotal p b z))
      else
        TopCat.homotopyFiberPath p b z
          ((TopCat.I.homeomorph.{u}).symm
            ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩) := by
  rw [TopCat.homotopyFiberLoopEquivOfBasedContraction_toFun]
  exact TopCat.homotopyFiberToLoopsOfBasedContraction_apply p e b he C z t

example : Continuous (fun z : TopCat.homotopyFiber p b × unitInterval =>
    (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun z.1 z.2) :=
  Path.continuous_uncurry_iff.mpr
    (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun.continuous

example : Nonempty (ContinuousMap.Homotopy
    ((TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun.comp
      (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun)
    (ContinuousMap.id (TopCat.homotopyFiber p b))) :=
  (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).left_inv

example : Nonempty (ContinuousMap.Homotopy
    ((TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun.comp
      (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun)
    (ContinuousMap.id (LoopSpace B b))) :=
  (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).right_inv

example :
    (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun
        (TopCat.homotopyFiberSelectedPointMap p e b he PUnit.unit) =
      Path.refl b := by
  rw [TopCat.homotopyFiberLoopEquivOfBasedContraction_toFun]
  exact ConcreteCategory.congr_hom
    (TopCat.homotopyFiberToLoopsOfBasedContraction_selectedPoint p e b he C) PUnit.unit

example :
    (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun (Path.refl b) =
      TopCat.homotopyFiberSelectedPointMap p e b he PUnit.unit := by
  rw [TopCat.homotopyFiberLoopEquivOfBasedContraction_invFun]
  exact ConcreteCategory.congr_hom
    (TopCat.loopToHomotopyFiber_constant_point p e b he) PUnit.unit
end
#check TopCat.homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel
#print axioms TopCat.homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel
#check TopCat.homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel
#print axioms TopCat.homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel
#check TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction
#print axioms TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction
#check TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_hom_fst
#print axioms TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_hom_fst
#check TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_inv_fst
#print axioms TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_inv_fst

section
variable {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
  (he : p e = b) (C : TopCat.BasedContraction E e)

example (s : unitInterval) :
    TopCat.homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel p e b he C
        (s, TopCat.homotopyFiberSelectedPointMap p e b he PUnit.unit) =
      TopCat.homotopyFiberSelectedPointMap p e b he PUnit.unit :=
  (TopCat.homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel p e b he C).eq_snd
    s (Set.mem_singleton_iff.mpr rfl)

example (s : unitInterval) :
    TopCat.homotopyFiberPath p b
        (TopCat.homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel p e b he C
          (s, TopCat.homotopyFiberSelectedPointMap p e b he PUnit.unit)) =
      ContinuousMap.const TopCat.I.{u} b := by
  have fixed :=
    (TopCat.homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel p e b he C).eq_snd
      s (Set.mem_singleton_iff.mpr rfl)
  exact (congrArg (TopCat.homotopyFiberPath p b) fixed).trans
    (ConcreteCategory.congr_hom
      (TopCat.homotopyFiberSelectedPointMap_path p e b he) PUnit.unit)

example (s : unitInterval) :
    TopCat.homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel p e b he C
      (s, Path.refl b) = Path.refl b :=
  (TopCat.homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel p e b he C).eq_snd
    s (Set.mem_singleton_iff.mpr rfl)

example (z : TopCat.homotopyFiber p b) :
    TopCat.homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel p e b he C (1, z) = z :=
  (TopCat.homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel p e b he C).toHomotopy.apply_one
    z

example (gamma : LoopSpace B b) :
    TopCat.homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel p e b he C (1, gamma) =
      gamma :=
  (TopCat.homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel p e b he C).toHomotopy.apply_one
    gamma

example :
    (TopPair.Hom.fst
      (TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction p e b he C).hom).hom =
      (TopCat.homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun :=
  TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_hom_fst p e b he C

example :
    (TopPair.Hom.fst
      (TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction p e b he C).inv).hom =
      (TopCat.loopToHomotopyFiber p e b he).hom := by
  exact TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_inv_fst p e b he C
end
