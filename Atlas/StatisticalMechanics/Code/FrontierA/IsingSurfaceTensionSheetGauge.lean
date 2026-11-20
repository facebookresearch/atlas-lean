/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionBoundaryBridge

open Finset
open scoped BigOperators symmDiff

namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def multibondConfigXor (t s : V -> Bool) : V -> Bool :=
  fun v => (s v).xor (t v)



def multibondConfigXorEquiv (t : V -> Bool) :
    (V -> Bool) ≃ (V -> Bool) where
  toFun := multibondConfigXor t
  invFun := multibondConfigXor t
  left_inv s := by
    funext v
    simp [multibondConfigXor, Bool.xor_assoc]
  right_inv s := by
    funext v
    simp [multibondConfigXor, Bool.xor_assoc]



theorem multibondCut_configXor
    (ends : P -> V × V) (s t : V -> Bool) :
    multibondCut ends (multibondConfigXor t s) =
      multibondCut ends s ∆ multibondCut ends t := by
  ext p
  simp only [mem_multibondCut, Finset.mem_symmDiff]
  cases hs1 : s (ends p).1 <;> cases hs2 : s (ends p).2 <;>
    cases ht1 : t (ends p).1 <;> cases ht2 : t (ends p).2 <;>
    simp [multibondConfigXor, hs1, hs2, ht1, ht2]



theorem multibondIsingWeight_twist_symmDiff_cut_configXor
    (ends : P -> V × V) (J : P -> Real) (D : Finset P)
    (s t : V -> Bool) :
    multibondIsingWeight ends
        (multibondTwistCoupling J (D ∆ multibondCut ends t))
        (multibondConfigXor t s) =
      multibondIsingWeight ends (multibondTwistCoupling J D) s := by
  unfold multibondIsingWeight
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  simp only [multibondTwistCoupling]
  by_cases hpD : p ∈ D <;>
    cases hs1 : s (ends p).1 <;> cases hs2 : s (ends p).2 <;>
    cases ht1 : t (ends p).1 <;> cases ht2 : t (ends p).2 <;>
    simp [multibondConfigXor, multibondCut, Finset.mem_symmDiff,
      hpD, hs1, hs2, ht1, ht2]



theorem multibondIsingPartition_twist_symmDiff_cut
    (ends : P -> V × V) (J : P -> Real) (D : Finset P)
    (t : V -> Bool) :
    multibondIsingPartition ends
        (multibondTwistCoupling J (D ∆ multibondCut ends t)) =
      multibondIsingPartition ends (multibondTwistCoupling J D) := by
  unfold multibondIsingPartition
  rw [← Equiv.sum_comp (multibondConfigXorEquiv t)]
  apply Finset.sum_congr rfl
  intro s _
  exact multibondIsingWeight_twist_symmDiff_cut_configXor ends J D s t



theorem multibondDisorderFreeEnergy_symmDiff_cut
    (ends : P -> V × V) (J : P -> Real) (D : Finset P)
    (t : V -> Bool) :
    multibondDisorderFreeEnergy ends J
        (D ∆ multibondCut ends t) =
      multibondDisorderFreeEnergy ends J D := by
  unfold multibondDisorderFreeEnergy
  rw [multibondIsingPartition_twist_symmDiff_cut]

end

end StatMech.FrontierA
