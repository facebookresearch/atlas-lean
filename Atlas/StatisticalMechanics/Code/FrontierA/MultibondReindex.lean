/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionSheetGauge

open Finset

namespace StatMech.FrontierA

noncomputable section

variable {P P' V V' : Type*}
  [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']
  [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']


def multibondConfigReindex (eV : V ≃ V') : (V -> Bool) ≃ (V' -> Bool) where
  toFun s v := s (eV.symm v)
  invFun s v := s (eV v)
  left_inv s := by funext v; simp
  right_inv s := by funext v; simp

theorem multibondIsingWeight_reindex
    (eP : P ≃ P') (eV : V ≃ V')
    (ends : P -> V × V) (ends' : P' -> V' × V')
    (J : P -> Real) (J' : P' -> Real)
    (hJ : forall p, J' (eP p) = J p)
    (hagrees : forall p s,
      (multibondConfigReindex eV s) (ends' (eP p)).1 =
          (multibondConfigReindex eV s) (ends' (eP p)).2 <->
        s (ends p).1 = s (ends p).2)
    (s : V -> Bool) :
    multibondIsingWeight ends' J' (multibondConfigReindex eV s) =
      multibondIsingWeight ends J s := by
  unfold multibondIsingWeight
  congr 1
  rw [← Equiv.sum_comp eP]
  apply Finset.sum_congr rfl
  intro p _
  rw [hJ]
  by_cases h : s (ends p).1 = s (ends p).2
  · rw [if_pos h, if_pos ((hagrees p s).2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((hagrees p s).1 h'))]

theorem multibondIsingPartition_reindex
    (eP : P ≃ P') (eV : V ≃ V')
    (ends : P -> V × V) (ends' : P' -> V' × V')
    (J : P -> Real) (J' : P' -> Real)
    (hJ : forall p, J' (eP p) = J p)
    (hagrees : forall p s,
      (multibondConfigReindex eV s) (ends' (eP p)).1 =
          (multibondConfigReindex eV s) (ends' (eP p)).2 <->
        s (ends p).1 = s (ends p).2) :
    multibondIsingPartition ends' J' = multibondIsingPartition ends J := by
  unfold multibondIsingPartition
  rw [← Equiv.sum_comp (multibondConfigReindex eV)]
  apply Finset.sum_congr rfl
  intro s _
  exact multibondIsingWeight_reindex eP eV ends ends' J J' hJ hagrees s

theorem multibondDisorderFreeEnergy_reindex
    (eP : P ≃ P') (eV : V ≃ V')
    (ends : P -> V × V) (ends' : P' -> V' × V')
    (J : P -> Real) (J' : P' -> Real) (D : Finset P)
    (hJ : forall p, J' (eP p) = J p)
    (hagrees : forall p s,
      (multibondConfigReindex eV s) (ends' (eP p)).1 =
          (multibondConfigReindex eV s) (ends' (eP p)).2 <->
        s (ends p).1 = s (ends p).2) :
    multibondDisorderFreeEnergy ends' J' (D.map eP.toEmbedding) =
      multibondDisorderFreeEnergy ends J D := by
  unfold multibondDisorderFreeEnergy
  rw [multibondIsingPartition_reindex eP eV ends ends' J J' hJ hagrees]
  rw [multibondIsingPartition_reindex eP eV ends ends'
    (multibondTwistCoupling J D)
    (multibondTwistCoupling J' (D.map eP.toEmbedding))]
  · intro p
    simp [multibondTwistCoupling, hJ]
  · exact hagrees

end

end StatMech.FrontierA
