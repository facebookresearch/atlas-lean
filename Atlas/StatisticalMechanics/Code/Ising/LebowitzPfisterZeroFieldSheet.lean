/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.LebowitzPfisterReflectionGauge

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]




theorem replicaBridgeMoment_zeroField_neg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (sites : I -> V) (r : Real) :
    replicaBridgeMoment G J (fun _ => 0) sites (-r) =
      replicaBridgeMoment G J (fun _ => 0) sites r := by
  rw [replicaBridgeMoment_neg_eq_cross_negField]
  have hfield : (fun x : V => -(0 : Real)) = (fun _ => 0) := by
    funext x
    simp
  rw [hfield, replicaCrossBridgeMoment_same]



@[simp] theorem replicaBridgeFreeEnergy_zeroField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (sites : I -> V) (r : Real) :
    replicaBridgeFreeEnergy G J (fun _ => 0) sites r = 0 := by
  unfold replicaBridgeFreeEnergy
  rw [replicaBridgeMoment_zeroField_neg]
  ring



theorem replicaBridgeVariance_zeroField_neg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (sites : I -> V) (r : Real) :
    replicaBridgeVariance G J (fun _ => 0) sites (-r) =
      replicaBridgeVariance G J (fun _ => 0) sites r := by
  rw [replicaBridgeVariance_neg_eq_cross_negField]
  have hfield : (fun x : V => -(0 : Real)) = (fun _ => 0) := by
    funext x
    simp
  rw [hfield, replicaCrossBridgeVariance_same]




theorem replicaBridgeFreeEnergy_zeroField_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (sites : I -> V) (r : Real) (hr : 0 <= r) :
    replicaBridgeFreeEnergy G J (fun _ => 0) sites r <=
      2 * r * ∑ i : I,
        (expJ G.edgeFinset J (fun _ => 0)
          (fun s => spin s (sites i))) ^ 2 := by
  rw [replicaBridgeFreeEnergy_zeroField]
  exact mul_nonneg (mul_nonneg (by norm_num) hr)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

end

end StatMech.Ising
