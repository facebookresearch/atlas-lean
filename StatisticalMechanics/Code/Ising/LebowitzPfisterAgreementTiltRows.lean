/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterAgreementTiltFKG
import Code.Walls.vbgtriangle









open Finset
open scoped BigOperators

namespace StatMech.Ising

open StatMech.Sharpness StatMech.Walls.VBG

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]



noncomputable def replicaAgreementTiltCovarianceRow
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (i : I) (r : Real) : Real :=
  vbg_cov (replicaAgreementTiltProb G J hf sites r)
    (fun q => spin q (sites i)) (replicaAgreementSpin sites)



theorem replicaBridgeVariance_eq_sum_agreementTiltCovarianceRow
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeVariance G J hf sites r =
      ∑ i : I, replicaAgreementTiltCovarianceRow G J hf sites i r := by
  rw [replicaBridgeVariance_eq_agreementTiltVariance]
  unfold replicaAgreementTiltVariance replicaAgreementTiltCovarianceRow
    vbg_cov vbg_exp replicaAgreementSpin
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  · rw [← Finset.sum_mul]
    rw [pow_two]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum]



theorem replicaBridgeVariance_le_neg_of_covarianceRows
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real)
    (hrow : forall i,
      replicaAgreementTiltCovarianceRow G J hf sites i r <=
        replicaAgreementTiltCovarianceRow G J hf sites i (-r)) :
    replicaBridgeVariance G J hf sites r <=
      replicaBridgeVariance G J hf sites (-r) := by
  rw [replicaBridgeVariance_eq_sum_agreementTiltCovarianceRow,
    replicaBridgeVariance_eq_sum_agreementTiltCovarianceRow]
  exact Finset.sum_le_sum fun i _ => hrow i

end

end StatMech.Ising
