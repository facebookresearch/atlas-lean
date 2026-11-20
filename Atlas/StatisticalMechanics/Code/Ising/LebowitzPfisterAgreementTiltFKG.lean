/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.LebowitzPfisterThreeBridgeObstruction

open Finset

namespace StatMech.Ising

open StatMech StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]



theorem replicaAgreementSpin_sup_add_inf
    (sites : I -> V) (q s : ConfigSpace V) :
    replicaAgreementSpin sites (q ⊔ s) +
        replicaAgreementSpin sites (q ⊓ s) =
      replicaAgreementSpin sites q + replicaAgreementSpin sites s := by
  unfold replicaAgreementSpin
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hq : q (sites i) <;> cases hs : s (sites i) <;>
    simp [spin, hq, hs]


theorem replicaAgreementTiltFactor_logModular
    (sites : I -> V) (r : Real) (q s : ConfigSpace V) :
    Real.exp (r * replicaAgreementSpin sites q) *
        Real.exp (r * replicaAgreementSpin sites s) =
      Real.exp (r * replicaAgreementSpin sites (q ⊔ s)) *
        Real.exp (r * replicaAgreementSpin sites (q ⊓ s)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [← mul_add, ← mul_add, replicaAgreementSpin_sup_add_inf]



theorem replicaAgreementTiltProb_fkg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall x, 0 <= hf x)
    (sites : I -> V) (r : Real) :
    FKGLatticeCondition (replicaAgreementTiltProb G J hf sites r) := by
  intro q s
  have hbase := ghsiAgreementProb_fkg G J hf hJ hhf q s
  have htilt := replicaAgreementTiltFactor_logModular sites r q s
  have hmoment0 : 0 <= replicaBridgeMoment G J hf sites r :=
    (replicaBridgeMoment_pos G J hf sites r).le
  unfold replicaAgreementTiltProb
  rw [div_mul_div_comm, div_mul_div_comm]
  apply div_le_div_of_nonneg_right _ (mul_nonneg hmoment0 hmoment0)
  calc
    (ghsiAgreementProb G J hf q *
          Real.exp (r * replicaAgreementSpin sites q)) *
        (ghsiAgreementProb G J hf s *
          Real.exp (r * replicaAgreementSpin sites s)) =
      (ghsiAgreementProb G J hf q * ghsiAgreementProb G J hf s) *
        (Real.exp (r * replicaAgreementSpin sites q) *
          Real.exp (r * replicaAgreementSpin sites s)) := by ring
    _ <= (ghsiAgreementProb G J hf (q ⊓ s) *
          ghsiAgreementProb G J hf (q ⊔ s)) *
        (Real.exp (r * replicaAgreementSpin sites q) *
          Real.exp (r * replicaAgreementSpin sites s)) :=
      mul_le_mul_of_nonneg_right (by simpa [mul_comm] using hbase)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = (ghsiAgreementProb G J hf (q ⊔ s) *
          Real.exp (r * replicaAgreementSpin sites (q ⊔ s))) *
        (ghsiAgreementProb G J hf (q ⊓ s) *
          Real.exp (r * replicaAgreementSpin sites (q ⊓ s))) := by
      rw [htilt]
      ring



theorem replicaAgreementTilt_fkg_inequality
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall x, 0 <= hf x)
    (sites : I -> V) (r : Real)
    {f g : ConfigSpace V -> Real} (hfmono : Monotone f) (hgmono : Monotone g) :
    (∑ q, replicaAgreementTiltProb G J hf sites r q * f q) *
        (∑ q, replicaAgreementTiltProb G J hf sites r q * g q) <=
      ∑ q, replicaAgreementTiltProb G J hf sites r q * (f q * g q) := by
  exact StatMech.fkg_inequality
    (fun q => div_nonneg
      (mul_nonneg (ghsiAgreementProb_nonneg G J hf q) (Real.exp_pos _).le)
      (replicaBridgeMoment_pos G J hf sites r).le)
    (replicaAgreementTiltProb_sum_eq_one G J hf sites r)
    (replicaAgreementTiltProb_fkg G J hf hJ hhf sites r)
    hfmono hgmono

end

end StatMech.Ising
