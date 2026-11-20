/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeSingletonCuts











open Finset

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem ghsiAgreementProb_pos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real) (q : ConfigSpace V) :
    0 < ghsiAgreementProb G K hf q := by
  unfold ghsiAgreementProb
  exact div_pos (ghsiFibreMass_pos G K hf q)
    (sq_pos_of_pos (ZJ_pos G.edgeFinset K hf))




theorem ghsiAgreementMarginalProb_pos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    {M P : Finset V} (hPM : P ⊆ M) :
    0 < ghsiAgreementMarginalProb G K hf M P := by
  classical
  let q : ConfigSpace V := agreementConfigFinsetEquiv.symm P
  have hq : q ∈ (Finset.univ : Finset (ConfigSpace V)).filter
      (fun r => ghsLAgreeFinset r ∩ M = P) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have heq : ghsLAgreeFinset (agreementConfigFinsetEquiv.symm P) = P :=
      agreementConfigFinsetEquiv.apply_symm_apply P
    rw [heq]
    exact Finset.inter_eq_left.mpr hPM
  unfold ghsiAgreementMarginalProb
  exact Finset.sum_pos'
    (fun r _ => ghsiAgreementProb_nonneg G K hf r)
    ⟨q, hq, ghsiAgreementProb_pos G K hf q⟩



theorem mul_mul_le_of_cancellativeCuts
    {x0 x1 x3 x12 x13 x15 : Real}
    (hx0 : 0 < x0) (hx12 : 0 < x12)
    (hx3 : 0 <= x3) (hx13 : 0 <= x13)
    (hlog : x1 * x12 <= x0 * x13)
    (hcompl : x0 * x3 <= x12 * x15) :
    x1 * x3 <= x13 * x15 := by
  have hmul := mul_le_mul hlog hcompl
    (mul_nonneg hx0.le hx3) (mul_nonneg hx0.le hx13)
  apply le_of_mul_le_mul_left (a := x0 * x12) _ (mul_pos hx0 hx12)
  calc
    (x0 * x12) * (x1 * x3) = (x1 * x12) * (x0 * x3) := by ring
    _ <= (x0 * x13) * (x12 * x15) := hmul
    _ = (x0 * x12) * (x13 * x15) := by ring





theorem ghsiAgreementMarginalProb_disjoint_cancellativeCut
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {M A B : Finset V} (hAM : A ⊆ M) (hBM : B ⊆ M)
    (hAB : Disjoint A B) :
    ghsiAgreementMarginalProb G K hf M A *
        ghsiAgreementMarginalProb G K hf M (M \ B) <=
      ghsiAgreementMarginalProb G K hf M (A ∪ B) *
        ghsiAgreementMarginalProb G K hf M M := by
  let mu := ghsiAgreementMarginalProb G K hf M
  have hlog := ghsiAgreementMarginalProb_logSupermodular
    G K hf hK hhf hAM hBM
  have hinter : A ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hAB
  rw [hinter] at hlog
  have hcompl := ghsiAgreementMarginalProb_compl_ratio_mono
    G K hf hK hhf (M := M) (P := ∅) (Q := B) (empty_subset _) hBM
  have hcompl' : mu ∅ * mu (M \ B) <= mu B * mu M := by
    simpa only [mu, sdiff_empty] using hcompl
  have hzero : 0 < mu ∅ := ghsiAgreementMarginalProb_pos
    G K hf (empty_subset M)
  have hB : 0 < mu B := ghsiAgreementMarginalProb_pos G K hf hBM
  exact mul_mul_le_of_cancellativeCuts hzero hB
    (ghsiAgreementMarginalProb_nonneg G K hf M (M \ B))
    (ghsiAgreementMarginalProb_nonneg G K hf M (A ∪ B))
    hlog hcompl'

end

end StatMech.Ising
