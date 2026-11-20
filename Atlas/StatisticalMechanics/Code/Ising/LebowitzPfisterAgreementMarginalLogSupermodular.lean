/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeEndpointZero










open Finset

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghsiAgreementMarginalProb_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (M P : Finset V) :
    0 <= ghsiAgreementMarginalProb G K hf M P := by
  classical
  unfold ghsiAgreementMarginalProb
  exact Finset.sum_nonneg fun q _ => ghsiAgreementProb_nonneg G K hf q



theorem ghsiAgreementMarginalProb_sum_powerset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real) (M : Finset V) :
    (∑ P ∈ M.powerset, ghsiAgreementMarginalProb G K hf M P) = 1 := by
  classical
  rw [← ghsiAgreementProb_sum_eq_one G K hf]
  unfold ghsiAgreementMarginalProb
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun q : ConfigSpace V => ghsLAgreeFinset q ∩ M)
    (t := M.powerset)
    (fun q _ => Finset.mem_powerset.mpr inter_subset_right)]


theorem ghsiAgreementMarginalProb_logSupermodular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {M P Q : Finset V} (hPM : P ⊆ M) (hQM : Q ⊆ M) :
    ghsiAgreementMarginalProb G K hf M P *
        ghsiAgreementMarginalProb G K hf M Q <=
      ghsiAgreementMarginalProb G K hf M (P ∩ Q) *
        ghsiAgreementMarginalProb G K hf M (P ∪ Q) := by
  let C : Real := (4 * Fintype.card (ConfigSpace V) : Real) *
    (ZJ G.edgeFinset K hf) ^ 2
  have hC : 0 < C := by
    dsimp only [C]
    have hcard : (0 : Real) < Fintype.card (ConfigSpace V) := by
      exact_mod_cast Fintype.card_pos
    exact mul_pos (mul_pos (by norm_num) hcard)
      (sq_pos_of_pos (ZJ_pos G.edgeFinset K hf))
  have hinter : P ∩ Q ⊆ M := inter_subset_left.trans hPM
  have hunion : P ∪ Q ⊆ M := union_subset hPM hQM
  have hmass := ghsiSubsetMarginalMass_logSupermodular
    G K hf hK hhf hPM hQM
  rw [ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G K hf hPM,
    ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G K hf hQM,
    ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G K hf hinter,
    ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G K hf hunion] at hmass
  change C * ghsiAgreementMarginalProb G K hf M P *
      (C * ghsiAgreementMarginalProb G K hf M Q) <=
    C * ghsiAgreementMarginalProb G K hf M (P ∩ Q) *
      (C * ghsiAgreementMarginalProb G K hf M (P ∪ Q)) at hmass
  have hC2 : 0 < C ^ 2 := sq_pos_of_pos hC
  apply le_of_mul_le_mul_left _ hC2
  convert hmass using 1 <;> ring



theorem ghsiAgreementMarginalProb_compl_ratio_mono
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {M P Q : Finset V} (hPQ : P ⊆ Q) (hQM : Q ⊆ M) :
    ghsiAgreementMarginalProb G K hf M P *
        ghsiAgreementMarginalProb G K hf M (M \ Q) <=
      ghsiAgreementMarginalProb G K hf M Q *
        ghsiAgreementMarginalProb G K hf M (M \ P) := by
  let C : Real := (4 * Fintype.card (ConfigSpace V) : Real) *
    (ZJ G.edgeFinset K hf) ^ 2
  have hC : 0 < C := by
    dsimp only [C]
    have hcard : (0 : Real) < Fintype.card (ConfigSpace V) := by
      exact_mod_cast Fintype.card_pos
    exact mul_pos (mul_pos (by norm_num) hcard)
      (sq_pos_of_pos (ZJ_pos G.edgeFinset K hf))
  have hPM : P ⊆ M := hPQ.trans hQM
  have hmass := ghsiSubsetMarginalMass_compl_ratio_mono
    G K hf hK hhf hPQ hQM
  rw [ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G K hf hPM,
    ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G K hf sdiff_subset,
    ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G K hf hQM,
    ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
      G K hf sdiff_subset] at hmass
  change C * ghsiAgreementMarginalProb G K hf M P *
      (C * ghsiAgreementMarginalProb G K hf M (M \ Q)) <=
    C * ghsiAgreementMarginalProb G K hf M Q *
      (C * ghsiAgreementMarginalProb G K hf M (M \ P)) at hmass
  have hC2 : 0 < C ^ 2 := sq_pos_of_pos hC
  apply le_of_mul_le_mul_left _ hC2
  convert hmass using 1 <;> ring



theorem ghsiAgreementMarginalProb_weightedCut_sum_le
    {I : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (M : Finset V) (cuts : Finset I)
    (weight : I -> Real) (P Q : I -> Finset V)
    (hweight : forall i, i ∈ cuts -> 0 <= weight i)
    (hP : forall i, i ∈ cuts -> P i ⊆ M)
    (hQ : forall i, i ∈ cuts -> Q i ⊆ M) :
    (∑ i ∈ cuts, weight i *
        (ghsiAgreementMarginalProb G K hf M (P i) *
          ghsiAgreementMarginalProb G K hf M (Q i))) <=
      ∑ i ∈ cuts, weight i *
        (ghsiAgreementMarginalProb G K hf M (P i ∩ Q i) *
          ghsiAgreementMarginalProb G K hf M (P i ∪ Q i)) := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (ghsiAgreementMarginalProb_logSupermodular
      G K hf hK hhf (hP i hi) (hQ i hi)) (hweight i hi)


theorem ghsiAgreementMarginalProb_weightedComplRatio_sum_le
    {I : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (M : Finset V) (cuts : Finset I)
    (weight : I -> Real) (P Q : I -> Finset V)
    (hweight : forall i, i ∈ cuts -> 0 <= weight i)
    (hPQ : forall i, i ∈ cuts -> P i ⊆ Q i)
    (hQM : forall i, i ∈ cuts -> Q i ⊆ M) :
    (∑ i ∈ cuts, weight i *
        (ghsiAgreementMarginalProb G K hf M (P i) *
          ghsiAgreementMarginalProb G K hf M (M \ Q i))) <=
      ∑ i ∈ cuts, weight i *
        (ghsiAgreementMarginalProb G K hf M (Q i) *
          ghsiAgreementMarginalProb G K hf M (M \ P i)) := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (ghsiAgreementMarginalProb_compl_ratio_mono
      G K hf hK hhf (hPQ i hi) (hQM i hi)) (hweight i hi)

end

end StatMech.Ising
