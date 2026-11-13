/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.BeffaraDC.Duality
import Code.FK.EdgeMarginal















open scoped BigOperators

namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem selfDualPoint_odds {q : Real} (hq : 0 < q) :
    BeffaraDC.selfDualPoint q / (1 - BeffaraDC.selfDualPoint q) =
      Real.sqrt q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  unfold BeffaraDC.selfDualPoint
  field_simp
  ring

omit [DecidableEq V] in


theorem edgeProduct_selfDualPoint_eq_common_mul_sqrt_pow
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    edgeProduct G (BeffaraDC.selfDualPoint q) omega =
      (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
        (Real.sqrt q) ^ openCount G omega := by
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq
  rw [BeffaraDC.dlt_edgeProduct_eq_count,
    BeffaraDC.dlt_edgeProductCount_yates hp1]
  · rw [selfDualPoint_odds hq]
  · exact Finset.card_filter_le _ _

omit [DecidableEq V] in


theorem bcWeight_selfDualPoint_eq_common_mul_sqrt_pow_score
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    bcWeight G C (BeffaraDC.selfDualPoint q) q omega =
      (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
        (Real.sqrt q) ^
          (openCount G omega + 2 * numClustersBC G C omega) := by
  unfold bcWeight
  rw [edgeProduct_selfDualPoint_eq_common_mul_sqrt_pow G hq]
  have hqpow : q ^ numClustersBC G C omega =
      (Real.sqrt q) ^ (2 * numClustersBC G C omega) := by
    calc
      q ^ numClustersBC G C omega =
          ((Real.sqrt q) ^ 2) ^ numClustersBC G C omega :=
        congrArg (fun x : Real => x ^ numClustersBC G C omega)
          (Real.sq_sqrt hq.le).symm
      _ = (Real.sqrt q) ^ (2 * numClustersBC G C omega) := by
        rw [pow_mul]
  rw [hqpow]
  calc
    (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
          (Real.sqrt q) ^ openCount G omega *
        (Real.sqrt q) ^ (2 * numClustersBC G C omega) =
      (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
        ((Real.sqrt q) ^ openCount G omega *
          (Real.sqrt q) ^ (2 * numClustersBC G C omega)) := by ring
    _ = _ := by rw [← pow_add]

omit [DecidableEq V] in


theorem bcWeight_selfDualPoint_le_sqrt_pow_of_score_le
    (G C D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    {q : Real} (hq : 1 <= q) (N : Nat)
    (omega eta : ConfigSpace (Sym2 V))
    (hscore : openCount G omega + 2 * numClustersBC G C omega <=
      openCount G eta + 2 * numClustersBC G D eta + N) :
    bcWeight G C (BeffaraDC.selfDualPoint q) q omega <=
      (Real.sqrt q) ^ N *
        bcWeight G D (BeffaraDC.selfDualPoint q) q eta := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hs0 : 0 <= Real.sqrt q := Real.sqrt_nonneg q
  have hs1 : 1 <= Real.sqrt q :=
    (Real.le_sqrt (by norm_num) hq0.le).2 (by simpa using hq)
  obtain ⟨_hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  have hcommon : 0 <=
      (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card :=
    pow_nonneg (sub_nonneg.mpr hp1.le) _
  rw [bcWeight_selfDualPoint_eq_common_mul_sqrt_pow_score G C hq0,
    bcWeight_selfDualPoint_eq_common_mul_sqrt_pow_score G D hq0]
  have hpowRaw : (Real.sqrt q) ^
        (openCount G omega + 2 * numClustersBC G C omega) <=
      (Real.sqrt q) ^
        (openCount G eta + 2 * numClustersBC G D eta + N) :=
    pow_le_pow_right₀ hs1 hscore
  have hpow : (Real.sqrt q) ^
        (openCount G omega + 2 * numClustersBC G C omega) <=
      (Real.sqrt q) ^
          (openCount G eta + 2 * numClustersBC G D eta) *
        (Real.sqrt q) ^ N := by
    rw [← pow_add]
    exact hpowRaw
  calc
    (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
        (Real.sqrt q) ^
          (openCount G omega + 2 * numClustersBC G C omega) <=
      (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
        ((Real.sqrt q) ^
          (openCount G eta + 2 * numClustersBC G D eta) *
            (Real.sqrt q) ^ N) :=
      mul_le_mul_of_nonneg_left hpow hcommon
    _ = (Real.sqrt q) ^ N *
        ((1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
          (Real.sqrt q) ^
            (openCount G eta + 2 * numClustersBC G D eta)) := by ring

omit [DecidableEq V] in



theorem bcWeight_selfDualPoint_le_qpow_of_score_le
    (G C D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    {q : Real} (hq : 1 <= q) (N : Nat)
    (omega eta : ConfigSpace (Sym2 V))
    (hscore : openCount G omega + 2 * numClustersBC G C omega <=
      openCount G eta + 2 * numClustersBC G D eta + N) :
    bcWeight G C (BeffaraDC.selfDualPoint q) q omega <=
      q ^ N * bcWeight G D (BeffaraDC.selfDualPoint q) q eta := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hs0 : 0 <= Real.sqrt q := Real.sqrt_nonneg q
  have hs1 : 1 <= Real.sqrt q :=
    (Real.le_sqrt (by norm_num) hq0.le).2 (by simpa using hq)
  have hsq : Real.sqrt q <= q := by
    apply (Real.sqrt_le_left hq0.le).2
    nlinarith [mul_nonneg hq0.le (sub_nonneg.mpr hq)]
  obtain ⟨_hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  have hcommon : 0 <=
      (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card := by
    exact pow_nonneg (sub_nonneg.mpr hp1.le) _
  rw [bcWeight_selfDualPoint_eq_common_mul_sqrt_pow_score G C hq0,
    bcWeight_selfDualPoint_eq_common_mul_sqrt_pow_score G D hq0]
  have hpowRaw : (Real.sqrt q) ^
        (openCount G omega + 2 * numClustersBC G C omega) <=
      (Real.sqrt q) ^
        (openCount G eta + 2 * numClustersBC G D eta + N) :=
    pow_le_pow_right₀ hs1 hscore
  have hpow : (Real.sqrt q) ^
        (openCount G omega + 2 * numClustersBC G C omega) <=
      (Real.sqrt q) ^
          (openCount G eta + 2 * numClustersBC G D eta) *
        (Real.sqrt q) ^ N := by
    rw [← pow_add]
    exact hpowRaw
  have hN : (Real.sqrt q) ^ N <= q ^ N :=
    pow_le_pow_left₀ hs0 hsq N
  calc
    (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
        (Real.sqrt q) ^
          (openCount G omega + 2 * numClustersBC G C omega) <=
      (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
        ((Real.sqrt q) ^
          (openCount G eta + 2 * numClustersBC G D eta) *
            (Real.sqrt q) ^ N) :=
      mul_le_mul_of_nonneg_left hpow hcommon
    _ <= (1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
        ((Real.sqrt q) ^
          (openCount G eta + 2 * numClustersBC G D eta) * q ^ N) := by
      apply mul_le_mul_of_nonneg_left _ hcommon
      exact mul_le_mul_of_nonneg_left hN (pow_nonneg hs0 _)
    _ = q ^ N *
        ((1 - BeffaraDC.selfDualPoint q) ^ G.edgeFinset.card *
          (Real.sqrt q) ^
            (openCount G eta + 2 * numClustersBC G D eta)) := by ring




theorem bcProb_selfDualPoint_le_qpow_of_score_le
    (G C D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (hCD : C <= D) {q : Real} (hq : 1 <= q) (N : Nat)
    (omega eta : ConfigSpace (Sym2 V))
    (hscore : openCount G omega + 2 * numClustersBC G C omega <=
      openCount G eta + 2 * numClustersBC G D eta + N) :
    bcProb G C (BeffaraDC.selfDualPoint q) q omega <=
      q ^ N * bcProb G D (BeffaraDC.selfDualPoint q) q eta := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  have hZC : 0 < bcZ G C (BeffaraDC.selfDualPoint q) q :=
    bcZ_pos G C hp hp1 hq0
  have hZD : 0 < bcZ G D (BeffaraDC.selfDualPoint q) q :=
    bcZ_pos G D hp hp1 hq0
  have hZ : bcZ G D (BeffaraDC.selfDualPoint q) q <=
      bcZ G C (BeffaraDC.selfDualPoint q) q := by
    unfold bcZ
    exact Finset.sum_le_sum fun rho _ =>
      bcWeight_antitone G C D hCD hp hp1 hq rho
  have hweight := bcWeight_selfDualPoint_le_qpow_of_score_le
    G C D hq N omega eta hscore
  unfold bcProb
  calc
    bcWeight G C (BeffaraDC.selfDualPoint q) q omega /
        bcZ G C (BeffaraDC.selfDualPoint q) q <=
      (q ^ N * bcWeight G D (BeffaraDC.selfDualPoint q) q eta) /
        bcZ G C (BeffaraDC.selfDualPoint q) q := by
      exact div_le_div_of_nonneg_right hweight hZC.le
    _ <= (q ^ N * bcWeight G D (BeffaraDC.selfDualPoint q) q eta) /
        bcZ G D (BeffaraDC.selfDualPoint q) q := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (pow_nonneg (by linarith) N)
          (bcWeight_nonneg G D hp hp1 hq0 eta)) hZD hZ
    _ = q ^ N *
        (bcWeight G D (BeffaraDC.selfDualPoint q) q eta /
          bcZ G D (BeffaraDC.selfDualPoint q) q) := by ring




theorem bcProb_selfDualPoint_le_sqrt_pow_of_score_le
    (G C D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (hCD : C <= D) {q : Real} (hq : 1 <= q) (N : Nat)
    (omega eta : ConfigSpace (Sym2 V))
    (hscore : openCount G omega + 2 * numClustersBC G C omega <=
      openCount G eta + 2 * numClustersBC G D eta + N) :
    bcProb G C (BeffaraDC.selfDualPoint q) q omega <=
      (Real.sqrt q) ^ N *
        bcProb G D (BeffaraDC.selfDualPoint q) q eta := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  have hZC : 0 < bcZ G C (BeffaraDC.selfDualPoint q) q :=
    bcZ_pos G C hp hp1 hq0
  have hZD : 0 < bcZ G D (BeffaraDC.selfDualPoint q) q :=
    bcZ_pos G D hp hp1 hq0
  have hZ : bcZ G D (BeffaraDC.selfDualPoint q) q <=
      bcZ G C (BeffaraDC.selfDualPoint q) q := by
    unfold bcZ
    exact Finset.sum_le_sum fun rho _ =>
      bcWeight_antitone G C D hCD hp hp1 hq rho
  have hweight := bcWeight_selfDualPoint_le_sqrt_pow_of_score_le
    G C D hq N omega eta hscore
  unfold bcProb
  calc
    bcWeight G C (BeffaraDC.selfDualPoint q) q omega /
        bcZ G C (BeffaraDC.selfDualPoint q) q <=
      ((Real.sqrt q) ^ N *
          bcWeight G D (BeffaraDC.selfDualPoint q) q eta) /
        bcZ G C (BeffaraDC.selfDualPoint q) q :=
      div_le_div_of_nonneg_right hweight hZC.le
    _ <= ((Real.sqrt q) ^ N *
          bcWeight G D (BeffaraDC.selfDualPoint q) q eta) /
        bcZ G D (BeffaraDC.selfDualPoint q) q := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (pow_nonneg (Real.sqrt_nonneg q) N)
          (bcWeight_nonneg G D hp hp1 hq0 eta)) hZD hZ
    _ = (Real.sqrt q) ^ N *
        (bcWeight G D (BeffaraDC.selfDualPoint q) q eta /
          bcZ G D (BeffaraDC.selfDualPoint q) q) := by ring

end

end StatMech.FK
