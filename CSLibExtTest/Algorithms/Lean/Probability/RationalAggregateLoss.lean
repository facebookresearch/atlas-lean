/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Probability.RationalAggregateLoss
public import CSLibExt.Algorithms.Lean.Probability.RationalLossConvolution

/-!
# Tests for the finite count-mixture law

Count zero, a deterministic count, and a nonconstant count/severity
enumeration (masses `1/2, 3/8, 1/8`, zero beyond), with no truncation.
-/

open Cslib.Algorithms.Lean.Probability.RationalLossConvolution

namespace Cslib.Algorithms.Lean.Probability.RationalAggregateLoss

private theorem t_finsupp_sum_bridge (f : ℕ →₀ ℚ) (g : ℕ → ℚ → ℚ) :
    f.sum g = ∑ a ∈ f.support, g a (f a) := rfl

private theorem t_smul_apply_eq (q : ℚ) (w : ℕ →₀ ℚ) (m : ℕ) :
    (q • w) m = q * w m := by
  rw [Finsupp.smul_apply, smul_eq_mul]

private theorem t_single_sum_id (c : ℕ) (v : ℚ) :
    (Finsupp.single c v).sum (fun _ q => q) = v :=
  Finsupp.sum_single_index rfl

private theorem t_sum_add_id (f g : ℕ →₀ ℚ) :
    (f + g).sum (fun _ q => q)
      = f.sum (fun _ q => q) + g.sum (fun _ q => q) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private theorem t_decode_apply (L : RationalLossLaw) (n : ℕ) :
    decode L n = ENNReal.ofReal ((L.weights n : ℚ) : ℝ) := by
  unfold decode
  rw [PMF.ofFinset_apply]

private theorem t_iterLaw_one (S : RationalLossLaw) :
    iterLaw S 1 = convLaw unitLaw S := by
  show iterLaw S (0 + 1) = convLaw unitLaw S
  rw [iterLaw_succ, iterLaw_zero]

private theorem t_iterLaw_two (S : RationalLossLaw) :
    iterLaw S 2 = convLaw (iterLaw S 1) S := by
  show iterLaw S (1 + 1) = convLaw (iterLaw S 1) S
  rw [iterLaw_succ]

private theorem t_convLaw_weights (L1 L2 : RationalLossLaw) :
    (convLaw L1 L2).weights = convWeights L1.weights L2.weights := rfl

private theorem t_single_apply_eq (a b n : ℕ) (v : ℚ) :
    Finsupp.single (a + b) v n = if n = a + b then v else 0 := by
  rw [Finsupp.single_apply]
  by_cases h : a + b = n
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

private theorem t_convWeights_apply_sum (w1 w2 : ℕ →₀ ℚ) (n : ℕ) :
    convWeights w1 w2 n
      = ∑ a ∈ w1.support, ∑ b ∈ w2.support,
        if n = a + b then w1 a * w2 b else 0 := by
  unfold convWeights
  simp only [Finsupp.sum_apply, t_finsupp_sum_bridge,
    t_single_apply_eq]

private theorem t_zero_atom_left (w : ℕ →₀ ℚ) (n : ℕ) :
    convWeights (Finsupp.single 0 1) w n = w n := by
  rw [t_convWeights_apply_sum,
    Finsupp.support_single 0 (show (1 : ℚ) ≠ 0 by norm_num),
    Finset.sum_singleton]
  simp only [Finsupp.single_eq_same, zero_add, one_mul]
  by_cases hn : n ∈ w.support
  · have h0 : ∀ b ∈ w.support, b ≠ n →
        (if n = b then w b else 0) = 0 := by
      intro b _ hbn
      exact ite_eq_right (fun h => hbn h.symm)
    have h1 : n ∉ w.support → (if n = n then w n else 0) = 0 :=
      fun h => absurd hn h
    rw [Finset.sum_eq_single n h0 h1]
    simp
  · have h0 : ∀ b ∈ w.support, (if n = b then w b else 0) = 0 := by
      intro b hb
      apply ite_eq_right
      intro h
      have hmem : n ∈ w.support := by rwa [h]
      exact hn hmem
    rw [Finset.sum_eq_zero h0, Finsupp.notMem_support_iff.mp hn]

noncomputable def wC : ℕ →₀ ℚ :=
  Finsupp.single 0 (1 / 4 : ℚ) + Finsupp.single 1 (1 / 4 : ℚ)
    + Finsupp.single 2 (1 / 2 : ℚ)

noncomputable def wS : ℕ →₀ ℚ :=
  Finsupp.single 0 (1 / 2 : ℚ) + Finsupp.single 1 (1 / 2 : ℚ)

private theorem c0_support :
    (Finsupp.single 0 (1 / 4 : ℚ)).support = {0} :=
  Finsupp.support_single 0 (by norm_num)

private theorem c1_support :
    (Finsupp.single 1 (1 / 4 : ℚ)).support = {1} :=
  Finsupp.support_single 1 (by norm_num)

private theorem c2_support :
    (Finsupp.single 2 (1 / 2 : ℚ)).support = {2} :=
  Finsupp.support_single 2 (by norm_num)

private theorem s0_support :
    (Finsupp.single 0 (1 / 2 : ℚ)).support = {0} :=
  Finsupp.support_single 0 (by norm_num)

private theorem s1_support :
    (Finsupp.single 1 (1 / 2 : ℚ)).support = {1} :=
  Finsupp.support_single 1 (by norm_num)

private theorem c01_support :
    (Finsupp.single 0 (1 / 4 : ℚ)
      + Finsupp.single 1 (1 / 4 : ℚ)).support = {0, 1} := by
  have d : Disjoint (Finsupp.single 0 (1 / 4 : ℚ)).support
      (Finsupp.single 1 (1 / 4 : ℚ)).support := by
    rw [c0_support, c1_support]
    decide
  rw [Finsupp.support_add_eq d, c0_support, c1_support]
  decide

private theorem wC_support : wC.support = {0, 1, 2} := by
  have d : Disjoint (Finsupp.single 0 (1 / 4 : ℚ)
        + Finsupp.single 1 (1 / 4 : ℚ)).support
      (Finsupp.single 2 (1 / 2 : ℚ)).support := by
    rw [c01_support, c2_support]
    decide
  unfold wC
  rw [Finsupp.support_add_eq d, c01_support, c2_support]
  decide

private theorem wS_support : wS.support = {0, 1} := by
  have d : Disjoint (Finsupp.single 0 (1 / 2 : ℚ)).support
      (Finsupp.single 1 (1 / 2 : ℚ)).support := by
    rw [s0_support, s1_support]
    decide
  unfold wS
  rw [Finsupp.support_add_eq d, s0_support, s1_support]
  decide

private theorem wC_0 : wC 0 = 1 / 4 := by simp [wC, Finsupp.add_apply]
private theorem wC_1 : wC 1 = 1 / 4 := by simp [wC, Finsupp.add_apply]
private theorem wC_2 : wC 2 = 1 / 2 := by simp [wC, Finsupp.add_apply]
private theorem wS_0 : wS 0 = 1 / 2 := by simp [wS, Finsupp.add_apply]
private theorem wS_1 : wS 1 = 1 / 2 := by simp [wS, Finsupp.add_apply]

noncomputable def Cnt : RationalLossLaw where
  weights := wC
  nonneg := by
    intro n
    simp only [wC, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  normalized := by
    unfold wC
    rw [t_sum_add_id, t_sum_add_id, t_single_sum_id, t_single_sum_id,
      t_single_sum_id]
    norm_num

noncomputable def Sev : RationalLossLaw where
  weights := wS
  nonneg := by
    intro n
    simp only [wS, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  normalized := by
    unfold wS
    rw [t_sum_add_id, t_single_sum_id, t_single_sum_id]
    norm_num

noncomputable def Ctwo : RationalLossLaw where
  weights := Finsupp.single 2 1
  nonneg := by
    intro n
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  normalized := by
    rw [t_single_sum_id]

private theorem t_Cnt_weights : Cnt.weights = wC := rfl
private theorem t_Sev_weights : Sev.weights = wS := rfl
private theorem t_ctwo_weights : Ctwo.weights = Finsupp.single 2 1 := rfl

private theorem t_unit_support : unitLaw.weights.support = {0} := by
  rw [unitLaw_weights]
  exact Finsupp.support_single 0 (by norm_num)

private theorem t_unit_mass_0 : unitLaw.weights 0 = 1 := by
  rw [unitLaw_weights]
  exact Finsupp.single_eq_same

theorem agg_unit_weights (S : RationalLossLaw) (m : ℕ) :
    (aggregateLaw unitLaw S).weights m = unitLaw.weights m := by
  simp only [aggregateLaw_weights_apply, t_finsupp_sum_bridge]
  rw [t_unit_support, Finset.sum_singleton,
    t_unit_mass_0, iterLaw_zero, one_mul]

theorem agg_unit_decode (S : RationalLossLaw) :
    decode (aggregateLaw unitLaw S) = PMF.pure 0 := by
  apply PMF.ext
  intro m
  rw [t_decode_apply, agg_unit_weights, ← t_decode_apply,
    decode_unitLaw]

theorem agg_unit_mass_zero (S : RationalLossLaw) :
    decode (aggregateLaw unitLaw S) 0 = 1 := by
  rw [agg_unit_decode, PMF.pure_apply]
  simp

private theorem t_ctwo_support : Ctwo.weights.support = {2} := by
  rw [t_ctwo_weights]
  exact Finsupp.support_single 2 (by norm_num)

private theorem t_ctwo_mass_2 : Ctwo.weights 2 = 1 := by
  rw [t_ctwo_weights]
  exact Finsupp.single_eq_same

theorem agg_ctwo_weights (S : RationalLossLaw) (m : ℕ) :
    (aggregateLaw Ctwo S).weights m = (iterLaw S 2).weights m := by
  simp only [aggregateLaw_weights_apply, t_finsupp_sum_bridge]
  rw [t_ctwo_support, Finset.sum_singleton,
    t_ctwo_mass_2, one_mul]

theorem agg_ctwo_decode_apply (S : RationalLossLaw) (m : ℕ) :
    decode (aggregateLaw Ctwo S) m = decode (iterLaw S 2) m := by
  rw [t_decode_apply, t_decode_apply, agg_ctwo_weights]

private theorem t_iter0_eq_zero (m : ℕ) (hm : m ≠ 0) :
    (iterLaw Sev 0).weights m = 0 := by
  rw [iterLaw_zero, unitLaw_weights]
  exact Finsupp.single_eq_of_ne hm

private theorem t_iter1_weights : (iterLaw Sev 1).weights = wS := by
  rw [t_iterLaw_one, t_convLaw_weights, unitLaw_weights,
    t_Sev_weights]
  exact Finsupp.ext (fun n => t_zero_atom_left wS n)

private theorem t_iter1_eq_zero (m : ℕ) (hm : m ∉ wS.support) :
    (iterLaw Sev 1).weights m = 0 := by
  rw [t_iter1_weights]
  exact Finsupp.notMem_support_iff.mp hm

private theorem t_iter2_weights_eq (m : ℕ) :
    (iterLaw Sev 2).weights m = convWeights wS wS m := by
  rw [t_iterLaw_two, t_convLaw_weights, t_iter1_weights,
    t_Sev_weights]

private theorem t_wS_enum (F : ℕ → ℕ → ℚ) :
    (∑ a ∈ wS.support, ∑ b ∈ wS.support, F a b)
      = (F 0 0 + F 0 1) + (F 1 0 + F 1 1) := by
  have hb : (0 : ℕ) ∉ ({1} : Finset ℕ) := by decide
  rw [wS_support, Finset.sum_insert hb, Finset.sum_insert hb,
    Finset.sum_singleton, Finset.sum_singleton, Finset.sum_insert hb,
    Finset.sum_singleton]

theorem iter0_mass_0 : (iterLaw Sev 0).weights 0 = 1 := by
  rw [iterLaw_zero, unitLaw_weights]
  exact Finsupp.single_eq_same

theorem iter0_mass_1 : (iterLaw Sev 0).weights 1 = 0 :=
  t_iter0_eq_zero 1 (by norm_num)

theorem iter0_mass_2 : (iterLaw Sev 0).weights 2 = 0 :=
  t_iter0_eq_zero 2 (by norm_num)

theorem iter1_mass_0 : (iterLaw Sev 1).weights 0 = 1 / 2 := by
  rw [t_iter1_weights, wS_0]

theorem iter1_mass_1 : (iterLaw Sev 1).weights 1 = 1 / 2 := by
  rw [t_iter1_weights, wS_1]

theorem iter1_mass_2 : (iterLaw Sev 1).weights 2 = 0 := by
  apply t_iter1_eq_zero
  rw [wS_support]
  decide

theorem iter2_mass_0 : (iterLaw Sev 2).weights 0 = 1 / 4 := by
  rw [t_iter2_weights_eq, t_convWeights_apply_sum, t_wS_enum, wS_0,
    wS_1]
  simp
  norm_num

theorem iter2_mass_1 : (iterLaw Sev 2).weights 1 = 1 / 2 := by
  rw [t_iter2_weights_eq, t_convWeights_apply_sum, t_wS_enum, wS_0,
    wS_1]
  simp
  norm_num

theorem iter2_mass_2 : (iterLaw Sev 2).weights 2 = 1 / 4 := by
  rw [t_iter2_weights_eq, t_convWeights_apply_sum, t_wS_enum, wS_0,
    wS_1]
  simp
  norm_num

private theorem t_agg_enum (F : ℕ → ℚ) :
    (∑ k ∈ wC.support, F k) = F 0 + (F 1 + F 2) := by
  have h01 : (0 : ℕ) ∉ ({1, 2} : Finset ℕ) := by decide
  have h12 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  rw [wC_support, Finset.sum_insert h01, Finset.sum_insert h12,
    Finset.sum_singleton]

theorem agg_mass_0 : (aggregateLaw Cnt Sev).weights 0 = 1 / 2 := by
  simp only [aggregateLaw_weights_apply, t_finsupp_sum_bridge]
  rw [t_Cnt_weights, t_agg_enum, wC_0, wC_1, wC_2,
    iter0_mass_0, iter1_mass_0, iter2_mass_0]
  norm_num

theorem agg_mass_1 : (aggregateLaw Cnt Sev).weights 1 = 3 / 8 := by
  simp only [aggregateLaw_weights_apply, t_finsupp_sum_bridge]
  rw [t_Cnt_weights, t_agg_enum, wC_0, wC_1, wC_2,
    iter0_mass_1, iter1_mass_1, iter2_mass_1]
  norm_num

theorem agg_mass_2 : (aggregateLaw Cnt Sev).weights 2 = 1 / 8 := by
  simp only [aggregateLaw_weights_apply, t_finsupp_sum_bridge]
  rw [t_Cnt_weights, t_agg_enum, wC_0, wC_1, wC_2,
    iter0_mass_2, iter1_mass_2, iter2_mass_2]
  norm_num

theorem agg_decode_mass_0 :
    decode (aggregateLaw Cnt Sev) 0 = ENNReal.ofReal (((1 / 2 : ℚ)) : ℝ) := by
  rw [t_decode_apply, agg_mass_0]

theorem agg_decode_mass_1 :
    decode (aggregateLaw Cnt Sev) 1 = ENNReal.ofReal (((3 / 8 : ℚ)) : ℝ) := by
  rw [t_decode_apply, agg_mass_1]

theorem agg_decode_mass_2 :
    decode (aggregateLaw Cnt Sev) 2 = ENNReal.ofReal (((1 / 8 : ℚ)) : ℝ) := by
  rw [t_decode_apply, agg_mass_2]

private theorem t_iter2_eq_zero (m : ℕ) (hm : 2 < m) :
    (iterLaw Sev 2).weights m = 0 := by
  rw [t_iter2_weights_eq, t_convWeights_apply_sum, wS_support]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  show (if m = a + b then wS a * wS b else 0) = 0
  have hne : ¬ m = a + b := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    omega
  rw [ite_eq_right hne]

private theorem t_agg_eq_zero_of_ge (m : ℕ) (hm : 3 ≤ m) :
    (aggregateLaw Cnt Sev).weights m = 0 := by
  simp only [aggregateLaw_weights_apply, t_finsupp_sum_bridge]
  rw [t_Cnt_weights, wC_support]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · have hm0 : m ≠ 0 := by omega
    rw [t_iter0_eq_zero m hm0, mul_zero]
  · have hmem : m ∉ wS.support := by
      rw [wS_support]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [t_iter1_eq_zero m hmem, mul_zero]
  · rw [t_iter2_eq_zero m (by omega : 2 < m), mul_zero]

theorem agg_decode_eq_zero (m : ℕ) (hm : 3 ≤ m) :
    decode (aggregateLaw Cnt Sev) m = 0 := by
  rw [t_decode_apply, t_agg_eq_zero_of_ge m hm]
  simp

theorem agg_support_bound (m : ℕ)
    (h : decode (aggregateLaw Cnt Sev) m ≠ 0) : m ≤ 2 := by
  by_contra hlt
  have h3 : 3 ≤ m := by omega
  rw [agg_decode_eq_zero m h3] at h
  simp at h

theorem agg_decode_tsum :
    ∑' m, decode (aggregateLaw Cnt Sev) m = 1 :=
  PMF.tsum_coe (decode (aggregateLaw Cnt Sev))

theorem agg_endpoint_instance (m : ℕ) :
    decode (aggregateLaw Cnt Sev) m
      = ((decode Cnt).bind (fun n =>
        (fun q : PMF ℕ => q.bind (fun a => (decode Sev).map (a + ·)))^[n]
          (PMF.pure 0))) m := by
  rw [decode_aggregateLaw_eq_bind]

theorem agg_endpoint_at_one :
    ((decode Cnt).bind (fun n =>
      (fun q : PMF ℕ => q.bind (fun a => (decode Sev).map (a + ·)))^[n]
        (PMF.pure 0))) 1 = ENNReal.ofReal (((3 / 8 : ℚ)) : ℝ) := by
  rw [← decode_aggregateLaw_eq_bind]
  exact agg_decode_mass_1

end Cslib.Algorithms.Lean.Probability.RationalAggregateLoss
