/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Probability.RationalLossConvolution
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Tests for rational loss convolution

Direct product enumeration (masses `1/8, 3/8, 3/8, 1/8`), consolidation of
repeated support entries, zero-weight entries not affecting support,
normalization, the support bound `2 + 1`, and the endpoint at mass `3/8`.
-/

namespace Cslib.Algorithms.Lean.Probability.RationalLossConvolution

private theorem test_finsupp_sum_bridge (f : ℕ →₀ ℚ) (g : ℕ → ℚ → ℚ) :
    f.sum g = ∑ a ∈ f.support, g a (f a) := rfl

private theorem test_single_apply_eq (a b n : ℕ) (v : ℚ) :
    Finsupp.single (a + b) v n = if n = a + b then v else 0 := by
  rw [Finsupp.single_apply]
  by_cases h : a + b = n
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

private theorem test_single_sum_id (c : ℕ) (v : ℚ) :
    (Finsupp.single c v).sum (fun _ q => q) = v :=
  Finsupp.sum_single_index rfl

noncomputable def w1 : ℕ →₀ ℚ :=
  Finsupp.single 0 (1 / 4 : ℚ) + Finsupp.single 1 (1 / 2 : ℚ)
    + Finsupp.single 2 (1 / 4 : ℚ)

noncomputable def w2 : ℕ →₀ ℚ :=
  Finsupp.single 0 (1 / 2 : ℚ) + Finsupp.single 1 (1 / 2 : ℚ)

noncomputable def w0 : ℕ →₀ ℚ := Finsupp.single 0 1

private theorem s0_support :
    (Finsupp.single 0 (1 / 4 : ℚ)).support = {0} :=
  Finsupp.support_single 0 (by norm_num)

private theorem s1_support :
    (Finsupp.single 1 (1 / 2 : ℚ)).support = {1} :=
  Finsupp.support_single 1 (by norm_num)

private theorem s2_support :
    (Finsupp.single 2 (1 / 4 : ℚ)).support = {2} :=
  Finsupp.support_single 2 (by norm_num)

private theorem t0_support :
    (Finsupp.single 0 (1 / 2 : ℚ)).support = {0} :=
  Finsupp.support_single 0 (by norm_num)

private theorem t1_support :
    (Finsupp.single 1 (1 / 2 : ℚ)).support = {1} :=
  Finsupp.support_single 1 (by norm_num)

private theorem e01_support :
    (Finsupp.single 0 (1 / 4 : ℚ)
      + Finsupp.single 1 (1 / 2 : ℚ)).support = {0, 1} := by
  have d : Disjoint (Finsupp.single 0 (1 / 4 : ℚ)).support
      (Finsupp.single 1 (1 / 2 : ℚ)).support := by
    rw [s0_support, s1_support]
    decide
  rw [Finsupp.support_add_eq d, s0_support, s1_support]
  decide

private theorem w1_support : w1.support = {0, 1, 2} := by
  have d : Disjoint (Finsupp.single 0 (1 / 4 : ℚ)
        + Finsupp.single 1 (1 / 2 : ℚ)).support
      (Finsupp.single 2 (1 / 4 : ℚ)).support := by
    rw [e01_support, s2_support]
    decide
  unfold w1
  rw [Finsupp.support_add_eq d, e01_support, s2_support]
  decide

private theorem w2_support : w2.support = {0, 1} := by
  have d : Disjoint (Finsupp.single 0 (1 / 2 : ℚ)).support
      (Finsupp.single 1 (1 / 2 : ℚ)).support := by
    rw [t0_support, t1_support]
    decide
  unfold w2
  rw [Finsupp.support_add_eq d, t0_support, t1_support]
  decide

private theorem w1_0 : w1 0 = 1 / 4 := by simp [w1, Finsupp.add_apply]
private theorem w1_1 : w1 1 = 1 / 2 := by simp [w1, Finsupp.add_apply]
private theorem w1_2 : w1 2 = 1 / 4 := by simp [w1, Finsupp.add_apply]
private theorem w2_0 : w2 0 = 1 / 2 := by simp [w2, Finsupp.add_apply]
private theorem w2_1 : w2 1 = 1 / 2 := by simp [w2, Finsupp.add_apply]

private theorem sum_add_id (f g : ℕ →₀ ℚ) :
    (f + g).sum (fun _ q => q)
      = f.sum (fun _ q => q) + g.sum (fun _ q => q) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

noncomputable def L1 : RationalLossLaw where
  weights := w1
  nonneg := by
    intro n
    simp only [w1, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  normalized := by
    unfold w1
    rw [sum_add_id, sum_add_id, test_single_sum_id, test_single_sum_id,
      test_single_sum_id]
    norm_num

noncomputable def L2 : RationalLossLaw where
  weights := w2
  nonneg := by
    intro n
    simp only [w2, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  normalized := by
    unfold w2
    rw [sum_add_id, test_single_sum_id, test_single_sum_id]
    norm_num

noncomputable def L0 : RationalLossLaw where
  weights := w0
  nonneg := by
    intro n
    simp only [w0, Finsupp.single_apply]
    split_ifs <;> norm_num
  normalized := by
    unfold w0
    rw [test_single_sum_id]

private theorem L1_weights : L1.weights = w1 := rfl
private theorem L2_weights : L2.weights = w2 := rfl

private theorem enum_double_sum (F : ℕ → ℕ → ℚ) :
    (∑ a ∈ w1.support, ∑ b ∈ w2.support, F a b)
      = (F 0 0 + F 0 1) + ((F 1 0 + F 1 1) + (F 2 0 + F 2 1)) := by
  have h01 : (0 : ℕ) ∉ ({1, 2} : Finset ℕ) := by decide
  have h12 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  have hb : (0 : ℕ) ∉ ({1} : Finset ℕ) := by decide
  rw [w1_support, w2_support, Finset.sum_insert h01,
    Finset.sum_insert h12, Finset.sum_singleton, Finset.sum_insert hb,
    Finset.sum_singleton, Finset.sum_insert hb, Finset.sum_singleton,
    Finset.sum_insert hb, Finset.sum_singleton]

theorem conv_mass_0 : convWeights w1 w2 0 = 1 / 8 := by
  rw [convWeights_apply, enum_double_sum, w1_0, w1_1, w1_2, w2_0,
    w2_1]
  simp
  norm_num

theorem conv_mass_1 : convWeights w1 w2 1 = 3 / 8 := by
  rw [convWeights_apply, enum_double_sum, w1_0, w1_1, w1_2, w2_0,
    w2_1]
  simp
  norm_num

theorem conv_mass_2 : convWeights w1 w2 2 = 3 / 8 := by
  rw [convWeights_apply, enum_double_sum, w1_0, w1_1, w1_2, w2_0,
    w2_1]
  simp
  norm_num

theorem conv_mass_3 : convWeights w1 w2 3 = 1 / 8 := by
  rw [convWeights_apply, enum_double_sum, w1_0, w1_1, w1_2, w2_0,
    w2_1]
  simp
  norm_num

theorem conv_mass_2_eq_addMonoidAlgebra_coeff :
    convWeights w1 w2 2
      = (AddMonoidAlgebra.ofCoeff w1 * AddMonoidAlgebra.ofCoeff w2).coeff 2 := by
  rw [convWeights_eq_addMonoidAlgebra_mul]

theorem decode_mass_0 :
    decode (convLaw L1 L2) 0 = ENNReal.ofReal (((1 / 8 : ℚ)) : ℝ) := by
  rw [decode_apply, convLaw_weights, L1_weights, L2_weights,
    conv_mass_0]

theorem decode_mass_1 :
    decode (convLaw L1 L2) 1 = ENNReal.ofReal (((3 / 8 : ℚ)) : ℝ) := by
  rw [decode_apply, convLaw_weights, L1_weights, L2_weights,
    conv_mass_1]

theorem decode_mass_2 :
    decode (convLaw L1 L2) 2 = ENNReal.ofReal (((3 / 8 : ℚ)) : ℝ) := by
  rw [decode_apply, convLaw_weights, L1_weights, L2_weights,
    conv_mass_2]

theorem decode_mass_3 :
    decode (convLaw L1 L2) 3 = ENNReal.ofReal (((1 / 8 : ℚ)) : ℝ) := by
  rw [decode_apply, convLaw_weights, L1_weights, L2_weights,
    conv_mass_3]

theorem zero_atom_left (w : ℕ →₀ ℚ) (n : ℕ) :
    convWeights (Finsupp.single 0 1) w n = w n := by
  rw [convWeights_apply,
    Finsupp.support_single 0 (show (1 : ℚ) ≠ 0 by norm_num),
    Finset.sum_singleton]
  simp only [Finsupp.single_eq_same, zero_add, one_mul]
  by_cases hn : n ∈ w.support
  · have h₀ : ∀ b ∈ w.support, b ≠ n →
        (if n = b then w b else 0) = 0 := by
      intro b _ hbn
      exact ite_eq_right (fun h => hbn h.symm)
    have h₁ : n ∉ w.support → (if n = n then w n else 0) = 0 :=
      fun h => absurd hn h
    rw [Finset.sum_eq_single n h₀ h₁]
    simp
  · have h₀ : ∀ b ∈ w.support, (if n = b then w b else 0) = 0 := by
      intro b hb
      apply ite_eq_right
      intro h
      have hmem : n ∈ w.support := by rwa [h]
      exact hn hmem
    rw [Finset.sum_eq_zero h₀, Finsupp.notMem_support_iff.mp hn]

theorem zero_atom_convLaw (w : ℕ →₀ ℚ) (hw0 : ∀ n, 0 ≤ w n)
    (hw1 : w.sum (fun _ q => q) = 1) (n : ℕ) :
    (convLaw L0 ⟨w, hw0, hw1⟩).weights n = w n := by
  rw [convLaw_weights]
  exact zero_atom_left w n

theorem repeated_support_mass :
    (Finsupp.single (1 : ℕ) (1 / 4 : ℚ)
        + Finsupp.single (1 : ℕ) (1 / 4 : ℚ)
        + Finsupp.single (0 : ℕ) (1 / 2 : ℚ)) 1 = 1 / 2 := by
  have h10 : (1 : ℕ) ≠ 0 := by decide
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne h10]
  norm_num

theorem zero_weight_add : w1 + Finsupp.single 99 0 = w1 := by
  rw [Finsupp.single_zero, add_zero]

theorem zero_weight_support :
    (w1 + Finsupp.single 99 0).support = w1.support := by
  rw [zero_weight_add]

theorem support_max_bound :
    2 ∈ w1.support ∧ ∀ m ∈ w1.support, m ≤ 2 := by
  rw [w1_support]
  constructor
  · decide
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega

theorem zero_weight_max_bound :
    2 ∈ (w1 + Finsupp.single 99 0).support
      ∧ ∀ m ∈ (w1 + Finsupp.single 99 0).support, m ≤ 2 := by
  rw [zero_weight_support]
  exact support_max_bound

theorem decode_tsum_eq_one (L : RationalLossLaw) :
    ∑' n, decode L n = 1 :=
  PMF.tsum_coe (decode L)

theorem decode_support_sum_eq_one :
    ∑ n ∈ (convLaw L1 L2).weights.support,
      decode (convLaw L1 L2) n = 1 := by
  simp only [decode_apply]
  exact decode_sum_eq_one _

example : (convWeights L1.weights L2.weights).sum (fun _ q => q)
    = 1 :=
  convWeights_normalized L1 L2

private theorem conv_eq_zero_of_gt (n : ℕ) (hn : 3 < n) :
    convWeights w1 w2 n = 0 := by
  rw [convWeights_apply, w1_support, w2_support]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  show (if n = a + b then w1 a * w2 b else 0) = 0
  have hne : ¬ n = a + b := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    omega
  rw [ite_eq_right hne]

theorem support_bound (n : ℕ)
    (h : decode (convLaw L1 L2) n ≠ 0) : n ≤ 3 := by
  by_contra hlt
  have h3 : 3 < n := not_le.mp hlt
  rw [decode_apply, convLaw_weights, L1_weights, L2_weights,
    conv_eq_zero_of_gt n h3] at h
  simp at h

theorem endpoint_instance :
    decode (convLaw L1 L2) 2
      = ((decode L1).bind (fun a => (decode L2).map (a + ·))) 2 := by
  rw [decode_convLaw_eq_bind_map]

theorem endpoint_bind_at_two :
    ((decode L1).bind (fun a => (decode L2).map (a + ·))) 2
      = ENNReal.ofReal (((3 / 8 : ℚ)) : ℝ) := by
  rw [← decode_convLaw_eq_bind_map]
  exact decode_mass_2

end Cslib.Algorithms.Lean.Probability.RationalLossConvolution
