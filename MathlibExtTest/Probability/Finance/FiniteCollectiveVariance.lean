/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.FiniteCollectiveVariance
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance

/-!
# Finite pins for ACT-04.L01 collective variance

Four independent finite pins for the collective-variance identity
`Var S = E N * Var X + Var N * (E X)^2`, each computed directly on a
finite uniform space without appealing to the production theorem,
plus one theorem-backed pin that applies the production theorem.

- `collective_variance_explicit_pin`: 12-atom product pin, value `11/3`.
- `collective_variance_deterministic_count`: count `N = 1`, value `1`.
- `collective_variance_zero_count`: count `N = 0`, value `0`.
- `collective_variance_constant_severity`: constant severities, value `1`.
- `collective_variance_theorem_backed_constant`: applies
  `variance_stopped_sum_finite` to constant severities, value `1/4`.
-/

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Finance.FiniteCollectiveVarianceTests

/-- Integral of a constant over a probability measure. -/
private theorem const_int_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ) : ∫ _ : Ω, c ∂μ = c := by
  simp

/-- Every real function on a finite probability space is integrable. -/
private theorem integrable_of_fintype_prob {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) :
    Integrable f μ := by
  have haesm : AEStronglyMeasurable f μ := (measurable_of_countable f).aestronglyMeasurable
  refine Integrable.of_bound haesm (∑ x, ‖f x‖) ?_
  apply Filter.Eventually.of_forall
  intro ω
  exact Finset.single_le_sum (fun x _ => norm_nonneg _) (Finset.mem_univ ω)

-- Test 1 data: count on `{0, 1, 2}`, two-point severities `{1, 3}`,
-- independent product law on 12 atoms.
private abbrev D1 : Type := Fin 3 × Fin 2 × Fin 2
private noncomputable def mu1 : Measure D1 :=
  ((Fintype.card D1 : ENNReal))⁻¹ • Measure.count
private def N1 : D1 → ℕ := fun ω => ω.1.val
private def X1 : ℕ → D1 → ℝ :=
  fun i ω => if i = 0 then (1 + 2 * (ω.2.1.val : ℝ))
    else if i = 1 then (1 + 2 * (ω.2.2.val : ℝ)) else 0
private def S1 : D1 → ℝ := fun ω => ∑ k ∈ Finset.range (N1 ω), X1 k ω

/-- Explicit 12-atom pin: both sides equal `11/3`. -/
theorem collective_variance_explicit_pin :
    ProbabilityTheory.variance S1 mu1 = 11 / 3 ∧
      (∫ ω, (N1 ω : ℝ) ∂mu1) * ProbabilityTheory.variance (X1 0) mu1 +
        ProbabilityTheory.variance (fun ω => (N1 ω : ℝ)) mu1 * (∫ ω, X1 0 ω ∂mu1) ^ 2
        = 11 / 3 := by
  have hcard12 : Fintype.card D1 = 12 := by decide
  have hcu : Measure.count (Set.univ : Set D1) = (Fintype.card D1 : ENNReal) := by
    simp
  have hprob : IsProbabilityMeasure mu1 := by
    refine ⟨?_⟩
    show (((Fintype.card D1 : ENNReal))⁻¹ • Measure.count) Set.univ = 1
    rw [Measure.smul_apply, hcu, hcard12, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hint_eq : ∀ f : D1 → ℝ, ∫ ω, f ω ∂mu1 = (1 / 12 : ℝ) * ∑ x, f x := by
    intro f
    have hInt : Integrable f mu1 := integrable_of_fintype_prob mu1 f
    have h1 : ∫ ω, f ω ∂mu1 = ∑ x, mu1.real {x} • f x := integral_fintype hInt
    have hsing : ∀ x : D1, mu1 {x} = ((Fintype.card D1 : ENNReal))⁻¹ := by
      intro x
      show (((Fintype.card D1 : ENNReal))⁻¹ • Measure.count) {x} = _
      rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
    have hw : ∀ x : D1, mu1.real {x} = (1 / 12 : ℝ) := by
      intro x
      rw [measureReal_def, hsing, hcard12, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num
    rw [h1]
    simp only [hw, smul_eq_mul, ← Finset.mul_sum]
  have hsum_eval : ∀ g : D1 → ℝ, ∑ x, g x
      = g (0, 0, 0) + g (0, 0, 1) + g (0, 1, 0) + g (0, 1, 1)
        + g (1, 0, 0) + g (1, 0, 1) + g (1, 1, 0) + g (1, 1, 1)
        + g (2, 0, 0) + g (2, 0, 1) + g (2, 1, 0) + g (2, 1, 1) := by
    intro g
    simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two]
    ring
  have proj1 : ∀ a b c, ((a, b, c) : D1).1 = a := fun a b c => rfl
  have proj21 : ∀ a b c, ((a, b, c) : D1).2.1 = b := fun a b c => rfl
  have proj22 : ∀ a b c, ((a, b, c) : D1).2.2 = c := fun a b c => rfl
  have v30 : (0 : Fin 3).val = 0 := rfl
  have v31 : (1 : Fin 3).val = 1 := rfl
  have v32 : (2 : Fin 3).val = 2 := rfl
  have v20 : (0 : Fin 2).val = 0 := rfl
  have v21 : (1 : Fin 2).val = 1 := rfl
  have hEN : ∫ ω, (N1 ω : ℝ) ∂mu1 = 1 := by
    rw [hint_eq, hsum_eval]
    unfold N1
    norm_num [proj1, v30, v31, v32]
  have hEN2 : ∫ ω, ((N1 ω : ℝ)) ^ 2 ∂mu1 = 5 / 3 := by
    rw [hint_eq, hsum_eval]
    unfold N1
    norm_num [proj1, v30, v31, v32]
  have hEX0 : ∫ ω, X1 0 ω ∂mu1 = 2 := by
    rw [hint_eq, hsum_eval]
    unfold X1
    norm_num [proj21, v20, v21]
  have hEX02 : ∫ ω, (X1 0 ω) ^ 2 ∂mu1 = 5 := by
    rw [hint_eq, hsum_eval]
    unfold X1
    norm_num [proj21, v20, v21]
  have hES : ∫ ω, S1 ω ∂mu1 = 2 := by
    rw [hint_eq, hsum_eval]
    unfold S1 N1 X1
    norm_num [proj1, proj21, proj22, v30, v31, v32, v20, v21,
      Finset.sum_range_succ, Finset.sum_range_zero]
  have hES2 : ∫ ω, (S1 ω) ^ 2 ∂mu1 = 23 / 3 := by
    rw [hint_eq, hsum_eval]
    unfold S1 N1 X1
    norm_num [proj1, proj21, proj22, v30, v31, v32, v20, v21,
      Finset.sum_range_succ, Finset.sum_range_zero]
  have hmemN : MemLp (fun ω : D1 => (N1 ω : ℝ)) 2 mu1 := by
    have haesm : AEStronglyMeasurable (fun ω : D1 => (N1 ω : ℝ)) mu1 :=
      (measurable_of_countable (f := (fun ω : D1 => (N1 ω : ℝ)))).aestronglyMeasurable
    refine MemLp.of_bound haesm 2 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖(((N1 ω : ℕ)) : ℝ)‖ ≤ 2
    have hlt : ω.1.val < 3 := ω.1.2
    have hle : ω.1.val ≤ 2 := by omega
    have hNr : (((N1 ω : ℕ)) : ℝ) = (((ω.1.val : ℕ)) : ℝ) := rfl
    calc ‖(((N1 ω : ℕ)) : ℝ)‖ = (((N1 ω : ℕ)) : ℝ) := Real.norm_of_nonneg (Nat.cast_nonneg _)
      _ = (((ω.1.val : ℕ)) : ℝ) := hNr
      _ ≤ (2 : ℝ) := by exact_mod_cast hle
  have hmemX0 : MemLp (X1 0) 2 mu1 := by
    have haesm : AEStronglyMeasurable (X1 0) mu1 :=
      (measurable_of_countable (f := X1 0)).aestronglyMeasurable
    refine MemLp.of_bound haesm 3 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖X1 0 ω‖ ≤ 3
    have hlt : ω.2.1.val < 2 := ω.2.1.2
    have hle : ω.2.1.val ≤ 1 := by omega
    have hX : X1 0 ω = 1 + 2 * (((ω.2.1.val : ℕ)) : ℝ) := by simp [X1]
    have hnn : 0 ≤ X1 0 ω := by
      rw [hX]
      have hb : (0 : ℝ) ≤ (((ω.2.1.val : ℕ)) : ℝ) := Nat.cast_nonneg _
      linarith
    have hle3 : X1 0 ω ≤ 3 := by
      rw [hX]
      have hbr : (((ω.2.1.val : ℕ)) : ℝ) ≤ 1 := by exact_mod_cast hle
      linarith
    calc ‖X1 0 ω‖ = X1 0 ω := Real.norm_of_nonneg hnn
      _ ≤ 3 := hle3
  have hmemS : MemLp S1 2 mu1 := by
    have haesm : AEStronglyMeasurable S1 mu1 :=
      (measurable_of_countable (f := S1)).aestronglyMeasurable
    refine MemLp.of_bound haesm 6 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖S1 ω‖ ≤ 6
    have hNle : N1 ω ≤ 2 := by
      have hlt : ω.1.val < 3 := ω.1.2
      show ω.1.val ≤ 2
      omega
    have hXle : ∀ k : ℕ, X1 k ω ≤ 3 := by
      intro k
      unfold X1
      split_ifs with h0 h1
      · have hlt : ω.2.1.val < 2 := ω.2.1.2
        have hle : ω.2.1.val ≤ 1 := by omega
        have hbr : (((ω.2.1.val : ℕ)) : ℝ) ≤ 1 := by exact_mod_cast hle
        linarith
      · have hlt : ω.2.2.val < 2 := ω.2.2.2
        have hle : ω.2.2.val ≤ 1 := by omega
        have hbr : (((ω.2.2.val : ℕ)) : ℝ) ≤ 1 := by exact_mod_cast hle
        linarith
      · norm_num
    have hXnn : ∀ k : ℕ, 0 ≤ X1 k ω := by
      intro k
      unfold X1
      split_ifs
      · have hb : (0 : ℝ) ≤ (((ω.2.1.val : ℕ)) : ℝ) := Nat.cast_nonneg _
        linarith
      · have hb : (0 : ℝ) ≤ (((ω.2.2.val : ℕ)) : ℝ) := Nat.cast_nonneg _
        linarith
      · norm_num
    have hSnn : 0 ≤ S1 ω := by
      unfold S1
      apply Finset.sum_nonneg
      intro k _
      exact hXnn k
    have hSle : S1 ω ≤ 6 := by
      calc S1 ω = ∑ k ∈ Finset.range (N1 ω), X1 k ω := rfl
        _ ≤ ∑ k ∈ Finset.range (N1 ω), (3 : ℝ) := Finset.sum_le_sum (fun k _ => hXle k)
        _ = (N1 ω : ℝ) * 3 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ 2 * 3 := by
            apply mul_le_mul_of_nonneg_right _ (by norm_num)
            exact_mod_cast hNle
        _ = 6 := by norm_num
    calc ‖S1 ω‖ = S1 ω := Real.norm_of_nonneg hSnn
      _ ≤ 6 := hSle
  have hVN : ProbabilityTheory.variance (fun ω => (N1 ω : ℝ)) mu1 = 2 / 3 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemN
    simp only [hsub, Pi.pow_apply, hEN2, hEN]
    norm_num
  have hVX : ProbabilityTheory.variance (X1 0) mu1 = 1 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemX0
    simp only [hsub, Pi.pow_apply, hEX02, hEX0]
    norm_num
  have hVS : ProbabilityTheory.variance S1 mu1 = 11 / 3 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemS
    simp only [hsub, Pi.pow_apply, hES2, hES]
    norm_num
  have hR : (∫ ω, (N1 ω : ℝ) ∂mu1) * ProbabilityTheory.variance (X1 0) mu1 +
      ProbabilityTheory.variance (fun ω => (N1 ω : ℝ)) mu1 * (∫ ω, X1 0 ω ∂mu1) ^ 2
      = 11 / 3 := by
    rw [hEN, hVX, hVN, hEX0]
    norm_num
  exact ⟨hVS, hR⟩

-- Test 2 data: deterministic count `N = 1`, two-point severities `{1, 3}`.
private abbrev D2 : Type := Fin 2
private noncomputable def mu2 : Measure D2 :=
  ((Fintype.card D2 : ENNReal))⁻¹ • Measure.count
private def N2 : D2 → ℕ := fun _ => 1
private def X2 : ℕ → D2 → ℝ :=
  fun i ω => if i = 0 then (1 + 2 * (ω.val : ℝ)) else 0
private def S2 : D2 → ℝ := fun ω => ∑ k ∈ Finset.range (N2 ω), X2 k ω

/-- Deterministic count pin: both sides equal `1`, `Var N = 0`. -/
theorem collective_variance_deterministic_count :
    ProbabilityTheory.variance S2 mu2 = 1 ∧
      (∫ ω, (N2 ω : ℝ) ∂mu2) * ProbabilityTheory.variance (X2 0) mu2 +
        ProbabilityTheory.variance (fun ω => (N2 ω : ℝ)) mu2 * (∫ ω, X2 0 ω ∂mu2) ^ 2
        = 1 ∧
      ProbabilityTheory.variance (fun ω => (N2 ω : ℝ)) mu2 = 0 ∧
      ∫ ω, (N2 ω : ℝ) ∂mu2 = 1 := by
  have hcard2 : Fintype.card D2 = 2 := by decide
  have hcu : Measure.count (Set.univ : Set D2) = (Fintype.card D2 : ENNReal) := by
    simp
  have hprob : IsProbabilityMeasure mu2 := by
    refine ⟨?_⟩
    show (((Fintype.card D2 : ENNReal))⁻¹ • Measure.count) Set.univ = 1
    rw [Measure.smul_apply, hcu, hcard2, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hint_eq : ∀ f : D2 → ℝ, ∫ ω, f ω ∂mu2 = (1 / 2 : ℝ) * ∑ x, f x := by
    intro f
    have hInt : Integrable f mu2 := integrable_of_fintype_prob mu2 f
    have h1 : ∫ ω, f ω ∂mu2 = ∑ x, mu2.real {x} • f x := integral_fintype hInt
    have hsing : ∀ x : D2, mu2 {x} = ((Fintype.card D2 : ENNReal))⁻¹ := by
      intro x
      show (((Fintype.card D2 : ENNReal))⁻¹ • Measure.count) {x} = _
      rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
    have hw : ∀ x : D2, mu2.real {x} = (1 / 2 : ℝ) := by
      intro x
      rw [measureReal_def, hsing, hcard2, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num
    rw [h1]
    simp only [hw, smul_eq_mul, ← Finset.mul_sum]
  have hsum_eval : ∀ g : D2 → ℝ, ∑ x, g x = g 0 + g 1 := by
    intro g
    simp only [Fin.sum_univ_two]
  have v20 : (0 : Fin 2).val = 0 := rfl
  have v21 : (1 : Fin 2).val = 1 := rfl
  have hEN : ∫ ω, (N2 ω : ℝ) ∂mu2 = 1 := by
    have hc : (fun ω : D2 => (N2 ω : ℝ)) =ᵐ[mu2] (fun _ => (1 : ℝ)) := by
      apply Filter.Eventually.of_forall
      intro ω
      simp [N2]
    calc ∫ ω, (N2 ω : ℝ) ∂mu2 = ∫ _ : D2, (1 : ℝ) ∂mu2 := integral_congr_ae hc
      _ = 1 := const_int_eq mu2 1
  have hEN2 : ∫ ω, ((N2 ω : ℝ)) ^ 2 ∂mu2 = 1 := by
    have hc : (fun ω : D2 => ((N2 ω : ℝ)) ^ 2) =ᵐ[mu2] (fun _ => (1 : ℝ)) := by
      apply Filter.Eventually.of_forall
      intro ω
      simp [N2]
    calc ∫ ω, ((N2 ω : ℝ)) ^ 2 ∂mu2 = ∫ _ : D2, (1 : ℝ) ∂mu2 := integral_congr_ae hc
      _ = 1 := const_int_eq mu2 1
  have hEX0 : ∫ ω, X2 0 ω ∂mu2 = 2 := by
    rw [hint_eq, hsum_eval]
    unfold X2
    norm_num [v20, v21]
  have hEX02 : ∫ ω, (X2 0 ω) ^ 2 ∂mu2 = 5 := by
    rw [hint_eq, hsum_eval]
    unfold X2
    norm_num [v20, v21]
  have hSeq : ∀ ω : D2, S2 ω = X2 0 ω := by
    intro ω
    unfold S2 N2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hES : ∫ ω, S2 ω ∂mu2 = 2 := by
    have hc : S2 =ᵐ[mu2] X2 0 := Filter.Eventually.of_forall hSeq
    calc ∫ ω, S2 ω ∂mu2 = ∫ ω, X2 0 ω ∂mu2 := integral_congr_ae hc
      _ = 2 := hEX0
  have hES2 : ∫ ω, (S2 ω) ^ 2 ∂mu2 = 5 := by
    have hc : (fun ω => (S2 ω) ^ 2) =ᵐ[mu2] (fun ω => (X2 0 ω) ^ 2) :=
      Filter.Eventually.of_forall (fun ω => congrArg (fun x : ℝ => x ^ 2) (hSeq ω))
    calc ∫ ω, (S2 ω) ^ 2 ∂mu2 = ∫ ω, (X2 0 ω) ^ 2 ∂mu2 := integral_congr_ae hc
      _ = 5 := hEX02
  have hmemN : MemLp (fun ω : D2 => (N2 ω : ℝ)) 2 mu2 := by
    have haesm : AEStronglyMeasurable (fun ω : D2 => (N2 ω : ℝ)) mu2 :=
      (measurable_of_countable (f := (fun ω : D2 => (N2 ω : ℝ)))).aestronglyMeasurable
    refine MemLp.of_bound haesm 1 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖(((N2 ω : ℕ)) : ℝ)‖ ≤ 1
    have hN1 : N2 ω = 1 := rfl
    calc ‖(((N2 ω : ℕ)) : ℝ)‖ = (((N2 ω : ℕ)) : ℝ) := Real.norm_of_nonneg (Nat.cast_nonneg _)
      _ ≤ (1 : ℝ) := by simp [hN1, Nat.cast_one]
  have hmemX0 : MemLp (X2 0) 2 mu2 := by
    have haesm : AEStronglyMeasurable (X2 0) mu2 :=
      (measurable_of_countable (f := X2 0)).aestronglyMeasurable
    refine MemLp.of_bound haesm 3 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖X2 0 ω‖ ≤ 3
    have hlt : ω.val < 2 := ω.2
    have hle : ω.val ≤ 1 := by omega
    have hX : X2 0 ω = 1 + 2 * ((ω.val : ℕ) : ℝ) := by simp [X2]
    have hnn : 0 ≤ X2 0 ω := by
      rw [hX]
      have hb : (0 : ℝ) ≤ ((ω.val : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hle3 : X2 0 ω ≤ 3 := by
      rw [hX]
      have hbr : ((ω.val : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hle
      linarith
    calc ‖X2 0 ω‖ = X2 0 ω := Real.norm_of_nonneg hnn
      _ ≤ 3 := hle3
  have hmemS : MemLp S2 2 mu2 := by
    have haesm : AEStronglyMeasurable S2 mu2 :=
      (measurable_of_countable (f := S2)).aestronglyMeasurable
    refine MemLp.of_bound haesm 3 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖S2 ω‖ ≤ 3
    have hX : X2 0 ω = 1 + 2 * ((ω.val : ℕ) : ℝ) := by simp [X2]
    have hlt : ω.val < 2 := ω.2
    have hle : ω.val ≤ 1 := by omega
    have hS3 : S2 ω ≤ 3 := by
      rw [hSeq ω, hX]
      have hbr : ((ω.val : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hle
      linarith
    have hSnn : 0 ≤ S2 ω := by
      rw [hSeq ω, hX]
      have hb : (0 : ℝ) ≤ ((ω.val : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc ‖S2 ω‖ = S2 ω := Real.norm_of_nonneg hSnn
      _ ≤ 3 := hS3
  have hVN : ProbabilityTheory.variance (fun ω => (N2 ω : ℝ)) mu2 = 0 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemN
    simp only [hsub, Pi.pow_apply, hEN2, hEN]
    norm_num
  have hVX : ProbabilityTheory.variance (X2 0) mu2 = 1 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemX0
    simp only [hsub, Pi.pow_apply, hEX02, hEX0]
    norm_num
  have hVS : ProbabilityTheory.variance S2 mu2 = 1 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemS
    simp only [hsub, Pi.pow_apply, hES2, hES]
    norm_num
  have hR : (∫ ω, (N2 ω : ℝ) ∂mu2) * ProbabilityTheory.variance (X2 0) mu2 +
      ProbabilityTheory.variance (fun ω => (N2 ω : ℝ)) mu2 * (∫ ω, X2 0 ω ∂mu2) ^ 2
      = 1 := by
    rw [hEN, hVX, hVN, hEX0]
    norm_num
  exact ⟨hVS, hR, hVN, hEN⟩

-- Test 3 data: zero count `N = 0` (so `S = 0` regardless of severities).
private abbrev D3 : Type := Fin 1
private noncomputable def mu3 : Measure D3 :=
  ((Fintype.card D3 : ENNReal))⁻¹ • Measure.count
private def N3 : D3 → ℕ := fun _ => 0
private def X3 : ℕ → D3 → ℝ := fun _ _ => 5
private def S3 : D3 → ℝ := fun ω => ∑ k ∈ Finset.range (N3 ω), X3 k ω

/-- Zero-count pin: both sides equal `0`. -/
theorem collective_variance_zero_count :
    ProbabilityTheory.variance S3 mu3 = 0 ∧
      (∫ ω, (N3 ω : ℝ) ∂mu3) * ProbabilityTheory.variance (X3 0) mu3 +
        ProbabilityTheory.variance (fun ω => (N3 ω : ℝ)) mu3 * (∫ ω, X3 0 ω ∂mu3) ^ 2
        = 0 := by
  have hcard1 : Fintype.card D3 = 1 := by decide
  have hcu : Measure.count (Set.univ : Set D3) = (Fintype.card D3 : ENNReal) := by
    simp
  have hprob : IsProbabilityMeasure mu3 := by
    refine ⟨?_⟩
    show (((Fintype.card D3 : ENNReal))⁻¹ • Measure.count) Set.univ = 1
    rw [Measure.smul_apply, hcu, hcard1, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hS0pt : ∀ ω : D3, S3 ω = 0 := by
    intro ω
    simp [S3, N3, Finset.range_zero, Finset.sum_empty]
  have hN0pt : ∀ ω : D3, ((N3 ω : ℕ) : ℝ) = 0 := fun ω => by simp [N3]
  have hN02pt : ∀ ω : D3, (((N3 ω : ℕ)) : ℝ) ^ 2 = 0 := fun ω => by rw [hN0pt ω]; norm_num
  have hX0pt : ∀ ω : D3, X3 0 ω = 5 := fun ω => rfl
  have hX02pt : ∀ ω : D3, (X3 0 ω) ^ 2 = 25 := fun ω => by rw [hX0pt ω]; norm_num
  have hS02pt : ∀ ω : D3, (S3 ω) ^ 2 = 0 := fun ω => by rw [hS0pt ω]; norm_num
  have hEN : ∫ ω, (N3 ω : ℝ) ∂mu3 = 0 := by
    have hc : (fun ω : D3 => (N3 ω : ℝ)) =ᵐ[mu3] (fun _ => (0 : ℝ)) :=
      Filter.Eventually.of_forall hN0pt
    calc ∫ ω, (N3 ω : ℝ) ∂mu3 = ∫ _ : D3, (0 : ℝ) ∂mu3 := integral_congr_ae hc
      _ = 0 := const_int_eq mu3 0
  have hEN2 : ∫ ω, ((N3 ω : ℝ)) ^ 2 ∂mu3 = 0 := by
    have hc : (fun ω : D3 => ((N3 ω : ℝ)) ^ 2) =ᵐ[mu3] (fun _ => (0 : ℝ)) :=
      Filter.Eventually.of_forall hN02pt
    calc ∫ ω, ((N3 ω : ℝ)) ^ 2 ∂mu3 = ∫ _ : D3, (0 : ℝ) ∂mu3 := integral_congr_ae hc
      _ = 0 := const_int_eq mu3 0
  have hEX0 : ∫ ω, X3 0 ω ∂mu3 = 5 := by
    have hc : (X3 0) =ᵐ[mu3] (fun _ => (5 : ℝ)) :=
      Filter.Eventually.of_forall hX0pt
    calc ∫ ω, X3 0 ω ∂mu3 = ∫ _ : D3, (5 : ℝ) ∂mu3 := integral_congr_ae hc
      _ = 5 := const_int_eq mu3 5
  have hEX02 : ∫ ω, (X3 0 ω) ^ 2 ∂mu3 = 25 := by
    have hc : (fun ω => (X3 0 ω) ^ 2) =ᵐ[mu3] (fun _ => (25 : ℝ)) :=
      Filter.Eventually.of_forall hX02pt
    calc ∫ ω, (X3 0 ω) ^ 2 ∂mu3 = ∫ _ : D3, (25 : ℝ) ∂mu3 := integral_congr_ae hc
      _ = 25 := const_int_eq mu3 25
  have hES : ∫ ω, S3 ω ∂mu3 = 0 := by
    have hc : S3 =ᵐ[mu3] (fun _ => (0 : ℝ)) :=
      Filter.Eventually.of_forall hS0pt
    calc ∫ ω, S3 ω ∂mu3 = ∫ _ : D3, (0 : ℝ) ∂mu3 := integral_congr_ae hc
      _ = 0 := const_int_eq mu3 0
  have hES2 : ∫ ω, (S3 ω) ^ 2 ∂mu3 = 0 := by
    have hc : (fun ω => (S3 ω) ^ 2) =ᵐ[mu3] (fun _ => (0 : ℝ)) :=
      Filter.Eventually.of_forall hS02pt
    calc ∫ ω, (S3 ω) ^ 2 ∂mu3 = ∫ _ : D3, (0 : ℝ) ∂mu3 := integral_congr_ae hc
      _ = 0 := const_int_eq mu3 0
  have hmemN : MemLp (fun ω : D3 => (N3 ω : ℝ)) 2 mu3 := by
    have haesm : AEStronglyMeasurable (fun ω : D3 => (N3 ω : ℝ)) mu3 :=
      (measurable_of_countable (f := (fun ω : D3 => (N3 ω : ℝ)))).aestronglyMeasurable
    refine MemLp.of_bound haesm 1 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖(((N3 ω : ℕ)) : ℝ)‖ ≤ 1
    rw [hN0pt ω]
    norm_num [Real.norm_eq_abs]
  have hmemX0 : MemLp (X3 0) 2 mu3 := by
    have haesm : AEStronglyMeasurable (X3 0) mu3 :=
      (measurable_of_countable (f := X3 0)).aestronglyMeasurable
    refine MemLp.of_bound haesm 5 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖X3 0 ω‖ ≤ 5
    rw [hX0pt ω]
    norm_num [Real.norm_eq_abs]
  have hmemS : MemLp S3 2 mu3 := by
    have haesm : AEStronglyMeasurable S3 mu3 :=
      (measurable_of_countable (f := S3)).aestronglyMeasurable
    refine MemLp.of_bound haesm 1 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖S3 ω‖ ≤ 1
    rw [hS0pt ω]
    norm_num [Real.norm_eq_abs]
  have hVN : ProbabilityTheory.variance (fun ω => (N3 ω : ℝ)) mu3 = 0 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemN
    simp only [hsub, Pi.pow_apply, hEN2, hEN]
    norm_num
  have hVX : ProbabilityTheory.variance (X3 0) mu3 = 0 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemX0
    simp only [hsub, Pi.pow_apply, hEX02, hEX0]
    norm_num
  have hVS : ProbabilityTheory.variance S3 mu3 = 0 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemS
    simp only [hsub, Pi.pow_apply, hES2, hES]
    norm_num
  have hR : (∫ ω, (N3 ω : ℝ) ∂mu3) * ProbabilityTheory.variance (X3 0) mu3 +
      ProbabilityTheory.variance (fun ω => (N3 ω : ℝ)) mu3 * (∫ ω, X3 0 ω ∂mu3) ^ 2
      = 0 := by
    rw [hEN, hVX, hVN, hEX0]
    norm_num
  exact ⟨hVS, hR⟩

-- Test 4 data: count on `{0, 1}`, constant severities `2`.
private abbrev D4 : Type := Fin 2
private noncomputable def mu4 : Measure D4 :=
  ((Fintype.card D4 : ENNReal))⁻¹ • Measure.count
private def N4 : D4 → ℕ := fun ω => ω.val
private def X4 : ℕ → D4 → ℝ := fun _ _ => 2
private def S4 : D4 → ℝ := fun ω => ∑ k ∈ Finset.range (N4 ω), X4 k ω

/-- Constant-severity pin: both sides equal `1`, `Var X = 0`. -/
theorem collective_variance_constant_severity :
    ProbabilityTheory.variance S4 mu4 = 1 ∧
      (∫ ω, (N4 ω : ℝ) ∂mu4) * ProbabilityTheory.variance (X4 0) mu4 +
        ProbabilityTheory.variance (fun ω => (N4 ω : ℝ)) mu4 * (∫ ω, X4 0 ω ∂mu4) ^ 2
        = 1 ∧
      ProbabilityTheory.variance (X4 0) mu4 = 0 := by
  have hcard2 : Fintype.card D4 = 2 := by decide
  have hcu : Measure.count (Set.univ : Set D4) = (Fintype.card D4 : ENNReal) := by
    simp
  have hprob : IsProbabilityMeasure mu4 := by
    refine ⟨?_⟩
    show (((Fintype.card D4 : ENNReal))⁻¹ • Measure.count) Set.univ = 1
    rw [Measure.smul_apply, hcu, hcard2, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hint_eq : ∀ f : D4 → ℝ, ∫ ω, f ω ∂mu4 = (1 / 2 : ℝ) * ∑ x, f x := by
    intro f
    have hInt : Integrable f mu4 := integrable_of_fintype_prob mu4 f
    have h1 : ∫ ω, f ω ∂mu4 = ∑ x, mu4.real {x} • f x := integral_fintype hInt
    have hsing : ∀ x : D4, mu4 {x} = ((Fintype.card D4 : ENNReal))⁻¹ := by
      intro x
      show (((Fintype.card D4 : ENNReal))⁻¹ • Measure.count) {x} = _
      rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
    have hw : ∀ x : D4, mu4.real {x} = (1 / 2 : ℝ) := by
      intro x
      rw [measureReal_def, hsing, hcard2, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num
    rw [h1]
    simp only [hw, smul_eq_mul, ← Finset.mul_sum]
  have hsum_eval : ∀ g : D4 → ℝ, ∑ x, g x = g 0 + g 1 := by
    intro g
    simp only [Fin.sum_univ_two]
  have v20 : (0 : Fin 2).val = 0 := rfl
  have v21 : (1 : Fin 2).val = 1 := rfl
  have hEN : ∫ ω, (N4 ω : ℝ) ∂mu4 = 1 / 2 := by
    rw [hint_eq, hsum_eval]
    unfold N4
    norm_num [v20, v21]
  have hEN2 : ∫ ω, ((N4 ω : ℝ)) ^ 2 ∂mu4 = 1 / 2 := by
    rw [hint_eq, hsum_eval]
    unfold N4
    norm_num [v20, v21]
  have hX0pt : ∀ ω : D4, X4 0 ω = 2 := fun ω => rfl
  have hX02pt : ∀ ω : D4, (X4 0 ω) ^ 2 = 4 := fun ω => by rw [hX0pt ω]; norm_num
  have hEX0 : ∫ ω, X4 0 ω ∂mu4 = 2 := by
    have hc : (X4 0) =ᵐ[mu4] (fun _ => (2 : ℝ)) :=
      Filter.Eventually.of_forall hX0pt
    calc ∫ ω, X4 0 ω ∂mu4 = ∫ _ : D4, (2 : ℝ) ∂mu4 := integral_congr_ae hc
      _ = 2 := const_int_eq mu4 2
  have hEX02 : ∫ ω, (X4 0 ω) ^ 2 ∂mu4 = 4 := by
    have hc : (fun ω => (X4 0 ω) ^ 2) =ᵐ[mu4] (fun _ => (4 : ℝ)) :=
      Filter.Eventually.of_forall hX02pt
    calc ∫ ω, (X4 0 ω) ^ 2 ∂mu4 = ∫ _ : D4, (4 : ℝ) ∂mu4 := integral_congr_ae hc
      _ = 4 := const_int_eq mu4 4
  have hSeq : ∀ ω : D4, S4 ω = (N4 ω : ℝ) * 2 := by
    intro ω
    simp [S4, X4, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hES : ∫ ω, S4 ω ∂mu4 = 1 := by
    rw [hint_eq, hsum_eval]
    unfold S4 N4 X4
    norm_num [v20, v21, Finset.sum_range_succ, Finset.sum_range_zero]
  have hES2 : ∫ ω, (S4 ω) ^ 2 ∂mu4 = 2 := by
    rw [hint_eq, hsum_eval]
    unfold S4 N4 X4
    norm_num [v20, v21, Finset.sum_range_succ, Finset.sum_range_zero]
  have hmemN : MemLp (fun ω : D4 => (N4 ω : ℝ)) 2 mu4 := by
    have haesm : AEStronglyMeasurable (fun ω : D4 => (N4 ω : ℝ)) mu4 :=
      (measurable_of_countable (f := (fun ω : D4 => (N4 ω : ℝ)))).aestronglyMeasurable
    refine MemLp.of_bound haesm 1 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖(((N4 ω : ℕ)) : ℝ)‖ ≤ 1
    have hlt : ω.val < 2 := ω.2
    have hle : ω.val ≤ 1 := by omega
    have hNr : (((N4 ω : ℕ)) : ℝ) = (((ω.val : ℕ)) : ℝ) := rfl
    calc ‖(((N4 ω : ℕ)) : ℝ)‖ = (((N4 ω : ℕ)) : ℝ) := Real.norm_of_nonneg (Nat.cast_nonneg _)
      _ = (((ω.val : ℕ)) : ℝ) := hNr
      _ ≤ (1 : ℝ) := by exact_mod_cast hle
  have hmemX0 : MemLp (X4 0) 2 mu4 := by
    have haesm : AEStronglyMeasurable (X4 0) mu4 :=
      (measurable_of_countable (f := X4 0)).aestronglyMeasurable
    refine MemLp.of_bound haesm 2 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖X4 0 ω‖ ≤ 2
    rw [hX0pt ω]
    norm_num [Real.norm_eq_abs]
  have hmemS : MemLp S4 2 mu4 := by
    have haesm : AEStronglyMeasurable S4 mu4 :=
      (measurable_of_countable (f := S4)).aestronglyMeasurable
    refine MemLp.of_bound haesm 2 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖S4 ω‖ ≤ 2
    have hlt : ω.val < 2 := ω.2
    have hle : ω.val ≤ 1 := by omega
    have hSnn : 0 ≤ S4 ω := by
      rw [hSeq ω]
      have hb : (0 : ℝ) ≤ ((N4 ω : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_nonneg hb h2
    have hSle : S4 ω ≤ 2 := by
      rw [hSeq ω]
      have hNr : (((N4 ω : ℕ)) : ℝ) = (((ω.val : ℕ)) : ℝ) := rfl
      rw [hNr]
      have hbr : ((ω.val : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hle
      linarith
    calc ‖S4 ω‖ = S4 ω := Real.norm_of_nonneg hSnn
      _ ≤ 2 := hSle
  have hVN : ProbabilityTheory.variance (fun ω => (N4 ω : ℝ)) mu4 = 1 / 4 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemN
    simp only [hsub, Pi.pow_apply, hEN2, hEN]
    norm_num
  have hVX : ProbabilityTheory.variance (X4 0) mu4 = 0 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemX0
    simp only [hsub, Pi.pow_apply, hEX02, hEX0]
    norm_num
  have hVS : ProbabilityTheory.variance S4 mu4 = 1 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemS
    simp only [hsub, Pi.pow_apply, hES2, hES]
    norm_num
  have hR : (∫ ω, (N4 ω : ℝ) ∂mu4) * ProbabilityTheory.variance (X4 0) mu4 +
      ProbabilityTheory.variance (fun ω => (N4 ω : ℝ)) mu4 * (∫ ω, X4 0 ω ∂mu4) ^ 2
      = 1 := by
    rw [hEN, hVX, hVN, hEX0]
    norm_num
  exact ⟨hVS, hR, hVX⟩

-- Test 5 data: count on `{0, 1}`, constant severities `1` for all `i`.
-- Unlike the pins above, this test applies the production theorem
-- `variance_stopped_sum_finite`: the constant family is i.i.d. L2 and
-- independent of the count.
private abbrev D5 : Type := Fin 2
private noncomputable def mu5 : Measure D5 :=
  ((Fintype.card D5 : ENNReal))⁻¹ • Measure.count
private def N5 : D5 → ℕ := fun ω => ω.val
private def X5 : ℕ → D5 → ℝ := fun _ _ => 1
private def S5 : D5 → ℝ := fun ω => ∑ k ∈ Finset.range (N5 ω), X5 k ω

/-- Theorem-backed pin: the production identity holds on constant severities,
both sides equal `1/4`. Fails if the production statement drifts. -/
theorem collective_variance_theorem_backed_constant :
    ProbabilityTheory.variance S5 mu5 = 1 / 4 ∧
      (∫ ω, (N5 ω : ℝ) ∂mu5) * ProbabilityTheory.variance (X5 0) mu5 +
        ProbabilityTheory.variance (fun ω => (N5 ω : ℝ)) mu5 * (∫ ω, X5 0 ω ∂mu5) ^ 2
        = 1 / 4 ∧
      ProbabilityTheory.variance S5 mu5 =
        (∫ ω, (N5 ω : ℝ) ∂mu5) * ProbabilityTheory.variance (X5 0) mu5 +
          ProbabilityTheory.variance (fun ω => (N5 ω : ℝ)) mu5 * (∫ ω, X5 0 ω ∂mu5) ^ 2 := by
  have hcard2 : Fintype.card D5 = 2 := by decide
  have hcu : Measure.count (Set.univ : Set D5) = (Fintype.card D5 : ENNReal) := by
    simp
  have hprob : IsProbabilityMeasure mu5 := by
    refine ⟨?_⟩
    show (((Fintype.card D5 : ENNReal))⁻¹ • Measure.count) Set.univ = 1
    rw [Measure.smul_apply, hcu, hcard2, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hint_eq : ∀ f : D5 → ℝ, ∫ ω, f ω ∂mu5 = (1 / 2 : ℝ) * ∑ x, f x := by
    intro f
    have hInt : Integrable f mu5 := integrable_of_fintype_prob mu5 f
    have h1 : ∫ ω, f ω ∂mu5 = ∑ x, mu5.real {x} • f x := integral_fintype hInt
    have hsing : ∀ x : D5, mu5 {x} = ((Fintype.card D5 : ENNReal))⁻¹ := by
      intro x
      show (((Fintype.card D5 : ENNReal))⁻¹ • Measure.count) {x} = _
      rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
    have hw : ∀ x : D5, mu5.real {x} = (1 / 2 : ℝ) := by
      intro x
      rw [measureReal_def, hsing, hcard2, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num
    rw [h1]
    simp only [hw, smul_eq_mul, ← Finset.mul_sum]
  have hsum_eval : ∀ g : D5 → ℝ, ∑ x, g x = g 0 + g 1 := by
    intro g
    simp only [Fin.sum_univ_two]
  have v20 : (0 : Fin 2).val = 0 := rfl
  have v21 : (1 : Fin 2).val = 1 := rfl
  have hEN : ∫ ω, (N5 ω : ℝ) ∂mu5 = 1 / 2 := by
    rw [hint_eq, hsum_eval]
    unfold N5
    norm_num [v20, v21]
  have hEN2 : ∫ ω, ((N5 ω : ℝ)) ^ 2 ∂mu5 = 1 / 2 := by
    rw [hint_eq, hsum_eval]
    unfold N5
    norm_num [v20, v21]
  have hX0pt : ∀ ω : D5, X5 0 ω = 1 := fun ω => rfl
  have hX02pt : ∀ ω : D5, (X5 0 ω) ^ 2 = 1 := fun ω => by rw [hX0pt ω]; norm_num
  have hEX0 : ∫ ω, X5 0 ω ∂mu5 = 1 := by
    have hc : (X5 0) =ᵐ[mu5] (fun _ => (1 : ℝ)) :=
      Filter.Eventually.of_forall hX0pt
    calc ∫ ω, X5 0 ω ∂mu5 = ∫ _ : D5, (1 : ℝ) ∂mu5 := integral_congr_ae hc
      _ = 1 := const_int_eq mu5 1
  have hEX02 : ∫ ω, (X5 0 ω) ^ 2 ∂mu5 = 1 := by
    have hc : (fun ω => (X5 0 ω) ^ 2) =ᵐ[mu5] (fun _ => (1 : ℝ)) :=
      Filter.Eventually.of_forall hX02pt
    calc ∫ ω, (X5 0 ω) ^ 2 ∂mu5 = ∫ _ : D5, (1 : ℝ) ∂mu5 := integral_congr_ae hc
      _ = 1 := const_int_eq mu5 1
  have hSeq : ∀ ω : D5, S5 ω = (N5 ω : ℝ) := by
    intro ω
    simp [S5, X5, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hES : ∫ ω, S5 ω ∂mu5 = 1 / 2 := by
    rw [hint_eq, hsum_eval]
    unfold S5 N5 X5
    norm_num [v20, v21, Finset.sum_range_succ, Finset.sum_range_zero]
  have hES2 : ∫ ω, (S5 ω) ^ 2 ∂mu5 = 1 / 2 := by
    rw [hint_eq, hsum_eval]
    unfold S5 N5 X5
    norm_num [v20, v21, Finset.sum_range_succ, Finset.sum_range_zero]
  have hmemN : MemLp (fun ω : D5 => (N5 ω : ℝ)) 2 mu5 := by
    have haesm : AEStronglyMeasurable (fun ω : D5 => (N5 ω : ℝ)) mu5 :=
      (measurable_of_countable (f := (fun ω : D5 => (N5 ω : ℝ)))).aestronglyMeasurable
    refine MemLp.of_bound haesm 1 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖(((N5 ω : ℕ)) : ℝ)‖ ≤ 1
    have hlt : ω.val < 2 := ω.2
    have hle : ω.val ≤ 1 := by omega
    have hNr : (((N5 ω : ℕ)) : ℝ) = (((ω.val : ℕ)) : ℝ) := rfl
    calc ‖(((N5 ω : ℕ)) : ℝ)‖ = (((N5 ω : ℕ)) : ℝ) := Real.norm_of_nonneg (Nat.cast_nonneg _)
      _ = (((ω.val : ℕ)) : ℝ) := hNr
      _ ≤ (1 : ℝ) := by exact_mod_cast hle
  have hmemX0 : MemLp (X5 0) 2 mu5 := by
    have haesm : AEStronglyMeasurable (X5 0) mu5 :=
      (measurable_of_countable (f := X5 0)).aestronglyMeasurable
    refine MemLp.of_bound haesm 1 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖X5 0 ω‖ ≤ 1
    rw [hX0pt ω]
    norm_num [Real.norm_eq_abs]
  have hmemS : MemLp S5 2 mu5 := by
    have haesm : AEStronglyMeasurable S5 mu5 :=
      (measurable_of_countable (f := S5)).aestronglyMeasurable
    refine MemLp.of_bound haesm 1 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖S5 ω‖ ≤ 1
    have hlt : ω.val < 2 := ω.2
    have hle : ω.val ≤ 1 := by omega
    have hSnn : 0 ≤ S5 ω := by
      rw [hSeq ω]
      exact Nat.cast_nonneg _
    have hSle : S5 ω ≤ 1 := by
      rw [hSeq ω]
      have hNr : (((N5 ω : ℕ)) : ℝ) = (((ω.val : ℕ)) : ℝ) := rfl
      rw [hNr]
      have hbr : ((ω.val : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hle
      linarith
    calc ‖S5 ω‖ = S5 ω := Real.norm_of_nonneg hSnn
      _ ≤ 1 := hSle
  have hVN : ProbabilityTheory.variance (fun ω => (N5 ω : ℝ)) mu5 = 1 / 4 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemN
    simp only [hsub, Pi.pow_apply, hEN2, hEN]
    norm_num
  have hVX : ProbabilityTheory.variance (X5 0) mu5 = 0 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemX0
    simp only [hsub, Pi.pow_apply, hEX02, hEX0]
    norm_num
  have hVS : ProbabilityTheory.variance S5 mu5 = 1 / 4 := by
    have hsub := ProbabilityTheory.variance_eq_sub hmemS
    simp only [hsub, Pi.pow_apply, hES2, hES]
    norm_num
  have hR : (∫ ω, (N5 ω : ℝ) ∂mu5) * ProbabilityTheory.variance (X5 0) mu5 +
      ProbabilityTheory.variance (fun ω => (N5 ω : ℝ)) mu5 * (∫ ω, X5 0 ω ∂mu5) ^ 2
      = 1 / 4 := by
    rw [hEN, hVX, hVN, hEX0]
    norm_num
  have hN : Measurable N5 := measurable_of_countable N5
  have hNb : ∀ᵐ ω ∂mu5, N5 ω ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    have hlt : ω.val < 2 := ω.2
    show ω.val ≤ 1
    omega
  have hX2 : ∀ i, MemLp (X5 i) 2 mu5 := by
    intro i
    have haesm : AEStronglyMeasurable (X5 i) mu5 := measurable_const.aestronglyMeasurable
    refine MemLp.of_bound haesm 1 ?_
    apply Filter.Eventually.of_forall
    intro ω
    show ‖X5 i ω‖ ≤ 1
    have hX : X5 i ω = 1 := rfl
    rw [hX]
    norm_num
  have hmeas : ∀ i, Measurable (X5 i) := fun i => measurable_const
  have hident : ∀ i, IdentDistrib (X5 i) (X5 0) mu5 mu5 := by
    intro i
    have hX5i : X5 i = fun _ : D5 => (1 : ℝ) := rfl
    have hX50 : X5 0 = fun _ : D5 => (1 : ℝ) := rfl
    rw [hX5i, hX50]
    exact IdentDistrib.refl measurable_const.aemeasurable
  have hindepX : iIndepFun X5 mu5 := by
    rw [iIndepFun_iff]
    intro s f' H
    have h2 : ∀ i ∈ s, f' i = Set.univ ∨ f' i = ∅ := by
      intro i hi
      have h := H i hi
      rw [MeasurableSpace.measurableSet_comap] at h
      obtain ⟨t, _, ht⟩ := h
      have hX5i : X5 i = fun _ : D5 => (1 : ℝ) := rfl
      rw [hX5i] at ht
      by_cases h1 : (1 : ℝ) ∈ t
      · left
        rw [← ht]
        ext x
        simp [h1]
      · right
        rw [← ht]
        ext x
        simp [h1]
    by_cases hall : ∀ i ∈ s, f' i = Set.univ
    · have hL : (⋂ i ∈ s, f' i) = Set.univ := by
        ext x
        simp only [Set.mem_iInter, Set.mem_univ, iff_true]
        intro i hi
        rw [hall i hi]
        trivial
      have hP : ∏ i ∈ s, mu5 (f' i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        rw [hall i hi, measure_univ]
      rw [hL, measure_univ]
      exact hP.symm
    · push Not at hall
      obtain ⟨j, hjs, hj⟩ := hall
      have hje : f' j = ∅ := (h2 j hjs).resolve_left hj
      have hL : (⋂ i ∈ s, f' i) = ∅ := by
        refine Set.eq_empty_of_forall_notMem (fun x hx => ?_)
        simp only [Set.mem_iInter] at hx
        simpa [hje] using hx j hjs
      rw [hL, measure_empty]
      exact (Finset.prod_eq_zero hjs (by rw [hje, measure_empty])).symm
  have hindepN : ProbabilityTheory.Indep (MeasurableSpace.comap N5 inferInstance)
      (⨆ i, MeasurableSpace.comap (X5 i) inferInstance) mu5 := by
    have hsup : (⨆ i, MeasurableSpace.comap (X5 i) inferInstance) = ⊥ := by
      have hX5eq : ∀ i : ℕ, X5 i = fun _ : D5 => (1 : ℝ) := fun i => rfl
      simp only [hX5eq, MeasurableSpace.comap_const, iSup_bot]
    rw [hsup]
    exact indep_bot_right _
  have hThm : ProbabilityTheory.variance S5 mu5 =
      (∫ ω, (N5 ω : ℝ) ∂mu5) * ProbabilityTheory.variance (X5 0) mu5 +
        ProbabilityTheory.variance (fun ω => (N5 ω : ℝ)) mu5 * (∫ ω, X5 0 ω ∂mu5) ^ 2 :=
    MathlibExt.Probability.Finance.FiniteCollectiveVariance.variance_stopped_sum_finite
      mu5 N5 hN 1 hNb X5 hX2 hmeas hident hindepX hindepN
  exact ⟨hVS, hR, hThm⟩

end MathlibExt.Probability.Finance.FiniteCollectiveVarianceTests
