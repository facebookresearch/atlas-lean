/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.PackingLowerBound

/-!
# Packing lower bound tests

Concrete instantiations of the finite packing lower bounds on small
databases and a randomized response mechanism.
-/

@[expose] public section

namespace CSLibExtTest.Privacy.PackingLowerBoundTests

open CSLibExt.Privacy.DifferentialPrivacy
open scoped ENNReal NNReal

@[simp] private theorem rrTest_quarters1 : (4⁻¹ + 3 / 4 : ℝ≥0∞) = 1 := by
  have h4 : (4 : ℝ≥0∞) = ((4 : ℝ≥0) : ℝ≥0∞) := by norm_cast
  have h3 : (3 : ℝ≥0∞) = ((3 : ℝ≥0) : ℝ≥0∞) := by norm_cast
  have h4ne : (4 : ℝ≥0) ≠ 0 := by norm_num
  rw [h4, h3, ← ENNReal.coe_inv h4ne, ← ENNReal.coe_div h4ne, ← ENNReal.coe_add,
    show ((4 : ℝ≥0)⁻¹ + 3 / 4) = 1 by norm_num, ENNReal.coe_one]

@[simp] private theorem rrTest_quarters2 : (3 / 4 + 4⁻¹ : ℝ≥0∞) = 1 := by
  have h4 : (4 : ℝ≥0∞) = ((4 : ℝ≥0) : ℝ≥0∞) := by norm_cast
  have h3 : (3 : ℝ≥0∞) = ((3 : ℝ≥0) : ℝ≥0∞) := by norm_cast
  have h4ne : (4 : ℝ≥0) ≠ 0 := by norm_num
  rw [h4, h3, ← ENNReal.coe_inv h4ne, ← ENNReal.coe_div h4ne, ← ENNReal.coe_add,
    show (3 / 4 + (4 : ℝ≥0)⁻¹) = 1 by norm_num, ENNReal.coe_one]

private noncomputable def rrTest (d : Bool) : PMF Bool := PMF.ofFintype (fun b => ((if b = d then 3 / 4 else 1 / 4 : ℝ≥0) : ℝ≥0∞)) (by cases d <;> norm_num)

private theorem rrTest_isDP : IsDP rrTest (fun _ _ => True) (Real.log 3) := by
  refine ⟨Real.log_nonneg (by norm_num), fun d d' _ o => ?_⟩
  have hexp : ENNReal.ofReal (Real.exp (Real.log 3)) = (3 : ℝ≥0∞) := by
    rw [Real.exp_log (by norm_num), ENNReal.ofReal_ofNat]
  have h3c : (3 : ℝ≥0∞) = ((3 : ℝ≥0) : ℝ≥0∞) := by norm_cast
  have h4c : (4 : ℝ≥0∞) = ((4 : ℝ≥0) : ℝ≥0∞) := by norm_cast
  have h4ne : (4 : ℝ≥0) ≠ 0 := by norm_num
  cases d <;> cases d' <;> cases o <;>
    simp [rrTest, PMF.ofFintype_apply, hexp] <;>
    simp only [h3c, h4c, ← ENNReal.coe_div h4ne, ← ENNReal.coe_inv h4ne,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe] <;>
    norm_num

private theorem rr_hchain : ∀ i : Fin 2,
    ∃ k ≤ 1, Relation.RelatesInSteps (fun _ _ => True) (decide (i = 1)) false k := by
  intro i
  fin_cases i
  · exact ⟨0, Nat.zero_le 1, Relation.RelatesInSteps.zero_iff.mpr (by decide)⟩
  · exact ⟨1, le_rfl, Relation.RelatesInSteps.single trivial⟩

private theorem rr_hdisj : Pairwise (fun i j : Fin 2 =>
    Disjoint ({decide (i = 1)} : Set Bool) ({decide (j = 1)} : Set Bool)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp at hij
  · simp only [Set.disjoint_singleton_left, Set.mem_singleton_iff]
    decide
  · simp only [Set.disjoint_singleton_left, Set.mem_singleton_iff]
    decide
  · simp at hij

private theorem rr_hprob : ∀ i : Fin 2,
    (3 / 4 : ℝ) ≤ ((rrTest (decide (i = 1))).toOuterMeasure
      ({decide (i = 1)} : Set Bool)).toReal := by
  intro i
  rw [PMF.toOuterMeasure_apply_singleton]
  simp [rrTest, PMF.ofFintype_apply]

theorem test_histCount_packingDB : histCount (histPackingDB (n := 3) (N := 2) 2 0 1) 1 = 2 ∧ histCount (histPackingDB (n := 3) (N := 2) 2 0 1) 0 = 1 := by
  refine ⟨by decide, by decide⟩

theorem test_histFreq_packingDB : histFreq (histPackingDB (n := 3) (N := 2) 2 0 1) 1 = 2 / 3 := by
  have hc := test_histCount_packingDB.1
  unfold histFreq
  rw [hc]
  norm_num

theorem test_histPackingDB_values : histPackingDB (n := 3) (N := 2) 2 0 1 0 = 1 ∧ histPackingDB (n := 3) (N := 2) 2 0 1 1 = 1 ∧ histPackingDB (n := 3) (N := 2) 2 0 1 2 = 0 := by
  refine ⟨by decide, by decide, by decide⟩

theorem test_histAccurate_disjoint_two : Disjoint (histAccurate (1 / 4 : ℝ) (histPackingDB (n := 3) (N := 2) 2 0 0)) (histAccurate (1 / 4 : ℝ) (histPackingDB (n := 3) (N := 2) 2 0 1)) := by
  have h := histAccurate_pairwise_disjoint (n := 3) (N := 2) (m := 2) (α := 1 / 4)
    (by norm_num) (by norm_num) (0 : Fin 2)
  exact h (show (0 : Fin 2) ≠ 1 by decide)

theorem test_toOuterMeasure_sum_le_one_bool : ∑ b : Bool, (PMF.pure false).toOuterMeasure ({b} : Set Bool) ≤ 1 := by
  exact toOuterMeasure_sum_le_one (PMF.pure false) (fun b : Bool => ({b} : Set Bool))
    (fun b₁ b₂ hne => by
      simp only [Set.disjoint_singleton_left, Set.mem_singleton_iff]
      exact hne)

theorem test_packing_pure_rr : (2 : ℝ) * (3 / 4) ≤ 3 := by
  have hbase := packing_lower_bound_pure (I := Fin 2) (M := rrTest) (adj := fun _ _ => True)
    (ε := Real.log 3) (p := 3 / 4) (m := 1) rrTest_isDP false
    (fun i : Fin 2 => decide (i = 1)) (fun i => ({decide (i = 1)} : Set Bool))
    rr_hchain rr_hdisj rr_hprob
  have e3 : Real.exp (((1 : ℕ) : ℝ) * Real.log 3) = 3 := by
    rw [Nat.cast_one, one_mul, Real.exp_log (by norm_num)]
  rw [Fintype.card_fin, e3] at hbase
  simpa using hbase

theorem test_packing_pure_log_rr : Real.log ((2 : ℝ) * (3 / 4)) ≤ Real.log 3 := by
  have hbase := packing_lower_bound_pure_log (I := Fin 2) (M := rrTest) (adj := fun _ _ => True)
    (ε := Real.log 3) (p := 3 / 4) (m := 1) rrTest_isDP false
    (fun i : Fin 2 => decide (i = 1)) (fun i => ({decide (i = 1)} : Set Bool))
    rr_hchain rr_hdisj rr_hprob (by rw [Fintype.card_fin]; norm_num) (by norm_num)
  rw [Fintype.card_fin, Nat.cast_one, one_mul] at hbase
  simpa using hbase

theorem test_packing_approx_vacuous : (Fintype.card (Fin 2) : ℝ) * ((1 / 2 : ℝ) * Real.exp (-((1 : ℝ) * 0)) - (1 : ℝ) * 1) ≤ 1 := by
  have h := packing_lower_bound_approx_vacuous_of_delta_large (I := Fin 2) (m := 1)
    (ε := 0) (δ := 1) (p := 1 / 2) (by norm_num [Real.exp_zero])
  simpa using h

theorem test_histogram_packing_inst {M : (Fin 1 → Fin 2) → PMF (Fin 2 → ℝ)} {ε p : ℝ} (hM : IsDP M ReplaceOne ε) (hprob : ∀ d : Fin 1 → Fin 2, p ≤ ((M d).toOuterMeasure (histAccurate (1 / 4 : ℝ) d)).toReal) : (2 : ℝ) * p ≤ Real.exp ((1 : ℝ) * ε) := by
  have h := histogram_packing_lower_bound (n := 1) (N := 2) (m := 1) (α := 1 / 4)
    (0 : Fin 2) le_rfl (by norm_num) hM hprob
  simpa using h

theorem test_histogram_sample_complexity_inst {M : (Fin 2 → Fin 2) → PMF (Fin 2 → ℝ)} {ε p : ℝ} (hM : IsDP M ReplaceOne ε) (hprob : ∀ d : Fin 2 → Fin 2, p ≤ ((M d).toOuterMeasure (histAccurate (1 / 4 : ℝ) d)).toReal) (hp : 0 < p) (hε : 0 < ε) : Real.log ((2 : ℝ) * p) / ε ≤ (2 : ℝ) := by
  have h := histogram_sample_complexity_lower_bound (n := 2) (N := 2) (α := 1 / 4)
    (0 : Fin 2) (by norm_num) hM hprob hp hε
  simpa using h

#print axioms packing_lower_bound_approx
#print axioms packing_lower_bound_pure
#print axioms histogram_packing_lower_bound

end CSLibExtTest.Privacy.PackingLowerBoundTests
