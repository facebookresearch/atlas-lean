/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Code.BeffaraDC.SelfDualValue
import Code.BeffaraDC.RussoHamming
import Code.BeffaraDC.FiniteMoments
import Code.BeffaraDC.AnnulusDefs

namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset






theorem selfDualPoint_value (q : ℝ) :
    selfDualPoint q = Real.sqrt q / (1 + Real.sqrt q) := rfl


theorem selfDualPoint_pos {q : ℝ} (hq : 0 < q) : 0 < selfDualPoint q :=
  (selfDualPoint_mem_Ioo hq).1


theorem selfDualPoint_lt_one {q : ℝ} (hq : 0 < q) : selfDualPoint q < 1 :=
  (selfDualPoint_mem_Ioo hq).2



theorem selfDualPoint_dual_eq {q : ℝ} (hq : 0 < q) :
    dualParam (selfDualPoint q) q = selfDualPoint q :=
  selfDualPoint_is_fixed hq















variable {E : Type*} [Fintype E] [DecidableEq E]


private theorem mul_le_mul_left_of_nonneg {b x y : ℝ} (hb : 0 ≤ b) (hxy : x ≤ y) :
    b * x ≤ b * y := mul_le_mul_of_nonneg_left hxy hb










theorem decay_of_linear_hamming {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ < p₂)
    (hp2 : p₂ < 1) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {a n : ℝ}
    (hLinearHamming : a * n ≤ expect p₂ (fun ω => (hammingToSet A ω : ℝ)))
    (hprobOne : prob p₂ A ≤ 1) :
    prob p₁ A ≤ Real.exp (- 4 * (p₂ - p₁) * (a * n)) := by
  
  have hrh := russoHammingIntegrated hp1 hp12 hp2 A hA
  set H₂ := expect p₂ (fun ω => (hammingToSet A ω : ℝ)) with hH₂
  
  have hcoef : (0 : ℝ) ≤ 4 * (p₂ - p₁) := by
    have : (0 : ℝ) < p₂ - p₁ := by linarith
    positivity
  
  have hexp_mono : Real.exp (- 4 * (p₂ - p₁) * H₂)
      ≤ Real.exp (- 4 * (p₂ - p₁) * (a * n)) := by
    refine Real.exp_le_exp.mpr ?_
    have : 4 * (p₂ - p₁) * (a * n) ≤ 4 * (p₂ - p₁) * H₂ :=
      mul_le_mul_left_of_nonneg hcoef hLinearHamming
    nlinarith [this]
  
  have hprob_nn : 0 ≤ prob p₂ A := prob_nonneg (by linarith) hp2.le A
  have hexp_pos : 0 < Real.exp (- 4 * (p₂ - p₁) * H₂) := Real.exp_pos _
  calc prob p₁ A
      ≤ prob p₂ A * Real.exp (- 4 * (p₂ - p₁) * H₂) := hrh
    _ ≤ 1 * Real.exp (- 4 * (p₂ - p₁) * H₂) := by
        exact mul_le_mul_of_nonneg_right hprobOne hexp_pos.le
    _ = Real.exp (- 4 * (p₂ - p₁) * H₂) := one_mul _
    _ ≤ Real.exp (- 4 * (p₂ - p₁) * (a * n)) := hexp_mono





theorem decay_rate_of_linear_hamming {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ < p₂)
    (hp2 : p₂ < 1) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {a n : ℝ} (ha : 0 < a) (hn : 0 ≤ n)
    (hLinearHamming : a * n ≤ expect p₂ (fun ω => (hammingToSet A ω : ℝ)))
    (hprobOne : prob p₂ A ≤ 1) :
    0 < 4 * (p₂ - p₁) * a ∧ prob p₁ A ≤ Real.exp (- (4 * (p₂ - p₁) * a) * n) := by
  have hrate : 0 < 4 * (p₂ - p₁) * a := by
    have : (0 : ℝ) < p₂ - p₁ := by linarith
    positivity
  refine ⟨hrate, ?_⟩
  
  have _hn := hn
  have h := decay_of_linear_hamming hp1 hp12 hp2 A hA hLinearHamming hprobOne
  have heq : (- 4 * (p₂ - p₁) * (a * n)) = (- (4 * (p₂ - p₁) * a) * n) := by ring
  rwa [heq] at h





































theorem crossing_dichotomy {q : ℝ} (hq : 1 ≤ q) {p p₂ : ℝ}
    (hp0 : 0 < p) (hp_sd : p < selfDualPoint q) (hsd_p2 : selfDualPoint q ≤ p₂)
    (hp2 : p₂ < 1) (A : ℕ → Set (ConfigSpace E)) (hA : ∀ n, IsIncreasing (A n))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hprobOne : ∀ n : ℕ, prob p₂ (A n) ≤ 1)
    (hLinearHamming : ∀ n : ℕ,
      a * (n : ℝ) ≤ expect p₂ (fun ω => (hammingToSet (A n) ω : ℝ)))
    (hRSWLowerBound : ∀ n : ℕ, b ≤ prob (selfDualPoint q) (A n)) :
    
    ∃ c > 0, (∀ n : ℕ, prob p (A n) ≤ Real.exp (- c * (n : ℝ)))
      
      ∧ (0 < b ∧ ∀ n : ℕ, b ≤ prob (selfDualPoint q) (A n)) := by
  
  
  have _hq : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hp12 : p < p₂ := lt_of_lt_of_le hp_sd hsd_p2
  refine ⟨4 * (p₂ - p) * a, ?_, ?_, hb, hRSWLowerBound⟩
  · 
    have : (0 : ℝ) < p₂ - p := by linarith
    positivity
  · intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    exact (decay_rate_of_linear_hamming hp0 hp12 hp2 (A n) (hA n) ha hn
      (hLinearHamming n) (hprobOne n)).2








theorem beffaraDC_dichotomy {q : ℝ} (hq : 1 ≤ q) {p p₂ : ℝ}
    (hp0 : 0 < p) (hp_sd : p < Real.sqrt q / (1 + Real.sqrt q))
    (hsd_p2 : Real.sqrt q / (1 + Real.sqrt q) ≤ p₂) (hp2 : p₂ < 1)
    (A : ℕ → Set (ConfigSpace E)) (hA : ∀ n, IsIncreasing (A n))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hprobOne : ∀ n : ℕ, prob p₂ (A n) ≤ 1)
    (hLinearHamming : ∀ n : ℕ,
      a * (n : ℝ) ≤ expect p₂ (fun ω => (hammingToSet (A n) ω : ℝ)))
    (hRSWLowerBound : ∀ n : ℕ,
      b ≤ prob (Real.sqrt q / (1 + Real.sqrt q)) (A n)) :
    ∃ c > 0,
      (∀ n : ℕ, prob p (A n) ≤ Real.exp (- c * (n : ℝ)))
      ∧ (0 < b ∧ ∀ n : ℕ, b ≤ prob (Real.sqrt q / (1 + Real.sqrt q)) (A n)) := by
  
  have hval : Real.sqrt q / (1 + Real.sqrt q) = selfDualPoint q :=
    (selfDualPoint_value q).symm
  rw [hval] at hp_sd hsd_p2 hRSWLowerBound ⊢
  exact crossing_dichotomy hq hp0 hp_sd hsd_p2 hp2 A hA ha hb
    hprobOne hLinearHamming hRSWLowerBound

end BeffaraDC

end StatMech

