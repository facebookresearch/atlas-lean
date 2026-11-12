/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Exchange.PriceNormalization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics MathlibExt.Economics.Exchange

namespace MathlibExtTest.Economics.Exchange.PriceNormalization

namespace PriceNormalizationExamples

/-- Linear utility `x₀ + x₁` for both consumers. -/
def linU : Fin 2 → (Fin 2 → ℝ) → ℝ := fun _ x => x 0 + x 1

/-- Consumer `0` owns good `0`, consumer `1` owns good `1`. -/
def endow : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- No trade at prices `(1, 1)` is a Walrasian equilibrium. -/
theorem noTrade_eq_one : IsWalrasianEquilibrium linU endow ![1, 1] endow := by
  refine ⟨?hendow, ?hnn, ?hdem, rfl⟩
  · simp only [SecondWelfareTheorem.consumptionSet, Set.mem_ofPred_eq]
    intro i
    fin_cases i
    · intro j
      fin_cases j
      · show (0 : ℝ) ≤ 1; norm_num
      · show (0 : ℝ) ≤ 0; norm_num
    · intro j
      fin_cases j
      · show (0 : ℝ) ≤ 0; norm_num
      · show (0 : ℝ) ≤ 1; norm_num
  · intro l
    fin_cases l
    · show (0 : ℝ) ≤ 1; norm_num
    · show (0 : ℝ) ≤ 1; norm_num
  · intro i
    have h01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases h01 with rfl | rfl
    · simp only [Consumer.IsMarshallianDemand, Consumer.budgetSet,
        SecondWelfareTheorem.consumptionSet, Set.mem_ofPred_eq]
      refine ⟨⟨?hx0, le_rfl⟩, ?hopt0⟩
      · intro j
        fin_cases j
        · show (0 : ℝ) ≤ 1; norm_num
        · show (0 : ℝ) ≤ 0; norm_num
      · intro y hy
        obtain ⟨-, hy1⟩ := hy
        have hwealth : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ endow 0 = (1 : ℝ) := by
          have h : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = (1 : ℝ) := by
            simp [dotProduct, Fin.sum_univ_two]
          exact h
        have hdot : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + y 1 := by
          simp [dotProduct, Fin.sum_univ_two]
        rw [hwealth, hdot] at hy1
        have huv : linU 0 y = y 0 + y 1 := rfl
        have huve : linU 0 (endow 0) = 1 + 0 := rfl
        rw [huv, huve]
        linarith
    · simp only [Consumer.IsMarshallianDemand, Consumer.budgetSet,
        SecondWelfareTheorem.consumptionSet, Set.mem_ofPred_eq]
      refine ⟨⟨?hx1, le_rfl⟩, ?hopt1⟩
      · intro j
        fin_cases j
        · show (0 : ℝ) ≤ 0; norm_num
        · show (0 : ℝ) ≤ 1; norm_num
      · intro y hy
        obtain ⟨-, hy1⟩ := hy
        have hwealth : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ endow 1 = (1 : ℝ) := by
          have h : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = (1 : ℝ) := by
            simp [dotProduct, Fin.sum_univ_two]
          exact h
        have hdot : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + y 1 := by
          simp [dotProduct, Fin.sum_univ_two]
        rw [hwealth, hdot] at hy1
        have huv : linU 1 y = y 0 + y 1 := rfl
        have huve : linU 1 (endow 1) = 0 + 1 := rfl
        rw [huv, huve]
        linarith

/-- ... and so is no trade at the rescaled prices `(2, 2)`. -/
theorem noTrade_eq_two : IsWalrasianEquilibrium linU endow ![2, 2] endow := by
  have h2 : (![2, 2] : Fin 2 → ℝ) = (2 : ℝ) • ![1, 1] := by
    ext j
    fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul]
  rw [h2]
  have hpos : (0 : ℝ) < 2 := by norm_num
  exact (isWalrasianEquilibrium_smul_iff _ _ hpos _ _).mpr noTrade_eq_one

/-- Scaling by zero fails: at zero prices every bundle is affordable and no bundle is demanded. -/
theorem noTrade_not_eq_zero : ¬ IsWalrasianEquilibrium linU endow 0 endow := by
  rintro ⟨-, -, hdem, -⟩
  have h0 := hdem 0
  simp only [Consumer.IsMarshallianDemand, Consumer.budgetSet,
    SecondWelfareTheorem.consumptionSet, Set.mem_ofPred_eq] at h0
  obtain ⟨hmem, hmax⟩ := h0
  have hmem2 : (∀ l, 0 ≤ (![2, 0] : Fin 2 → ℝ) l) ∧
      (0 : Fin 2 → ℝ) ⬝ᵥ ![2, 0] ≤ (0 : Fin 2 → ℝ) ⬝ᵥ endow 0 := by
    constructor
    · intro j
      fin_cases j
      · show (0 : ℝ) ≤ 2; norm_num
      · show (0 : ℝ) ≤ 0; norm_num
    · rw [zero_dotProduct, zero_dotProduct]
  have hle := hmax ![2, 0] hmem2
  have e1 : linU 0 ![2, 0] = 2 + 0 := rfl
  have e2 : linU 0 (endow 0) = 1 + 0 := rfl
  rw [e1, e2] at hle
  norm_num at hle

end PriceNormalizationExamples

end MathlibExtTest.Economics.Exchange.PriceNormalization
