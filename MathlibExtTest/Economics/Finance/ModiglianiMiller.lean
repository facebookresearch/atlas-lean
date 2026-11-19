/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.ModiglianiMiller
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Finance.ModiglianiMiller

open MathlibExt.Economics.Finance.ModiglianiMiller
open MathlibExt.Probability.Finance.OptionPayoffs (europeanCallPayoff)
open MathlibExt.Probability.Finance.StatePriceVector (NoFundedArbitrage)

example : weightedValue (![0.4, 0.5] : Fin 2 → ℝ)
    (fun ω => debtPayoff ((![100, 40] : Fin 2 → ℝ) ω) 50) = 40 := by
  have hψ0 : ((![0.4, 0.5] : Fin 2 → ℝ) 0) = 0.4 := by simp
  have hψ1 : ((![0.4, 0.5] : Fin 2 → ℝ) 1) = 0.5 := by simp
  have hV0 : ((![100, 40] : Fin 2 → ℝ) 0) = 100 := by simp
  have hV1 : ((![100, 40] : Fin 2 → ℝ) 1) = 40 := by simp
  have hD0 : debtPayoff 100 50 = 50 := by
    show min (100 : ℝ) 50 = 50
    have hle : (50 : ℝ) ≤ 100 := by norm_num
    rw [min_eq_right hle]
  have hD1 : debtPayoff 40 50 = 40 := by
    show min (40 : ℝ) 50 = 40
    have hle : (40 : ℝ) ≤ 50 := by norm_num
    rw [min_eq_left hle]
  simp only [weightedValue, Fin.sum_univ_two, hψ0, hψ1, hV0, hV1, hD0, hD1]
  norm_num

example : weightedValue (![0.4, 0.5] : Fin 2 → ℝ)
    (fun ω => europeanCallPayoff ((![100, 40] : Fin 2 → ℝ) ω) 50) = 20 := by
  have hψ0 : ((![0.4, 0.5] : Fin 2 → ℝ) 0) = 0.4 := by simp
  have hψ1 : ((![0.4, 0.5] : Fin 2 → ℝ) 1) = 0.5 := by simp
  have hV0 : ((![100, 40] : Fin 2 → ℝ) 0) = 100 := by simp
  have hV1 : ((![100, 40] : Fin 2 → ℝ) 1) = 40 := by simp
  have hE0 : europeanCallPayoff 100 50 = 50 := by
    show max ((100 : ℝ) - 50) 0 = 50
    have hle : (0 : ℝ) ≤ 100 - 50 := by norm_num
    rw [max_eq_left hle]
    norm_num
  have hE1 : europeanCallPayoff 40 50 = 0 := by
    show max ((40 : ℝ) - 50) 0 = 0
    have hle : (40 : ℝ) - 50 ≤ 0 := by norm_num
    rw [max_eq_right hle]
  simp only [weightedValue, Fin.sum_univ_two, hψ0, hψ1, hV0, hV1, hE0, hE1]
  norm_num

example : weightedValue (![0.4, 0.5] : Fin 2 → ℝ)
      (fun ω => debtPayoff ((![100, 40] : Fin 2 → ℝ) ω) 50) +
      weightedValue (![0.4, 0.5] : Fin 2 → ℝ)
        (fun ω => europeanCallPayoff ((![100, 40] : Fin 2 → ℝ) ω) 50) =
      weightedValue (![0.4, 0.5] : Fin 2 → ℝ) (![100, 40] : Fin 2 → ℝ) ∧
    weightedValue (![0.4, 0.5] : Fin 2 → ℝ) (![100, 40] : Fin 2 → ℝ) = 60 := by
  constructor
  · exact weightedValue_debtPayoff_add_europeanCallPayoff _ _ _
  · have hψ0 : ((![0.4, 0.5] : Fin 2 → ℝ) 0) = 0.4 := by simp
    have hψ1 : ((![0.4, 0.5] : Fin 2 → ℝ) 1) = 0.5 := by simp
    have hV0 : ((![100, 40] : Fin 2 → ℝ) 0) = 100 := by simp
    have hV1 : ((![100, 40] : Fin 2 → ℝ) 1) = 40 := by simp
    simp only [weightedValue, Fin.sum_univ_two, hψ0, hψ1, hV0, hV1]
    norm_num

/-! ### Modigliani–Miller I in an arbitrage-free market -/

/-- Three securities on two states: the unlevered firm pays `V = (100, 40)`, the debt with face
value `50` pays `(50, 40)`, and the equity pays `(50, 0)`. -/
def mmPayoff : Fin 3 → Fin 2 → ℝ := ![![100, 40], ![50, 40], ![50, 0]]

theorem mmPayoff_debt (ω : Fin 2) : mmPayoff 1 ω = debtPayoff (mmPayoff 0 ω) 50 := by
  fin_cases ω <;> norm_num [mmPayoff, debtPayoff, min_def]

theorem mmPayoff_equity (ω : Fin 2) :
    mmPayoff 2 ω = europeanCallPayoff (mmPayoff 0 ω) 50 := by
  fin_cases ω <;> norm_num [mmPayoff, europeanCallPayoff, max_def]

/-- There is no funded arbitrage at the prices `(70, 45, 25)` and gross return `R = 1`: every funded
gain is a multiple of `(1, -1)`, so it cannot be nonnegative in both states and positive in one. -/
theorem mm_noArb : NoFundedArbitrage mmPayoff ![70, 45, 25] 1 := by
  rintro ⟨h, hnonneg, ω, hpos⟩
  have h0 := hnonneg 0
  have h1 := hnonneg 1
  fin_cases ω <;> simp [mmPayoff, Fin.sum_univ_three] at h0 h1 hpos <;> linarith

/-- Modigliani–Miller I in that market: debt `45` plus equity `25` equals the firm's `70`. -/
example : (![70, 45, 25] : Fin 3 → ℝ) 1 + ![70, 45, 25] 2 = ![70, 45, 25] 0 :=
  modiglianiMiller_of_no_arbitrage mmPayoff ![70, 45, 25] 1 one_pos mm_noArb (mmPayoff 0) 50
    (fun _ => rfl) mmPayoff_debt mmPayoff_equity

/-- No arbitrage pins the equity price: for any prices without funded arbitrage at any gross
return `R > 0`, if the unlevered firm trades at `70` and the debt at `45`, the equity trades at
`25`. -/
example (p : Fin 3 → ℝ) (R : ℝ) (hR : 0 < R) (hNA : NoFundedArbitrage mmPayoff p R)
    (hu : p 0 = 70) (hd : p 1 = 45) : p 2 = 25 := by
  have h := modiglianiMiller_of_no_arbitrage mmPayoff p R hR hNA (mmPayoff 0) 50
    (fun _ => rfl) mmPayoff_debt mmPayoff_equity
  linarith

end MathlibExtTest.Economics.Finance.ModiglianiMiller
