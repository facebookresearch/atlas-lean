/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.ModiglianiMiller
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Finance.ModiglianiMiller

open MathlibExt.Economics.Finance.ModiglianiMiller

example : statePriceValue (![0.4, 0.5] : Fin 2 → ℝ)
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
  simp only [statePriceValue, Fin.sum_univ_two, hψ0, hψ1, hV0, hV1, hD0, hD1]
  norm_num

example : statePriceValue (![0.4, 0.5] : Fin 2 → ℝ)
    (fun ω => equityPayoff ((![100, 40] : Fin 2 → ℝ) ω) 50) = 20 := by
  have hψ0 : ((![0.4, 0.5] : Fin 2 → ℝ) 0) = 0.4 := by simp
  have hψ1 : ((![0.4, 0.5] : Fin 2 → ℝ) 1) = 0.5 := by simp
  have hV0 : ((![100, 40] : Fin 2 → ℝ) 0) = 100 := by simp
  have hV1 : ((![100, 40] : Fin 2 → ℝ) 1) = 40 := by simp
  have hE0 : equityPayoff 100 50 = 50 := by
    show max ((100 : ℝ) - 50) 0 = 50
    have hle : (0 : ℝ) ≤ 100 - 50 := by norm_num
    rw [max_eq_left hle]
    norm_num
  have hE1 : equityPayoff 40 50 = 0 := by
    show max ((40 : ℝ) - 50) 0 = 0
    have hle : (40 : ℝ) - 50 ≤ 0 := by norm_num
    rw [max_eq_right hle]
  simp only [statePriceValue, Fin.sum_univ_two, hψ0, hψ1, hV0, hV1, hE0, hE1]
  norm_num

example : statePriceValue (![0.4, 0.5] : Fin 2 → ℝ)
      (fun ω => debtPayoff ((![100, 40] : Fin 2 → ℝ) ω) 50) +
      statePriceValue (![0.4, 0.5] : Fin 2 → ℝ)
        (fun ω => equityPayoff ((![100, 40] : Fin 2 → ℝ) ω) 50) =
      statePriceValue (![0.4, 0.5] : Fin 2 → ℝ) (![100, 40] : Fin 2 → ℝ) ∧
    statePriceValue (![0.4, 0.5] : Fin 2 → ℝ) (![100, 40] : Fin 2 → ℝ) = 60 := by
  constructor
  · exact modiglianiMiller_value _ _ _
  · have hψ0 : ((![0.4, 0.5] : Fin 2 → ℝ) 0) = 0.4 := by simp
    have hψ1 : ((![0.4, 0.5] : Fin 2 → ℝ) 1) = 0.5 := by simp
    have hV0 : ((![100, 40] : Fin 2 → ℝ) 0) = 100 := by simp
    have hV1 : ((![100, 40] : Fin 2 → ℝ) 1) = 40 := by simp
    simp only [statePriceValue, Fin.sum_univ_two, hψ0, hψ1, hV0, hV1]
    norm_num

end MathlibExtTest.Economics.Finance.ModiglianiMiller
