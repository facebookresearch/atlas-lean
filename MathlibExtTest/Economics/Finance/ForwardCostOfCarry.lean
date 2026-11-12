/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.ForwardCostOfCarry
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Finance.ForwardCostOfCarry

open MathlibExt.Economics.Finance.ForwardCostOfCarry

def S1 : Fin 2 → ℝ := ![110, 90]
def psi1 : Fin 2 → ℝ := ![0.4, 0.6]
def psi2 : Fin 2 → ℝ := ![0.3, 0.5]

example : (S1 0 + 5) - 103 * (1 : ℝ) = S1 0 - 98 := by
  have hF : (98 : ℝ) = 103 * 1 - 5 := by norm_num
  exact forward_replication_payoff hF 0

example : ∑ ω, psi1 ω = 1 / (1 : ℝ) := by
  rw [Fin.sum_univ_two]
  simp [psi1]
  norm_num

example : statePriceValue psi1 (fun ω => S1 ω + 5) = 103 := by
  simp only [statePriceValue, Fin.sum_univ_two]
  simp [psi1, S1]
  norm_num

example : statePriceValue psi1 (fun ω => S1 ω - 98) = 0 := by
  simp only [statePriceValue, Fin.sum_univ_two]
  simp [psi1, S1]
  norm_num

example (F : ℝ) (hforward : statePriceValue psi1 (fun ω => S1 ω - F) = 0) : F = 98 := by
  have hR : (1 : ℝ) ≠ 0 := one_ne_zero
  have hψ : ∑ ω, psi1 ω = 1 / (1 : ℝ) := by
    rw [Fin.sum_univ_two]
    simp [psi1]
    norm_num
  have hunderlying : statePriceValue psi1 (fun ω => S1 ω + 5) = 103 := by
    simp only [statePriceValue, Fin.sum_univ_two]
    simp [psi1, S1]
    norm_num
  have h := forward_cost_of_carry psi1 (S := S1) (S0 := 103) (R := 1) (inc := 5) (F := F) hR hψ hunderlying hforward
  norm_num at h
  exact h

example : ∑ ω, psi2 ω = 1 / ((5 / 4 : ℝ)) := by
  rw [Fin.sum_univ_two]
  simp [psi2]
  norm_num

example : statePriceValue psi2 (fun ω => S1 ω + 4) = 406 / 5 := by
  simp only [statePriceValue, Fin.sum_univ_two]
  simp [psi2, S1]
  norm_num

example : statePriceValue psi2 (fun ω => S1 ω - 195 / 2) = 0 := by
  simp only [statePriceValue, Fin.sum_univ_two]
  simp [psi2, S1]
  norm_num

example (F : ℝ) (hforward : statePriceValue psi2 (fun ω => S1 ω - F) = 0) : F = 195 / 2 := by
  have hR : ((5 / 4 : ℝ)) ≠ 0 := by norm_num
  have hψ : ∑ ω, psi2 ω = 1 / ((5 / 4 : ℝ)) := by
    rw [Fin.sum_univ_two]
    simp [psi2]
    norm_num
  have hunderlying : statePriceValue psi2 (fun ω => S1 ω + 4) = 406 / 5 := by
    simp only [statePriceValue, Fin.sum_univ_two]
    simp [psi2, S1]
    norm_num
  have h := forward_cost_of_carry psi2 (S := S1) (S0 := 406 / 5) (R := 5 / 4) (inc := 4) (F := F) hR hψ hunderlying hforward
  norm_num at h
  exact h

end MathlibExtTest.Economics.Finance.ForwardCostOfCarry
