/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.FirstWelfare
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

/-! Examples for `MathlibExt.Economics.FirstWelfare`: a two-agent, two-good exchange economy with linear utilities whose endowment allocation is a Walrasian equilibrium and hence Pareto efficient, and a satiated variant whose equilibrium is not Pareto efficient. -/

namespace MathlibExtTest.Economics.FirstWelfare

section Examples

open MathlibExt.Economics

def exPrice : Fin 2 → ℝ := fun _ => 1

def exEndow : Fin 2 → Fin 2 → ℝ := fun i l => if i = l then 1 else 0

def exAlloc : Fin 2 → Fin 2 → ℝ := exEndow

theorem exFin01 : (0 : Fin 2) ≠ 1 := by decide

theorem exFin10 : (1 : Fin 2) ≠ 0 := by decide

theorem exPrice_nonneg : 0 ≤ exPrice := by
  intro l
  show (0 : ℝ) ≤ 1
  exact zero_le_one

theorem exPrice_dot (y : Fin 2 → ℝ) : exPrice ⬝ᵥ y = y 0 + y 1 := by
  simp only [exPrice, dotProduct, Fin.sum_univ_two, one_mul]

theorem exEndow_dot0 : exPrice ⬝ᵥ exEndow 0 = 1 := by
  simp [exPrice, exEndow]

theorem exEndow_dot1 : exPrice ⬝ᵥ exEndow 1 = 1 := by
  simp [exPrice, exEndow]

theorem exAlloc_val0 : exAlloc 0 0 + exAlloc 0 1 = 1 := by
  simp [exAlloc, exEndow]

theorem exAlloc_val1 : exAlloc 1 0 + exAlloc 1 1 = 1 := by
  simp [exAlloc, exEndow]

def exLinEcon : ExchangeEconomy (Fin 2) (Fin 2) where
  endowment := exEndow
  utility := fun _ y => y 0 + y 1

theorem exLin_locallyNonsatiated : exLinEcon.LocallyNonsatiated := by
  intro i x hx ε hε
  refine ⟨fun l => x l + ε / 2, ?_, ?_, ?_⟩
  · intro l
    show 0 ≤ x l + ε / 2
    have hxl : 0 ≤ x l := hx l
    linarith
  · intro l
    show |x l + ε / 2 - x l| < ε
    have e : x l + ε / 2 - x l = ε / 2 := by ring
    rw [e, abs_of_pos (by linarith : 0 < ε / 2)]
    linarith
  · show x 0 + x 1 < x 0 + ε / 2 + (x 1 + ε / 2)
    linarith

theorem exAlloc_feasible : exLinEcon.IsFeasible exAlloc := by
  constructor
  · intro i
    fin_cases i <;> intro l <;> fin_cases l <;>
      norm_num [exAlloc, exEndow, exFin01, exFin10]
  · exact le_rfl

theorem exLin_isWalrasian : exLinEcon.IsWalrasianEquilibrium exPrice exAlloc := by
  refine ⟨exPrice_nonneg, exAlloc_feasible, ?_⟩
  rw [Fin.forall_fin_two]
  constructor
  · refine ⟨le_rfl, ?_⟩
    intro y _ hy_afford
    have hend : exPrice ⬝ᵥ exLinEcon.endowment 0 = 1 := exEndow_dot0
    rw [exPrice_dot, hend] at hy_afford
    show y 0 + y 1 ≤ exAlloc 0 0 + exAlloc 0 1
    rw [exAlloc_val0]
    exact hy_afford
  · refine ⟨le_rfl, ?_⟩
    intro y _ hy_afford
    have hend : exPrice ⬝ᵥ exLinEcon.endowment 1 = 1 := exEndow_dot1
    rw [exPrice_dot, hend] at hy_afford
    show y 0 + y 1 ≤ exAlloc 1 0 + exAlloc 1 1
    rw [exAlloc_val1]
    exact hy_afford

theorem exLin_isPareto : exLinEcon.IsParetoEfficient exAlloc :=
  ExchangeEconomy.isParetoEfficient_of_isWalrasianEquilibrium
    exLinEcon exLin_locallyNonsatiated exLin_isWalrasian

def exSatEcon : ExchangeEconomy (Fin 2) (Fin 2) where
  endowment := exEndow
  utility := fun i y => if i = 0 then 0 else y 0 + y 1

theorem exSat_util0 (y : Fin 2 → ℝ) : exSatEcon.utility 0 y = 0 := by simp [exSatEcon]

theorem exSat_util1 (y : Fin 2 → ℝ) : exSatEcon.utility 1 y = y 0 + y 1 := by
  simp [exSatEcon]

theorem exSat_isWalrasian : exSatEcon.IsWalrasianEquilibrium exPrice exAlloc := by
  have hfeas : exSatEcon.IsFeasible exAlloc := exAlloc_feasible
  refine ⟨exPrice_nonneg, hfeas, ?_⟩
  rw [Fin.forall_fin_two]
  constructor
  · refine ⟨le_rfl, ?_⟩
    intro y _ _
    simp only [exSat_util0]
    exact le_rfl
  · refine ⟨le_rfl, ?_⟩
    intro y _ hy_afford
    have hend : exPrice ⬝ᵥ exSatEcon.endowment 1 = 1 := exEndow_dot1
    rw [exPrice_dot, hend] at hy_afford
    simp only [exSat_util1, exAlloc_val1]
    exact hy_afford

def exSatWit : Fin 2 → Fin 2 → ℝ := fun i _ => if i = 0 then 0 else 1

theorem exSatWit_val1 : exSatWit 1 0 + exSatWit 1 1 = 2 := by norm_num [exSatWit]

theorem exSat_notPareto : ¬ exSatEcon.IsParetoEfficient exAlloc := by
  have hfeasW : exSatEcon.IsFeasible exSatWit := by
    constructor
    · intro i
      fin_cases i <;> intro l <;> fin_cases l <;>
        norm_num [exSatWit, exFin01, exFin10]
    · intro l
      fin_cases l <;>
        norm_num [exSatWit, exSatEcon, exEndow, exFin01, exFin10, Fin.sum_univ_two]
  have hgeW :
      ∀ i, exSatEcon.utility i (exAlloc i) ≤ exSatEcon.utility i (exSatWit i) := by
    rw [Fin.forall_fin_two]
    constructor
    · simp [exSatEcon]
    · simp only [exSat_util1, exAlloc_val1, exSatWit_val1]
      exact one_le_two
  have hltW :
      exSatEcon.utility 1 (exAlloc 1) < exSatEcon.utility 1 (exSatWit 1) := by
    simp only [exSat_util1, exAlloc_val1, exSatWit_val1]
    exact one_lt_two
  intro h
  exact h.2 ⟨exSatWit, hfeasW, hgeW, 1, hltW⟩

end Examples

#print axioms MathlibExt.Economics.ExchangeEconomy.isParetoEfficient_of_isWalrasianEquilibrium

end MathlibExtTest.Economics.FirstWelfare
