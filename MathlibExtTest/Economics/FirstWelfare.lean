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

/-! Examples for `MathlibExt.Economics.FirstWelfare`: a two-agent, two-good exchange economy
with linear utilities whose endowment allocation is a Walrasian equilibrium and hence Pareto
efficient, a satiated variant whose equilibrium is not Pareto efficient, and a zero-price
regression: the zero price vector satisfies every other equilibrium clause in a one-agent,
one-good economy but is not a Walrasian equilibrium. -/

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

theorem exPrice_ne_zero : exPrice ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [exPrice] at h0

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

theorem exLin_locallyNonsatiated :
    ∀ i, SecondWelfareTheorem.LocallyNonsatiated (exLinEcon.utility i) := by
  intro i x hx ε hε
  refine ⟨fun l => x l + ε / 2, ?_, ?_, ?_⟩
  · intro l
    show 0 ≤ x l + ε / 2
    have hxl : 0 ≤ x l := hx l
    linarith
  · rw [dist_pi_lt_iff hε]
    intro l
    show dist (x l + ε / 2) (x l) < ε
    rw [Real.dist_eq]
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
  refine ⟨exPrice_nonneg, exPrice_ne_zero, exAlloc_feasible, fun _ _ => rfl, ?_⟩
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
  refine ⟨exPrice_nonneg, exPrice_ne_zero, hfeas, fun _ _ => rfl, ?_⟩
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

/-- One agent, one good, zero endowment and constant utility. -/
def exZeroEcon : ExchangeEconomy Unit Unit where
  endowment := fun _ _ => 0
  utility := fun _ _ => 0

/-- At the zero price vector, the zero allocation meets every clause of
`IsWalrasianEquilibrium` except `p ≠ 0`. -/
theorem exZero_otherClauses :
    (0 : Unit → ℝ) ≤ 0 ∧ exZeroEcon.IsFeasible 0 ∧
      (∀ l : Unit, 0 < (0 : Unit → ℝ) l →
        (∑ i : Unit, (0 : Unit → Unit → ℝ) i) l = (∑ i, exZeroEcon.endowment i) l) ∧
      ∀ i, (0 : Unit → ℝ) ⬝ᵥ (0 : Unit → Unit → ℝ) i ≤ (0 : Unit → ℝ) ⬝ᵥ exZeroEcon.endowment i ∧
        ∀ y : Unit → ℝ, 0 ≤ y → (0 : Unit → ℝ) ⬝ᵥ y ≤ (0 : Unit → ℝ) ⬝ᵥ exZeroEcon.endowment i →
          exZeroEcon.utility i y ≤ exZeroEcon.utility i ((0 : Unit → Unit → ℝ) i) := by
  refine ⟨le_rfl, ⟨fun _ => le_rfl, ?_⟩, fun _ h => (lt_irrefl _ h).elim,
    fun _ => ⟨?_, fun _ _ _ => le_rfl⟩⟩
  · intro l
    simp [exZeroEcon]
  · simp

/-- Regression: the zero price vector is not a Walrasian equilibrium. -/
theorem exZero_not_isWalrasian : ¬ exZeroEcon.IsWalrasianEquilibrium 0 0 :=
  fun h => h.2.1 rfl

/-- One agent can leave an endowed good unsold without losing utility. -/
def exSlackEcon : ExchangeEconomy Unit Unit where
  endowment := fun _ _ => 1
  utility := fun _ _ => 0

/-- The unsold-good counterexample satisfies every clause except market clearing. -/
theorem exSlack_otherClauses :
    0 ≤ (1 : Unit → ℝ) ∧ (1 : Unit → ℝ) ≠ 0 ∧ exSlackEcon.IsFeasible 0 ∧
      ∀ i, (1 : Unit → ℝ) ⬝ᵥ (0 : Unit → Unit → ℝ) i ≤
          (1 : Unit → ℝ) ⬝ᵥ exSlackEcon.endowment i ∧
        ∀ y : Unit → ℝ, 0 ≤ y →
          (1 : Unit → ℝ) ⬝ᵥ y ≤ (1 : Unit → ℝ) ⬝ᵥ exSlackEcon.endowment i →
          exSlackEcon.utility i y ≤ exSlackEcon.utility i (0 : Unit → ℝ) := by
  norm_num [exSlackEcon, ExchangeEconomy.IsFeasible, Pi.le_def, dotProduct]

/-- Positive-price excess supply is not a Walrasian equilibrium. -/
theorem exSlack_not_isWalrasian : ¬ exSlackEcon.IsWalrasianEquilibrium 1 0 := by
  intro h
  have hclear := h.2.2.2.1 () (by norm_num)
  norm_num [exSlackEcon] at hclear

end Examples

#print axioms MathlibExt.Economics.ExchangeEconomy.isParetoEfficient_of_isWalrasianEquilibrium

end MathlibExtTest.Economics.FirstWelfare
