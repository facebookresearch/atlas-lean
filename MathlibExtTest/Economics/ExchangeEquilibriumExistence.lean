/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExchangeEquilibriumExistence

/-! One consumer, two goods, endowment `(1, 1)`. `E1` has continuous, budget-exhausting demand
that is desirable at zero prices, so a strictly positive price clears both markets (it is
`(1/2, 1/2)`). `E2` has a free-disposal equilibrium at `(1, 0)` but no market-clearing price.
`E3` has budget-exhausting but discontinuous demand and no equilibrium. -/

@[expose] public section

open MathlibExt.Economics.ExchangeEquilibriumExistence

namespace MathlibExtTest.Economics.ExchangeEquilibriumExistence

/-- Test 1 economy: smooth strictly positive excess demand at zero prices. -/
def E1 : ExchangeEconomy (Fin 1) (Fin 2) where
  endowment := fun _ => ![1, 1]
  demand := fun _ p => ![1 + p 1 * (p 1 - p 0), 1 + p 0 * (p 0 - p 1)]

theorem E1_hcont : ∀ i, ContinuousOn (E1.demand i) (priceSimplex (Fin 2)) := by
  intro i
  fin_cases i
  show ContinuousOn
    (fun p : Fin 2 → ℝ => ![1 + p 1 * (p 1 - p 0), 1 + p 0 * (p 0 - p 1)]) _
  rw [continuousOn_pi]
  intro l
  fin_cases l
  · fun_prop
  · fun_prop

theorem E1_hbudget : ∀ i, ∀ p ∈ priceSimplex (Fin 2),
    ∑ l, p l * E1.demand i p l = ∑ l, p l * E1.endowment i l := by
  intro i p _
  fin_cases i
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  show p 0 * E1.demand 0 p 0 + p 1 * E1.demand 0 p 1
    = p 0 * E1.endowment 0 0 + p 1 * E1.endowment 0 1
  simp only [E1]
  simp
  ring

theorem E1_hdes : ∀ p ∈ priceSimplex (Fin 2), ∀ l, p l = 0 → 0 < E1.excessDemand p l := by
  intro p hp l hl
  obtain ⟨_, h1⟩ := hp
  have hsum : p 0 + p 1 = 1 := by
    rw [← Fin.sum_univ_two]
    exact h1
  fin_cases l
  · have hl0 : p 0 = 0 := hl
    have hz : E1.excessDemand p 0 = p 1 * (p 1 - p 0) := by
      simp [E1, ExchangeEconomy.excessDemand]
    have hp1 : p 1 = 1 := by linarith [hsum, hl0]
    show 0 < E1.excessDemand p 0
    rw [hz, hl0, hp1]
    norm_num
  · have hl1 : p 1 = 0 := hl
    have hz : E1.excessDemand p 1 = p 0 * (p 0 - p 1) := by
      simp [E1, ExchangeEconomy.excessDemand]
    have hp0 : p 0 = 1 := by linarith [hsum, hl1]
    show 0 < E1.excessDemand p 1
    rw [hz, hl1, hp0]
    norm_num

theorem E1_exists
    (hB : ∀ g : (Fin 2 → ℝ) → (Fin 2 → ℝ), ContinuousOn g (priceSimplex (Fin 2)) →
      Set.MapsTo g (priceSimplex (Fin 2)) (priceSimplex (Fin 2)) →
      ∃ p ∈ priceSimplex (Fin 2), g p = p) :
    ∃ p ∈ priceSimplex (Fin 2), (∀ l, 0 < p l) ∧ E1.excessDemand p = 0 :=
  ExchangeEconomy.exists_excessDemand_eq_zero_of_brouwer hB E1 E1_hcont E1_hbudget E1_hdes

theorem E1_clears : E1.excessDemand ![1/2, 1/2] = 0 := by
  funext l
  fin_cases l
  · show E1.excessDemand ![1/2, 1/2] 0 = (0 : Fin 2 → ℝ) 0
    simp [E1, ExchangeEconomy.excessDemand]
  · show E1.excessDemand ![1/2, 1/2] 1 = (0 : Fin 2 → ℝ) 1
    simp [E1, ExchangeEconomy.excessDemand]

/-- Test 2 economy: free disposal strictly weaker than market clearing. -/
def E2 : ExchangeEconomy (Fin 1) (Fin 2) where
  endowment := fun _ => ![1, 1]
  demand := fun _ p => ![1 + p 1, 1 - p 0]

theorem E2_equil : E2.IsFreeDisposalEquilibrium ![1, 0] := by
  constructor
  · constructor
    · intro l
      fin_cases l
      · show (0 : ℝ) ≤ (![1, 0] : Fin 2 → ℝ) 0
        simp
      · show (0 : ℝ) ≤ (![1, 0] : Fin 2 → ℝ) 1
        simp
    · show ∑ l, (![1, 0] : Fin 2 → ℝ) l = 1
      rw [Fin.sum_univ_two]
      simp
  · constructor
    · intro l
      fin_cases l
      · show E2.excessDemand ![1, 0] 0 ≤ 0
        simp [E2, ExchangeEconomy.excessDemand]
      · show E2.excessDemand ![1, 0] 1 ≤ 0
        simp [E2, ExchangeEconomy.excessDemand]
    · intro l hlt
      fin_cases l
      · show (![1, 0] : Fin 2 → ℝ) 0 = 0
        have hz : E2.excessDemand ![1, 0] 0 = 0 := by
          simp [E2, ExchangeEconomy.excessDemand]
        have hlt0 : E2.excessDemand ![1, 0] 0 < 0 := hlt
        rw [hz] at hlt0
        norm_num at hlt0
      · show (![1, 0] : Fin 2 → ℝ) 1 = 0
        simp

theorem E2_no_clear : ¬ ∃ p ∈ priceSimplex (Fin 2), E2.excessDemand p = 0 := by
  rintro ⟨p, hp, hz⟩
  obtain ⟨_, h1⟩ := hp
  have hsum : p 0 + p 1 = 1 := by
    rw [← Fin.sum_univ_two]
    exact h1
  have hz0 : E2.excessDemand p 0 = 0 := by
    have h := congrFun hz 0
    simpa using h
  have hz1 : E2.excessDemand p 1 = 0 := by
    have h := congrFun hz 1
    simpa using h
  have e0 : E2.excessDemand p 0 = p 1 := by
    simp [E2, ExchangeEconomy.excessDemand]
  have e1 : E2.excessDemand p 1 = -p 0 := by
    simp [E2, ExchangeEconomy.excessDemand]
  rw [e0] at hz0
  rw [e1] at hz1
  have hp0 : p 0 = 0 := by linarith
  linarith

/-- Test 3 economy: discontinuous demand, budget holds but no equilibrium. -/
noncomputable def E3 : ExchangeEconomy (Fin 1) (Fin 2) where
  endowment := fun _ => ![1, 1]
  demand := fun _ p =>
    letI := Classical.propDecidable (p 0 ≤ 1/2)
    if p 0 ≤ 1/2 then ![1 + p 1, 1 - p 0] else ![1 - p 1, 1 + p 0]

theorem E3_hbudget : ∀ i, ∀ p ∈ priceSimplex (Fin 2),
    ∑ l, p l * E3.demand i p l = ∑ l, p l * E3.endowment i l := by
  intro i p _
  fin_cases i
  by_cases h : p 0 ≤ 1/2
  · rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [E3]
    rw [ite_eq_left h]
    simp
    ring
  · rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [E3]
    rw [ite_eq_right h]
    simp
    ring

theorem E3_no_equil : ¬ ∃ p, E3.IsFreeDisposalEquilibrium p := by
  rintro ⟨p, hp, hz, _⟩
  obtain ⟨h0, h1⟩ := hp
  have hsum : p 0 + p 1 = 1 := by
    rw [← Fin.sum_univ_two]
    exact h1
  by_cases h : p 0 ≤ 1/2
  · have e0 : E3.excessDemand p 0 = p 1 := by
      simp only [E3, ExchangeEconomy.excessDemand]
      rw [ite_eq_left h]
      simp
    have hz0 := hz 0
    rw [e0] at hz0
    have hp1 : p 1 = 0 := le_antisymm hz0 (h0 1)
    have hp0 : p 0 = 1 := by linarith
    linarith
  · have e1 : E3.excessDemand p 1 = p 0 := by
      simp only [E3, ExchangeEconomy.excessDemand]
      rw [ite_eq_right h]
      simp
    have hz1 := hz 1
    rw [e1] at hz1
    have hp0 : p 0 = 0 := le_antisymm hz1 (h0 0)
    linarith

-- Unconditional market clearing for `E1` via `exists_excessDemand_eq_zero`.
example : ∃ p ∈ priceSimplex (Fin 2), (∀ l, 0 < p l) ∧ E1.excessDemand p = 0 := by
  exact ExchangeEconomy.exists_excessDemand_eq_zero E1 E1_hcont E1_hbudget E1_hdes

-- Unconditional free-disposal equilibrium for `E1` via `exists_isFreeDisposalEquilibrium`.
example : ∃ p, E1.IsFreeDisposalEquilibrium p := by
  exact ExchangeEconomy.exists_isFreeDisposalEquilibrium E1 E1_hcont E1_hbudget

end MathlibExtTest.Economics.ExchangeEquilibriumExistence
