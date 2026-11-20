/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.RevealedPreference.GARP
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open MathlibExt.Economics.RevealedPreference

namespace MathlibExtTest.Economics.RevealedPreference.GARP

/-- Two goods, two observations: each chosen bundle was strictly cheaper than the other at the
other observation's prices, a two-cycle GARP violation. -/
def twoCycle : DemandData (Fin 2) (Fin 2) where
  price := ![![2, 1], ![1, 2]]
  bundle := ![![1, 0], ![0, 1]]

theorem twoCycle_not_garp : ¬ twoCycle.GARP := by
  intro hG
  have hR : twoCycle.RevealedPreferred 0 1 :=
    Relation.TransGen.single (by
      simp [DemandData.DirectlyRevealedPreferred, dotProduct, Fin.sum_univ_two, twoCycle])
  have hP : twoCycle.StrictlyDirectlyRevealedPreferred 1 0 := by
    simp [DemandData.StrictlyDirectlyRevealedPreferred, dotProduct, Fin.sum_univ_two, twoCycle]
  exact hG 0 1 hR hP

theorem twoCycle_not_rationalizes (u : (Fin 2 → ℝ) → ℝ) (hu : LocallyNonsatiated u) :
    ¬ twoCycle.Rationalizes u := by
  intro hD
  exact twoCycle_not_garp (DemandData.garp_of_rationalizes twoCycle hu hD)

/-- Three goods, three observations: `R⁰` cycles `0 → 1 → 2 → 0` with `x¹ P⁰ x²` and
`x² P⁰ x⁰`, yet no pair of observations violates GARP on its own. -/
def threeCycle : DemandData (Fin 3) (Fin 3) where
  price := ![![3, 1, 2], ![1, 1, 3], ![2, 2, 1]]
  bundle := ![![0, 0, 2], ![0, 2, 1], ![2, 0, 0]]

theorem threeCycle_pairwise (i j : Fin 3) (h : threeCycle.DirectlyRevealedPreferred i j) :
    ¬ threeCycle.StrictlyDirectlyRevealedPreferred j i := by
  fin_cases i <;> fin_cases j <;> revert h <;>
    norm_num [DemandData.DirectlyRevealedPreferred,
      DemandData.StrictlyDirectlyRevealedPreferred, dotProduct, Fin.sum_univ_three, threeCycle]

theorem threeCycle_not_garp : ¬ threeCycle.GARP := by
  intro hG
  have h01 : threeCycle.DirectlyRevealedPreferred 0 1 := by
    norm_num [DemandData.DirectlyRevealedPreferred, dotProduct, Fin.sum_univ_three, threeCycle]
  have h12 : threeCycle.DirectlyRevealedPreferred 1 2 := by
    norm_num [DemandData.DirectlyRevealedPreferred, dotProduct, Fin.sum_univ_three, threeCycle]
  have hR : threeCycle.RevealedPreferred 0 2 :=
    Relation.TransGen.tail (Relation.TransGen.single h01) h12
  have hP : threeCycle.StrictlyDirectlyRevealedPreferred 2 0 := by
    norm_num [DemandData.StrictlyDirectlyRevealedPreferred, dotProduct, Fin.sum_univ_three,
      threeCycle]
  exact hG 0 2 hR hP

/-- Two observations at the same prices with tied expenditure: each bundle is directly revealed
preferred to the other, with no strict comparison. -/
def ties : DemandData (Fin 2) (Fin 2) where
  price := ![![1, 1], ![1, 1]]
  bundle := ![![1, 0], ![0, 1]]

theorem ties_directlyRevealedPreferred :
    ties.DirectlyRevealedPreferred 0 1 ∧ ties.DirectlyRevealedPreferred 1 0 := by
  constructor <;>
    simp [DemandData.DirectlyRevealedPreferred, dotProduct, Fin.sum_univ_two, ties]

theorem ties_not_strictlyDirectlyRevealedPreferred (i j : Fin 2) :
    ¬ ties.StrictlyDirectlyRevealedPreferred i j := by
  fin_cases i <;> fin_cases j <;>
    simp [DemandData.StrictlyDirectlyRevealedPreferred, dotProduct, Fin.sum_univ_two, ties]

theorem sum_locallyNonsatiated : LocallyNonsatiated (fun y : Fin 2 → ℝ => y 0 + y 1) := by
  intro y ε hε
  use fun k => y k + ε / 2
  constructor
  · have hle : dist (fun k => y k + ε / 2) y ≤ ε / 2 := by
      rw [dist_pi_le_iff (by linarith : (0:ℝ) ≤ ε / 2)]
      intro b
      rw [Real.dist_eq]
      have : (y b + ε / 2 - y b) = ε / 2 := by ring
      rw [this]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ε / 2)]
    have hlt : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt hle hlt
  · simp only
    linarith

theorem ties_rationalizes : ties.Rationalizes (fun y => y 0 + y 1) := by
  intro i y h
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_two, ties] at h ⊢ <;> linarith

theorem ties_garp : ties.GARP := by
  exact DemandData.garp_of_rationalizes ties sum_locallyNonsatiated ties_rationalizes

end MathlibExtTest.Economics.RevealedPreference.GARP
