/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.RevealedPreference.Afriat
import Mathlib.Tactic.Linarith

@[expose] public section

open MathlibExt.Economics.RevealedPreference

namespace MathlibExtTest.Economics.RevealedPreference.Afriat

/-- Two observations at the same prices with tied expenditure (GARP holds with `R` in both
directions). -/
def ties : DemandData (Fin 2) (Fin 2) where
  price := ![![1, 1], ![1, 1]]
  bundle := ![![1, 0], ![0, 1]]

theorem ties_garp : ties.GARP := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [ties, DemandData.StrictlyDirectlyRevealedPreferred, dotProduct, Fin.sum_univ_two]

theorem ties_exists_certificate : ∃ U lam : Fin 2 → ℝ, ties.IsAfriatCertificate U lam := by
  exact DemandData.exists_isAfriatCertificate_of_garp ties_garp

/-- A two-cycle GARP violation: `p⁰·x⁰ = 2 > p⁰·x¹ = 1` and `p¹·x¹ = 2 > p¹·x⁰ = 1`. -/
def twoCycle : DemandData (Fin 2) (Fin 2) where
  price := ![![2, 1], ![1, 2]]
  bundle := ![![1, 0], ![0, 1]]

/-- The two-cycle has no Afriat certificate: the inequalities force `U⁰ < U¹ < U⁰`. -/
theorem twoCycle_no_certificate (U lam : Fin 2 → ℝ) : ¬ twoCycle.IsAfriatCertificate U lam := by
  rintro ⟨hpos, hineq⟩
  have h01 := hineq 0 1
  have h10 := hineq 1 0
  simp [twoCycle, dotProduct, Fin.sum_univ_two] at h01 h10
  have hp0 := hpos 0
  have hp1 := hpos 1
  linarith

/-- Three goods, three observations whose expenditure matrix `pⁱ·xʲ` has rows `[4, 4, 6]`,
`[6, 5, 2]`, `[2, 5, 4]`: a GARP violation through a three-cycle only. -/
def threeCycle : DemandData (Fin 3) (Fin 3) where
  price := ![![3, 1, 2], ![1, 1, 3], ![2, 2, 1]]
  bundle := ![![0, 0, 2], ![0, 2, 1], ![2, 0, 0]]

/-- The three-cycle has no Afriat certificate: the inequalities force `U⁰ < U² < U¹ ≤ U⁰`. -/
theorem threeCycle_no_certificate (U lam : Fin 3 → ℝ) :
    ¬ threeCycle.IsAfriatCertificate U lam := by
  rintro ⟨hpos, hineq⟩
  have h10 := hineq 1 0
  have h21 := hineq 2 1
  have h02 := hineq 0 2
  simp [threeCycle, dotProduct, Fin.sum_univ_three] at h10 h21 h02
  have hp0 := hpos 0
  have hp1 := hpos 1
  have hp2 := hpos 2
  linarith

end MathlibExtTest.Economics.RevealedPreference.Afriat
