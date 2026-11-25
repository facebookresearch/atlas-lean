/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.ACVoltageCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix
open PhyslibExt.Circuits.CurrentLimitedACLift
open PhyslibExt.Circuits.ACVoltageCertificate

namespace PhyslibExtTest.Circuits.ACVoltageCertificate

/-! ### Exact two-bus certificate: bound `3/2` attained at `V = (2, 5/4)` -/

/-- The certified bound of the two-bus certificate is `3/2`. -/
example : certifiedLowerBound 2 1 1 twoBusCertExample twoBusCertificate = 3 / 2 :=
  twoBus_certificate_exact.2.2.2.2

/-- The dual slack of the certificate is the explicit rank-one matrix
`[[25/16, -5/2], [-5/2, 4]] = F Fᴴ` with `F = (5/4, -2)ᵀ`. -/
example : dualSlack 2 1 1 twoBusCertExample twoBusCertificate =
    !![25 / 16, -5 / 2; -5 / 2, 4] := by
  rw [twoBus_certificate_exact.2.1]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [twoBusCertificate, Matrix.mul_apply] <;> norm_num

/-- The certified voltage `(2, 5/4)` is AC feasible and costs exactly the bound. -/
example : acFeasible 2 1 twoBusCertExample ![2, 5 / 4] ∧
    acCost 2 1 twoBusCertExample ![2, 5 / 4] =
      certifiedLowerBound 2 1 1 twoBusCertExample twoBusCertificate := by
  obtain ⟨-, -, hfeas, hcost, hbound⟩ := twoBus_certificate_exact
  exact ⟨hfeas, by rw [hbound]; exact hcost⟩

/-- Headline on the fixture: every AC-feasible voltage costs at least `3/2`. -/
example (V : Fin 2 → ℂ) (hV : acFeasible 2 1 twoBusCertExample V) :
    3 / 2 ≤ acCost 2 1 twoBusCertExample V := by
  obtain ⟨hnonneg, hfactor, -, -, hbound⟩ := twoBus_certificate_exact
  rw [← hbound]
  exact (acVoltageCertificate_correct 2 1 1 twoBusCertExample twoBusCertificate hnonneg
    hfactor).2.1 V hV

/-- Headline on the fixture: every relaxation-feasible matrix costs at least `3/2`. -/
example (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : sdpFeasible 2 1 twoBusCertExample W) :
    3 / 2 ≤ sdpCost 2 1 twoBusCertExample W := by
  obtain ⟨hnonneg, hfactor, -, -, hbound⟩ := twoBus_certificate_exact
  rw [← hbound]
  exact (acVoltageCertificate_correct 2 1 1 twoBusCertExample twoBusCertificate hnonneg
    hfactor).1 W hW

/-- Optimality by equality: the lift of `(2, 5/4)` minimizes the relaxation. -/
example (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : sdpFeasible 2 1 twoBusCertExample W) :
    sdpCost 2 1 twoBusCertExample (voltageLift 2 twoBusOptimalVoltage) ≤
      sdpCost 2 1 twoBusCertExample W := by
  obtain ⟨hnonneg, hfactor, hfeas, hcost, hbound⟩ := twoBus_certificate_exact
  exact (acOptimal_of_acCost_eq_certifiedLowerBound 2 1 1 twoBusCertExample
    twoBusCertificate hnonneg hfactor twoBusOptimalVoltage hfeas (hcost.trans hbound.symm)).2
    W hW

/-- Global optimum: no AC-feasible voltage beats `(2, 5/4)`. -/
example (V : Fin 2 → ℂ) (hV : acFeasible 2 1 twoBusCertExample V) :
    acCost 2 1 twoBusCertExample twoBusOptimalVoltage ≤ acCost 2 1 twoBusCertExample V :=
  twoBus_globalOptimum V hV

/-! ### Non-certificate point 1: a relaxed point that is not a lift -/

/-- The relaxed point is feasible for the relaxation, is the lift of no voltage, and costs
`2`. -/
example : sdpFeasible 2 1 twoBusCertExample twoBusRelaxedPoint ∧
    (∀ V : Fin 2 → ℂ, voltageLift 2 V ≠ twoBusRelaxedPoint) ∧
    sdpCost 2 1 twoBusCertExample twoBusRelaxedPoint = 2 :=
  ⟨twoBus_relaxedPoint_not_lift.1, twoBus_relaxedPoint_not_lift.2.1,
    twoBus_relaxedPoint_not_lift.2.2.1⟩

/-- The certificate bounds the relaxed point through the headline, with a strict gap, and
no voltage is recovered from it. -/
example : certifiedLowerBound 2 1 1 twoBusCertExample twoBusCertificate <
    sdpCost 2 1 twoBusCertExample twoBusRelaxedPoint ∧
    3 / 2 ≤ sdpCost 2 1 twoBusCertExample twoBusRelaxedPoint := by
  obtain ⟨hnonneg, hfactor, -, -, hbound⟩ := twoBus_certificate_exact
  have h := (acVoltageCertificate_correct 2 1 1 twoBusCertExample twoBusCertificate hnonneg
    hfactor).1 _ twoBus_relaxedPoint_not_lift.1
  exact ⟨twoBus_relaxedPoint_not_lift.2.2.2, hbound ▸ h⟩

/-! ### Non-certificate point 2: a stationary point that is not a certificate -/

/-- The stationary voltage `(2, 3/4)` is AC feasible and costs `5/2`. -/
example : acFeasible 2 1 twoBusCertExample twoBusStationaryVoltage ∧
    acCost 2 1 twoBusCertExample twoBusStationaryVoltage = 5 / 2 :=
  ⟨twoBus_stationaryPoint_not_certificate.1, twoBus_stationaryPoint_not_certificate.2.2.1⟩

/-- The stationarity multipliers fail the sign check, and their dual slack has no
factorization `F Fᴴ` of width `1` or of width `2`. -/
example : ¬ twoBusStationaryMultipliers.Nonneg ∧
    (∀ F : Matrix (Fin 2) (Fin 1) ℂ,
      dualSlack 2 1 1 twoBusCertExample twoBusStationaryMultipliers ≠ F * Fᴴ) ∧
    ∀ F : Matrix (Fin 2) (Fin 2) ℂ,
      dualSlack 2 1 1 twoBusCertExample twoBusStationaryMultipliers ≠ F * Fᴴ :=
  ⟨twoBus_stationaryPoint_not_certificate.2.2.2.2.1,
    twoBus_stationaryPoint_not_certificate.2.2.2.2.2.1 1,
    twoBus_stationaryPoint_not_certificate.2.2.2.2.2.1 2⟩

/-- The would-be bound `5/2` of the stationary multipliers is not a lower bound on the AC
cost: the certified voltage `(2, 5/4)` costs less. -/
example : ¬ ∀ V : Fin 2 → ℂ, acFeasible 2 1 twoBusCertExample V →
    certifiedLowerBound 2 1 1 twoBusCertExample twoBusStationaryMultipliers ≤
      acCost 2 1 twoBusCertExample V := by
  intro h
  have hle := h _ twoBus_certificate_exact.2.2.1
  have hlt := twoBus_stationaryPoint_not_certificate.2.2.2.2.2.2
  linarith

/-- The stationary voltage is not optimal: it costs `5/2`, the certified optimum `3/2`. -/
example : acCost 2 1 twoBusCertExample twoBusOptimalVoltage <
    acCost 2 1 twoBusCertExample twoBusStationaryVoltage := by
  rw [twoBus_certificate_exact.2.2.2.1, twoBus_stationaryPoint_not_certificate.2.2.1]
  norm_num

end PhyslibExtTest.Circuits.ACVoltageCertificate
