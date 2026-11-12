/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.Typical.AEP

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open InformationTheory

/-- The fair bit: the uniform law on `Fin 2`. -/
noncomputable def fairBit : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [Fin.sum_univ_two]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- A nonuniform two-point law: `3/4` on `0`, `1/4` on `1`. -/
noncomputable def threeQuarterBit : PMF (Fin 2) :=
  PMF.ofFintype (fun a => if a = 0 then ENNReal.ofReal (3 / 4) else ENNReal.ofReal (1 / 4))
    (by
      have h1 : (1 : Fin 2) ≠ 0 := by decide
      rw [Fin.sum_univ_two]
      simp only [ite_true, h1, ite_false]
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num)

/-- The fair bit has probability `1/2` at every outcome. -/
theorem fairBit_apply (a : Fin 2) : (fairBit a).toReal = 1 / 2 := by
  simp [fairBit, PMF.ofFintype_apply]

/-- The nonuniform law has probability `3/4` at `0` and `1/4` at `1`. -/
theorem threeQuarterBit_apply_zero : (threeQuarterBit 0).toReal = 3 / 4 := by
  simp [threeQuarterBit, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 4)]

theorem threeQuarterBit_apply_one : (threeQuarterBit 1).toReal = 1 / 4 := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp [threeQuarterBit, PMF.ofFintype_apply, h1]

/-- Boundary check: the point mass at `0` has entropy `0` in nats. The atom `1`
has probability `0` and contributes `0` by the `0 log 0 = 0` convention, not
`-Real.log 0`. -/
example : shannonEntropyNats (PMF.pure (0 : Fin 2)) = 0 := by
  rw [shannonEntropyNats, Fin.sum_univ_two]
  simp [PMF.pure_apply]

/-- Boundary check: the self-information of the point mass is `0` at both
outcomes: `-Real.log 1 = 0` at `0`, and the zero convention at the
zero-probability atom `1`. -/
example (a : Fin 2) : selfInformationNats (PMF.pure (0 : Fin 2)) a = 0 := by
  fin_cases a <;> simp [selfInformationNats, PMF.pure_apply]

/-- Boundary check: for the point mass, the AEP deviation event is empty for
every `ε > 0`, so its probability is `0`: the bound is `0 ≤ 0`. -/
example (ε : ℝ) (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter
        (fun a => ε < |selfInformationNats (PMF.pure (0 : Fin 2)) a -
          shannonEntropyNats (PMF.pure (0 : Fin 2))|),
        ((PMF.pure (0 : Fin 2)) a).toReal) = 0 := by
  have hent : shannonEntropyNats (PMF.pure (0 : Fin 2)) = 0 := by
    rw [shannonEntropyNats, Fin.sum_univ_two]
    simp [PMF.pure_apply]
  have hself : ∀ a : Fin 2, selfInformationNats (PMF.pure (0 : Fin 2)) a = 0 := by
    intro a
    fin_cases a <;> simp [selfInformationNats, PMF.pure_apply]
  have hfilter : Finset.univ.filter
      (fun a => ε < |selfInformationNats (PMF.pure (0 : Fin 2)) a -
        shannonEntropyNats (PMF.pure (0 : Fin 2))|) = ∅ := by
    apply Finset.filter_false_of_mem
    intro a _
    rw [hself a, hent]
    simp only [sub_zero, abs_zero]
    exact not_lt.mpr hε.le
  rw [hfilter]
  simp

/-- The fair bit has entropy `Real.log 2` in nats. -/
example : shannonEntropyNats fairBit = Real.log 2 := by
  rw [shannonEntropyNats, Fin.sum_univ_two, fairBit_apply, fairBit_apply]
  simp [Real.negMulLog]
  ring

/-- The fair bit has self-information `Real.log 2` at every outcome, so its
deviation from the entropy is `0` and the AEP bound is `0 ≤ 0` for every
`ε > 0`. -/
example (ε : ℝ) (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter
        (fun a => ε < |selfInformationNats fairBit a - shannonEntropyNats fairBit|),
        (fairBit a).toReal) = 0 := by
  have hent : shannonEntropyNats fairBit = Real.log 2 := by
    rw [shannonEntropyNats, Fin.sum_univ_two, fairBit_apply, fairBit_apply]
    simp [Real.negMulLog]
    ring
  have hself : ∀ a : Fin 2, selfInformationNats fairBit a = Real.log 2 := by
    intro a
    simp [selfInformationNats, fairBit_apply]
  have hfilter : Finset.univ.filter
      (fun a => ε < |selfInformationNats fairBit a - shannonEntropyNats fairBit|) = ∅ := by
    apply Finset.filter_false_of_mem
    intro a _
    rw [hself a, hent]
    simp only [sub_self, abs_zero]
    exact not_lt.mpr hε.le
  rw [hfilter]
  simp

/-- The nonuniform law has entropy `-(3/4 * log (3/4) + 1/4 * log (1/4))` in nats. -/
example : shannonEntropyNats threeQuarterBit =
    -(3 / 4 * Real.log (3 / 4) + 1 / 4 * Real.log (1 / 4)) := by
  rw [shannonEntropyNats, Fin.sum_univ_two, threeQuarterBit_apply_zero,
    threeQuarterBit_apply_one]
  simp [Real.negMulLog]
  ring

/-- The nonuniform law has self-informations `-Real.log (3/4)` and
`-Real.log (1/4)`. -/
example : selfInformationNats threeQuarterBit 0 = -Real.log (3 / 4) := by
  simp [selfInformationNats, threeQuarterBit_apply_zero]

example : selfInformationNats threeQuarterBit 1 = -Real.log (1 / 4) := by
  simp [selfInformationNats, threeQuarterBit_apply_one]

/-- The AEP estimate instantiates for the concrete nonuniform law at `ε = 1/2`:
the deviation probability is at most the self-information variance over
`(1/2)^2`. -/
example :
    (∑ a ∈ Finset.univ.filter
        (fun a => (1 / 2 : ℝ) < |selfInformationNats threeQuarterBit a -
          shannonEntropyNats threeQuarterBit|),
        (threeQuarterBit a).toReal) ≤
      (∑ a, (threeQuarterBit a).toReal *
          (selfInformationNats threeQuarterBit a - shannonEntropyNats threeQuarterBit) ^ 2)
        / (1 / 2 : ℝ) ^ 2 :=
  aep_chebyshev threeQuarterBit (1 / 2) (by norm_num)

/-- Bridge check: the nats entropy of the nonuniform law is the bits entropy
times `Real.log 2`. -/
example : shannonEntropyNats threeQuarterBit =
    shannonEntropy threeQuarterBit * Real.log 2 :=
  shannonEntropyNats_eq_mul_log_two threeQuarterBit
