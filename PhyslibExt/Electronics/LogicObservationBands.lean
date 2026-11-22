/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Logic observation bands

## i. Overview

A physical observation relation for digital voltage bands: with
thresholds `Vil < Vih`, a voltage is observed low when `v <= Vil`
and high when `v >= Vih`; voltages strictly between the thresholds
are invalid/unknown (`none`) and are not coerced to a Boolean value.
If an ideal output voltage is promised low (`<= Vol`, `Vol < Vil`)
or high (`>= Voh`, `Voh > Vih`), then additive noise smaller in
absolute value than both noise margins (`Vil - Vol` and
`Voh - Vih`) preserves the Boolean observation of the expected
output bit. No gate function is modeled: the promise hypothesis
states directly that the ideal output voltage encodes the expected
output bit. Nothing here is a transistor, cell or netlist claim.

## ii. Key results

- `observe_eq_false_of_le`, `observe_eq_true_of_le`,
  `observe_eq_none_iff`, `observe_eq_some_iff`: the threshold
  characterization of the three-valued observation, with the
  invalid band mapped to `none`.
- `observe_noisy_low`, `observe_noisy_high`: one-sided noise
  preservation below the respective margin.
- `observe_noisy_output`: the composed output-observation
  contract for both Boolean values.

## iii. Table of contents

- A. Voltage band observation

## iv. References

- N. H. E. Weste and D. M. Harris, *CMOS VLSI Design: A Circuits
  and Systems Perspective*, fourth edition, Addison-Wesley, 2011:
  logic input/output voltage levels `Vil`, `Vih`, `Vol`, `Voh` and
  the noise margins formed from them.

## A. Voltage band observation
-/

@[expose] public section

namespace PhyslibExt.Electronics.LogicObservationBands

/-- The physical observation of a voltage: `some false` for low,
`some true` for high, and `none` inside the invalid band
`(Vil, Vih)`. At the thresholds themselves the observation is the
corresponding Boolean value. -/
noncomputable def observe (Vil Vih v : ℝ) : Option Bool :=
  if v <= Vil then some false
  else if Vih <= v then some true
  else none

/-- A voltage at or below the low threshold is observed low. -/
lemma observe_eq_false_of_le {Vil v : ℝ} (hv : v <= Vil) (Vih : ℝ) :
    observe Vil Vih v = some false := by
  unfold observe
  simp [hv]

/-- A voltage at or above the high threshold is observed high. -/
lemma observe_eq_true_of_le {Vil Vih v : ℝ} (hVilVih : Vil < Vih)
    (hv : Vih <= v) :
    observe Vil Vih v = some true := by
  have h : ¬ v <= Vil := by linarith
  unfold observe
  simp [h, hv]

/-- The observation is invalid exactly on the open gap band. -/
lemma observe_eq_none_iff {Vil Vih v : ℝ} (hVilVih : Vil < Vih) :
    observe Vil Vih v = none ↔ Vil < v ∧ v < Vih := by
  by_cases h1 : v <= Vil
  · rw [observe_eq_false_of_le h1 Vih]
    constructor
    · intro h
      simp at h
    · intro h
      linarith [h.1]
  · by_cases h2 : Vih <= v
    · rw [observe_eq_true_of_le hVilVih h2]
      constructor
      · intro h
        simp at h
      · intro h
        linarith [h.2]
    · have ho : observe Vil Vih v = none := by simp [observe, h1, h2]
      rw [ho]
      rw [not_le] at h1 h2
      constructor
      · intro _
        exact ⟨h1, h2⟩
      · intro _
        rfl

/-- The observation, when defined, agrees with the two threshold
predicates and with no other Boolean value. -/
lemma observe_eq_some_iff {Vil Vih v : ℝ} (hVilVih : Vil < Vih) (b : Bool) :
    observe Vil Vih v = some b ↔ (b = false ∧ v <= Vil) ∨ (b = true ∧ Vih <= v) := by
  by_cases h1 : v <= Vil
  · rw [observe_eq_false_of_le h1 Vih]
    constructor
    · intro h
      cases b
      · exact Or.inl ⟨rfl, h1⟩
      · simp at h
    · intro h
      rcases h with ⟨rfl, -⟩ | ⟨rfl, hle⟩
      · rfl
      · have : False := by linarith
        exact this.elim
  · by_cases h2 : Vih <= v
    · rw [observe_eq_true_of_le hVilVih h2]
      constructor
      · intro h
        cases b
        · simp at h
        · exact Or.inr ⟨rfl, h2⟩
      · intro h
        rcases h with ⟨rfl, hle⟩ | ⟨rfl, -⟩
        · exact absurd hle h1
        · rfl
    · have ho : observe Vil Vih v = none := by simp [observe, h1, h2]
      rw [ho]
      constructor
      · intro h
        simp at h
      · intro h
        rcases h with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
        · exact absurd hle h1
        · exact absurd hle h2

/-- Low-side noise preservation: a promised low output `y <= Vol`,
perturbed by noise of absolute value below the low margin `Vil - Vol`,
is still observed low. -/
lemma observe_noisy_low {Vol Vil Vih y e : ℝ} (hVol : Vol < Vil)
    (hy : y <= Vol) (he : |e| < Vil - Vol) :
    observe Vil Vih (y + e) = some false := by
  apply observe_eq_false_of_le
  have _hpos : 0 < Vil - Vol := by linarith
  have he' : e ≤ |e| := le_abs_self e
  linarith

/-- High-side noise preservation: a promised high output `y >= Voh`,
perturbed by noise of absolute value below the high margin
`Voh - Vih`, is still observed high. -/
lemma observe_noisy_high {Voh Vil Vih y e : ℝ} (hVilVih : Vil < Vih)
    (hVoh : Vih < Voh) (hy : Voh <= y) (he : |e| < Voh - Vih) :
    observe Vil Vih (y + e) = some true := by
  refine observe_eq_true_of_le hVilVih ?_
  have _hpos : 0 < Voh - Vih := by linarith
  have he' : -(Voh - Vih) < e := (abs_lt.mp he).1
  linarith

/-- The output-observation contract: if a gate's ideal output voltage
is promised low (`<= Vol`) when its expected output bit is `false` and
high (`>= Voh`) when its expected output bit is `true`, with
`Vol < Vil < Vih < Voh`, then additive noise below both margins makes
the physical observation of the noisy output equal that expected
output bit. No gate function is modeled: the premise `hy` says directly
that the ideal output voltage encodes the expected output bit. Here
the two margins are `Vil - Vol` and `Voh - Vih`. -/
lemma observe_noisy_output {Vol Vil Vih Voh : ℝ} (hVol : Vol < Vil)
    (hVilVih : Vil < Vih) (hVoh : Vih < Voh) (b : Bool) (y e : ℝ)
    (hy : (b = false ∧ y <= Vol) ∨ (b = true ∧ Voh <= y))
    (he : |e| < min (Vil - Vol) (Voh - Vih)) :
    observe Vil Vih (y + e) = some b := by
  rcases hy with ⟨rfl, hy⟩ | ⟨rfl, hy⟩
  · exact observe_noisy_low hVol hy (lt_of_lt_of_le he (min_le_left _ _))
  · exact observe_noisy_high hVilVih hVoh hy (lt_of_lt_of_le he (min_le_right _ _))

end PhyslibExt.Electronics.LogicObservationBands
