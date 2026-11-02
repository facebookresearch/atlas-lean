/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.StripCases
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.StripCases`

* `rsc_pigeonhole_cover`, `rsc_strip_cases`, `rsc_strip_dichotomy` and `rsc_dichotomy_cases`
  for a Dirac measure on `Bool` with all events equal to `univ` (resp. `H = ∅`), where every
  hypothesis holds.
-/

@[expose] public section

open MeasureTheory StatMech.RSW.StripCases

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.StripCases

example : ∃ i ∈ Finset.range 3, (1 : ℝ) / ((Finset.range 3).card : ℝ)
    ≤ (Measure.dirac true).real ((fun _ : ℕ => (Set.univ : Set Bool)) i) :=
  rsc_pigeonhole_cover (Measure.dirac true) (Finset.range 3) (fun _ => Set.univ)
    (Ev := Set.univ) (by simp) (by intro x _; simpa using ⟨0, by norm_num⟩) (by decide)

example : (1 : ℝ) / 3 ≤ (Measure.dirac true).real (Set.univ : Set Bool) ∨
    (1 : ℝ) / 3 ≤ (Measure.dirac true).real (Set.univ : Set Bool) :=
  rsc_strip_cases (Measure.dirac true) Set.univ Set.univ Set.univ Set.univ (by simp)
    (by simp) rfl

example : (1 / 2 ≤ (Measure.dirac true).real (∅ : Set Bool)) ∨
    (∃ i ∈ Finset.range (18 * 1), (1 : ℝ) / (36 * ((1 : ℕ) : ℝ))
      ≤ (Measure.dirac true).real ((fun _ : ℕ => (Set.univ : Set Bool)) i)) :=
  rsc_strip_dichotomy (Measure.dirac true) le_rfl ∅ Set.univ (fun _ => Set.univ)
    (fun _ => by norm_num) (by intro x _; simpa using ⟨0, by norm_num⟩)

example : ∃ i ∈ Finset.range (18 * 1),
    ((1 : ℝ) / (108 * ((1 : ℕ) : ℝ)) ≤ (Measure.dirac true).real ((fun _ : ℕ => (Set.univ : Set Bool)) i)) ∨
      ((1 : ℝ) / (108 * ((1 : ℕ) : ℝ)) ≤ (Measure.dirac true).real ((fun _ : ℕ => (Set.univ : Set Bool)) i)) :=
  rsc_dichotomy_cases (Measure.dirac true) le_rfl ∅ Set.univ (fun _ => Set.univ)
    (fun _ => Set.univ) (fun _ => Set.univ) (fun _ => Set.univ) (by simp)
    (fun _ => by norm_num) (by intro x _; simpa using ⟨0, by norm_num⟩) (fun _ => by simp) (fun _ => rfl)

end MathlibExtTest.StatMech.Probability.Percolation.RSW.StripCases
