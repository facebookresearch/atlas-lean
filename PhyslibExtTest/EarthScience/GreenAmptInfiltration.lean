/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.GreenAmptInfiltration

/-!
# Green-Ampt checks

Consumers of `PhyslibExt.EarthScience.GreenAmptInfiltration`: the
satisfiability witness `K = 1`, `A = 0`, `F(s) = s + 2` on `[0, 1]`,
the public shape of the integrated law, the degenerate case `t = t₀`,
and the `A = 0` reduction of the integrated formula.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
witness profile `F(s) = s + 2` has `F' = 1 = 1 * (1 + 0 / F)` on
`[0, 1]` and `F > 0` there, so the interval hypotheses are jointly
satisfiable.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Satisfiability witness
- B. Shape, degenerate case, and `A = 0` reduction

## iv. References

- `PhyslibExt.EarthScience.GreenAmptInfiltration`
-/

/-- Satisfiability witness: `K = 1`, `A = 0`, `F(s) = s + 2` on
`[0, 1]` gives `1 - 0 = (3 - 2) / 1`. -/
example : (1 : ℝ) - 0 = ((1 + 2) - 2 - 0 * Real.log (((1 + 2) + 0) / (2 + 0))) / 1 := by
  have hFpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, s + 2 > 0 := by
    intro s hs
    have := hs.1
    linarith
  have hode : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => s + 2) (1 * (1 + 0 / (s + 2))) s := by
    intro s _
    have h : HasDerivAt (fun s : ℝ => s + 2) 1 s := by
      simpa using (hasDerivAt_id s).add_const (2 : ℝ)
    convert h using 1
    simp
  have h := EarthScience.green_ampt_integrated (fun s => s + 2) 1 0 2 0 1
    (by norm_num) (le_refl 0) (by norm_num) (by norm_num) hFpos (by norm_num) hode
  exact h

/-- The public statement shape of the integrated Green-Ampt law. -/
example (F : ℝ → ℝ) (K A F₀ t₀ t : ℝ) (hK : 0 < K)
    (hA : 0 ≤ A) (hF₀ : 0 < F₀) (ht : t₀ ≤ t)
    (hFpos : ∀ s ∈ Set.Icc t₀ t, F s > 0)
    (hF₀eq : F t₀ = F₀)
    (hode : ∀ s ∈ Set.Icc t₀ t, HasDerivAt F (K * (1 + A / F s)) s) :
    t - t₀ = (F t - F₀ - A * Real.log ((F t + A) / (F₀ + A))) / K :=
  EarthScience.green_ampt_integrated F K A F₀ t₀ t hK hA hF₀ ht hFpos hF₀eq hode

/-- The public statement shape of the no-suction case. -/
example (F : ℝ → ℝ) (K F₀ t₀ t : ℝ) (hK : 0 < K)
    (hF₀ : 0 < F₀) (ht : t₀ ≤ t)
    (hFpos : ∀ s ∈ Set.Icc t₀ t, F s > 0)
    (hF₀eq : F t₀ = F₀)
    (hode : ∀ s ∈ Set.Icc t₀ t, HasDerivAt F (K * (1 + 0 / F s)) s) :
    t - t₀ = (F t - F₀) / K :=
  EarthScience.green_ampt_no_suction F K F₀ t₀ t hK hF₀ ht hFpos hF₀eq hode

/-- Degenerate case `t = t₀`: the integrated formula gives `0 = 0`. -/
example (F : ℝ → ℝ) (K A F₀ t₀ : ℝ) (hK : 0 < K)
    (hA : 0 ≤ A) (hF₀ : 0 < F₀)
    (hFpos : ∀ s ∈ Set.Icc t₀ t₀, F s > 0)
    (hF₀eq : F t₀ = F₀)
    (hode : ∀ s ∈ Set.Icc t₀ t₀, HasDerivAt F (K * (1 + A / F s)) s) :
    t₀ - t₀ = (F t₀ - F₀ - A * Real.log ((F t₀ + A) / (F₀ + A))) / K := by
  have h := EarthScience.green_ampt_integrated F K A F₀ t₀ t₀ hK hA hF₀ (le_refl t₀)
    hFpos hF₀eq hode
  rw [hF₀eq] at h
  rw [hF₀eq]
  exact h

/-- At `A = 0` the integrated formula reduces to `(F - F₀) / K`. -/
example (K F F₀ : ℝ) :
    (F - F₀ - 0 * Real.log ((F + 0) / (F₀ + 0))) / K = (F - F₀) / K := by
  simp
