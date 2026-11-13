/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.IntegratedClausiusClapeyron

/-!
# Integrated Clausius-Clapeyron checks

Concrete consumers of
`PhyslibExt.EarthScience.IntegratedClausiusClapeyron`: the ideal-vapor
differential form with numbers, the integrated form applied to an
abstract pressure satisfying the differential form, and the degenerate
`T₁ = T₂` boundary case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. Differential
check: `L = 12`, `T = 2`, `v₂ - v₁ = 2`, `R = 1`, `p = 1` gives
`dp / dT = 12 / (2 * 2) = 3 = 12 * 1 / (1 * 2 ^ 2)`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Differential form with numbers
- B. Integrated form, abstract pressure and boundary case

## iv. References

- `PhyslibExt.EarthScience.IntegratedClausiusClapeyron`
-/

/-- Differential form with numbers: `L = 12`, `T = 2`, `Δv = 2` gives
`dp / dT = 3`, matching `L * p / (R * T ^ 2)` with `R = 1`, `p = 1`. -/
example : (3 : ℝ) = 12 * 1 / (1 * 2 ^ 2) := by
  have h := EarthScience.clausius_clapeyron_differential
    (dp_dT := (3 : ℝ)) (L := (12 : ℝ)) (R := (1 : ℝ)) (T := (2 : ℝ))
    (p := (1 : ℝ)) (v₂ := (2 : ℝ)) (v₁ := (0 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h

/-- Integrated form for an abstract pressure satisfying the differential
form, with `T₁ = 1`, `T₂ = 2`, `L = R = 1`: `log (p 2 / p 1) = 1 / 2`. -/
example (p : ℝ → ℝ)
    (hp : ∀ t ∈ Set.Icc (1 : ℝ) 2, 0 < p t)
    (hder : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      HasDerivAt p (1 * p t / (1 * t ^ 2)) t) :
    Real.log (p 2 / p 1) = (1 : ℝ) / 2 := by
  have h := EarthScience.integrated_clausius_clapeyron (p := p)
    (T₁ := (1 : ℝ)) (T₂ := (2 : ℝ)) (L := (1 : ℝ)) (R := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hder
  calc Real.log (p 2 / p 1) = -(1 / 1 : ℝ) * (1 / 2 - 1 / 1) := h
    _ = (1 : ℝ) / 2 := by norm_num

/-- Boundary case `T₁ = T₂`: the integrated form gives `log 1 = 0`. -/
example (p : ℝ → ℝ) (hp : 0 < p (1 : ℝ))
    (hder : HasDerivAt p (1 * p 1 / (1 * (1 : ℝ) ^ 2)) (1 : ℝ)) :
    Real.log (p 1 / p 1) = 0 := by
  have h := EarthScience.integrated_clausius_clapeyron (p := p)
    (T₁ := (1 : ℝ)) (T₂ := (1 : ℝ)) (L := (1 : ℝ)) (R := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t ht => by
      have : t = 1 := by
        have h1 := ht.1
        have h2 := ht.2
        linarith
      rw [this]
      exact hp)
    (fun t ht => by
      have : t = 1 := by
        have h1 := ht.1
        have h2 := ht.2
        linarith
      rw [this]
      exact hder)
  calc Real.log (p 1 / p 1) = -(1 / 1 : ℝ) * (1 / 1 - 1 / 1) := h
    _ = 0 := by norm_num
