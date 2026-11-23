/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Equilibrium minimises Gibbs energy for a two-phase system

At fixed temperature and pressure, equilibrium minimises the Gibbs energy.
In the linear model used here the chemical potentials `μ₁, μ₂` are
independent of composition (no mixing entropy): with total amount `N` and
`n₁ ∈ [0, N]` in phase 1, `G(n₁) = n₁ * μ₁ + (N - n₁) * μ₂`. If
`μ₁ ≤ μ₂`, putting everything in phase 1 minimises `G`; if `μ₁ = μ₂`,
every split has the same Gibbs energy, so equilibrium is degenerate.
This is the fixed-`T, p` potential; at fixed `T, V` the Helmholtz energy
would be the minimised potential instead.

## i. Overview

All three results are linear algebra in `n₁`: `G` is affine in the split.

## ii. Key results

- `EarthScience.gibbs_min_two_phase`: the all-phase-1 split minimises `G`.
- `EarthScience.gibbs_min_two_phase_strict`: strict version.
- `EarthScience.gibbs_min_equal_potentials`: degenerate case.

## iii. Table of contents

- A. Gibbs minimisation, two phases

## iv. References

- Donald A. McQuarrie and John D. Simon, *Physical Chemistry: A Molecular
  Approach* (University Science Books, 1997), Chapter 23, Phase Equilibria:
  coexistence is `μ_α = μ_β`, and at fixed `T, p` equilibrium minimises `G`.
-/

@[expose] public section

namespace EarthScience

/-- Gibbs-energy minimisation for a two-phase system at fixed `T, p`, in the
linear model where the chemical potentials `μ₁, μ₂` are independent of
composition: with total amount `N` and `n₁ ∈ [0, N]` in phase 1,
`G(n₁) = n₁ * μ₁ + (N - n₁) * μ₂`. If `μ₁ ≤ μ₂`, putting everything in
phase 1 minimises `G`. -/
theorem gibbs_min_two_phase {μ₁ μ₂ N n₁ : ℝ} (hN : 0 ≤ N)
    (hn : 0 ≤ n₁) (hnN : n₁ ≤ N) (hμ : μ₁ ≤ μ₂) :
    N * μ₁ ≤ n₁ * μ₁ + (N - n₁) * μ₂ := by
  have _ := hN
  have _ := hn
  have h1 : 0 ≤ N - n₁ := sub_nonneg.mpr hnN
  have h2 : (N - n₁) * μ₁ ≤ (N - n₁) * μ₂ :=
    mul_le_mul_of_nonneg_left hμ h1
  linarith

/-- Strict version: if `μ₁ < μ₂` and `n₁ < N`, the all-phase-1 split is
strictly better. -/
theorem gibbs_min_two_phase_strict {μ₁ μ₂ N n₁ : ℝ}
    (hn : 0 ≤ n₁) (hnN : n₁ < N) (hμ : μ₁ < μ₂) :
    N * μ₁ < n₁ * μ₁ + (N - n₁) * μ₂ := by
  have _ := hn
  have h1 : 0 < N - n₁ := sub_pos.mpr hnN
  have h2 : (N - n₁) * μ₁ < (N - n₁) * μ₂ :=
    mul_lt_mul_of_pos_left hμ h1
  linarith

/-- Equal potentials: if `μ₁ = μ₂`, every split has the same Gibbs energy,
so every split is a minimiser (degenerate equilibrium). -/
theorem gibbs_min_equal_potentials {μ₁ μ₂ N n₁ : ℝ} (hμ : μ₁ = μ₂) :
    n₁ * μ₁ + (N - n₁) * μ₂ = N * μ₁ := by
  rw [hμ]
  ring
end EarthScience
