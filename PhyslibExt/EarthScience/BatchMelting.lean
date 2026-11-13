/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Petrology: batch melting and partitioning

Equilibrium (batch) melting with melt mass fraction `F`, bulk solid/melt
partition coefficient `D`, mass balance `C₀ = F * Cl + (1 - F) * Cs` and
partitioning `Cs = D * Cl` gives `Cl = C₀ / [D + F * (1 - D)]`.

## i. Overview

This is Shaw's (1970) equilibrium, or batch, melting model with modal melting.
The melt stays in equilibrium with the residual solid until it is extracted as
a single batch, and the minerals of the residue melt in their modal
proportions, so the bulk partition coefficient `D` is constant.

`F` is the mass fraction of melt, `0 ≤ F ≤ 1`. `C₀` is the trace-element
concentration of the source before melting, `Cl` that of the melt and `Cs`
that of the residual solid, all as mass fractions (or in one common
mass-based unit). `D = Cs / Cl` is the bulk solid/melt partition coefficient:
the mineral/melt partition coefficients averaged with the mass fractions of
the minerals in the residue as weights, so `0 ≤ D` in the model.

The model's formula holds wherever its denominator
`D + F * (1 - D) = D * (1 - F) + F` is nonzero. The results here assume
`0 < D`, which keeps the denominator positive on all of `0 ≤ F ≤ 1`,
including the first-melt limit `F = 0`, where `Cl = C₀ / D`. The perfectly
incompatible case `D = 0`, where `Cl = C₀ / F` for `0 < F`, is not covered.

## ii. Key results

- `EarthScience.batch_melting_liquid`: `Cl = C₀ / (D + F * (1 - D))`.
- `EarthScience.batch_melting_denominator_pos`: the denominator is positive.
- `EarthScience.batch_melting_solid`: `Cs = D * C₀ / (D + F * (1 - D))`.

## iii. Table of contents

- A. Batch melting

## iv. References

- D. M. Shaw, "Trace element fractionation during anatexis", *Geochimica et
  Cosmochimica Acta* 34 (1970), 237–243: equilibrium (batch) melting, the
  bulk distribution coefficient of the residual solid, and the mass balance
  `C₀ = F * Cl + (1 - F) * Cs`, which give `Cl / C₀ = 1 / (D + F * (1 - D))`
  for modal melting.

## A. Batch melting
-/

@[expose] public section

namespace EarthScience

private theorem batch_melting_denom_pos_aux {F D : ℝ} (hD : 0 < D) (hF₀ : 0 ≤ F)
    (hF₁ : F ≤ 1) :
    0 < D + F * (1 - D) := by
  have h1 : 0 ≤ D * (1 - F) := mul_nonneg hD.le (sub_nonneg.mpr hF₁)
  have h2 : D + F * (1 - D) = D * (1 - F) + F := by ring
  rw [h2]
  by_cases hF : F = 0
  · subst hF
    simpa using hD
  · have hFpos : 0 < F := lt_of_le_of_ne hF₀ (Ne.symm hF)
    linarith

/-- Batch melting: conservation `C₀ = F * Cl + (1 - F) * Cs` plus
`Cs = D * Cl` gives `Cl = C₀ / (D + F * (1 - D))`. -/
theorem batch_melting_liquid {C₀ F D Cl Cs : ℝ} (hD : 0 < D) (hF₀ : 0 ≤ F) (hF₁ : F ≤ 1)
    (hcons : C₀ = F * Cl + (1 - F) * Cs) (hpart : Cs = D * Cl) :
    Cl = C₀ / (D + F * (1 - D)) := by
  have hden : 0 < D + F * (1 - D) := batch_melting_denom_pos_aux hD hF₀ hF₁
  have hden' : D + F * (1 - D) ≠ 0 := ne_of_gt hden
  rw [hpart] at hcons
  field_simp
  have hkey : Cl * (D + F * (1 - D)) = F * Cl + (1 - F) * (D * Cl) := by ring
  linarith

/-- Batch melting denominator is positive for `D > 0`, `F ∈ [0, 1]`. -/
theorem batch_melting_denominator_pos {F D : ℝ} (hD : 0 < D) (hF₀ : 0 ≤ F) (hF₁ : F ≤ 1) :
    0 < D + F * (1 - D) := by
  exact batch_melting_denom_pos_aux hD hF₀ hF₁

/-- Batch melting: solid concentration `Cs = D * C₀ / (D + F * (1 - D))`. -/
theorem batch_melting_solid {C₀ F D Cl Cs : ℝ} (hD : 0 < D) (hF₀ : 0 ≤ F) (hF₁ : F ≤ 1)
    (hcons : C₀ = F * Cl + (1 - F) * Cs) (hpart : Cs = D * Cl) :
    Cs = D * C₀ / (D + F * (1 - D)) := by
  have hCl : Cl = C₀ / (D + F * (1 - D)) := batch_melting_liquid hD hF₀ hF₁ hcons hpart
  rw [hpart, hCl]
  ring

end EarthScience
