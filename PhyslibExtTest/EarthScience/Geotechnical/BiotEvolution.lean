/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.BiotEvolution
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite Biot evolution checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.BiotEvolution` at unit
one-degree-of-freedom data (`K = I`, `Q` nonzero, `C = 0`,
storage the identity): storage value and positive
definiteness, existence at constant forcing, and the singular
no-dynamics rejection.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit storage and evolution
- B. Singular rejection

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.BiotEvolution`
-/

open Matrix
open EarthScience

namespace PhyslibExtTest.EarthScience.Geotechnical.BiotEvolution

/-! ## A. Unit storage and evolution -/

/-- At unit data the reduced storage is the identity. -/
example : biotStorage (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (0 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [biotStorage]

/-- Unit storage from `C = 1`, `K⁻¹ = 1` is positive definite
through the storage positivity lemma. -/
example : (biotStorage (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (0 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef :=
  biotStorage_posDef
    (by
      have h : (1 : Matrix (Fin 1) (Fin 1) ℝ)
          = Matrix.diagonal (fun _ => 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [h]
      exact Matrix.PosSemidef.diagonal (fun _ => zero_le_one))
    (by
      have h : (1 : Matrix (Fin 1) (Fin 1) ℝ)
          = Matrix.diagonal (fun _ => 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [h]
      exact Matrix.PosDef.diagonal (fun _ => one_pos))

/-- Existence of a Biot evolution at unit data with zero
forcing, as a client of the transported theorem. -/
example : ∃ u : ℝ → Fin 1 → ℝ, ∃ p : ℝ → Fin 1 → ℝ,
    SatisfiesBiotRateSystem 1 1 0 0 0 0 u p ∧ u 0 = 0 ∧ p 0 = 0 := by
  obtain ⟨u, p, hsat, hu0, hp0, -⟩ := biot_existsUnique
    (K := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Kinv := 1) (Q := 1)
    (C := 0) (H := 0) (df := 0) (s := 0)
    (by simp) (by simp)
    (by
      have h : biotStorage (1 : Matrix (Fin 1) (Fin 1) ℝ)
            (1 : Matrix (Fin 1) (Fin 1) ℝ)
            (0 : Matrix (Fin 1) (Fin 1) ℝ)
          = Matrix.diagonal (fun _ => 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [biotStorage]
      rw [h]
      exact Matrix.PosDef.diagonal (fun _ => one_pos))
    0 0
  exact ⟨u, p, hsat, hu0, hp0⟩

/-- Dissipative sign regression: with `Q = 0`, `C = H = I`
and zero forcing, the unique pressure path decays
(`p' = -p`), it does not grow. -/
example : ∃ p : ℝ → Fin 1 → ℝ, p 0 = ![2]
    ∧ ∀ t, deriv p t = -p t := by
  obtain ⟨u, p, hsat, -, hp0, -⟩ := biot_existsUnique
    (K := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Kinv := 1) (Q := 0)
    (C := 1) (H := 1) (df := 0) (s := 0)
    (by simp) (by simp)
    (by
      have h : biotStorage (1 : Matrix (Fin 1) (Fin 1) ℝ)
            (0 : Matrix (Fin 1) (Fin 1) ℝ)
            (1 : Matrix (Fin 1) (Fin 1) ℝ)
          = Matrix.diagonal (fun _ => 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [biotStorage]
      rw [h]
      exact Matrix.PosDef.diagonal (fun _ => one_pos))
    0 ![2]
  refine ⟨p, hp0, fun t => ?_⟩
  have h := (biot_pressure_rate_eq
    (show (1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 = 1 by simp)
    (show (1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 = 1 by simp)
    hsat t).1
  have hS : biotStorage (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [biotStorage]
  rw [hS] at h
  simpa using h

/-! ## B. Singular rejection -/

/-- With no dynamics and `H = 0`, a unit source admits no
solution: it is outside the storage range. -/
example : ¬ ∃ u : ℝ → Fin 1 → ℝ, ∃ p : ℝ → Fin 1 → ℝ,
    SatisfiesBiotRateSystem (1 : Matrix (Fin 1) (Fin 1) ℝ)
      0 0 0 0 ![1] u p := by
  rintro ⟨u, p, hsat⟩
  obtain ⟨w, hw⟩ := biot_source_mem_range_of_no_dynamics hsat
  have h0 := congrFun hw 0
  simp at h0

#print axioms EarthScience.biotStorage_posDef
#print axioms EarthScience.biot_pressure_rate_eq
#print axioms EarthScience.biot_existsUnique
#print axioms EarthScience.biot_source_mem_range_of_no_dynamics

end PhyslibExtTest.EarthScience.Geotechnical.BiotEvolution
