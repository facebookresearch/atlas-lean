/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Photon observation on a finite CT design

## i. Overview

The monochromatic photon law instantiated with a finite CT
design matrix: coefficient vectors with the same design
measurement have the same transmitted intensity at every ray,
and the rank-deficient design `[1, 1]` has an explicit
admissible nonnegative nullspace pair.

## ii. Key results

* `ct_nullspace_pair`: the admissible pair `(1, 0)`, `(0, 1)`.
* `ct_equal_rates`: equal transmitted intensities for the pair.
* `ct_rates_of_measurement_eq`: the general agreement law.

## iii. Table of contents

* A. The nullspace pair and rate agreement.
-/

@[expose] public section

open Matrix

namespace PhyslibExt.BiomedicalImaging.PhotonCTInstance

/-! ## A. The nullspace pair and rate agreement. -/

/-- The rank-deficient two-cell single-ray CT design `[1, 1]`. -/
def ctRow : Matrix (Fin 1) (Fin 2) ℝ := ![![1, 1]]

/-- **Admissible nullspace pair.** The nonnegative coefficient
vectors `(1, 0)` and `(0, 1)` are distinct but have the same
forward measurement. -/
lemma ct_nullspace_pair :
    ctRow *ᵥ ![1, 0] = ctRow *ᵥ ![0, 1] ∧ (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] ∧
      (∀ i, 0 ≤ (![1, 0] : Fin 2 → ℝ) i) ∧ (∀ i, 0 ≤ (![0, 1] : Fin 2 → ℝ) i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i
    simp [ctRow, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · intro i
    fin_cases i <;> simp
  · intro i
    fin_cases i <;> simp

/-- **Equal transmitted rates.** Equal forward line integrals
give equal monochromatic transmitted intensities from incident
intensity `I0`. -/
lemma ct_equal_rates (I0 : ℝ) :
    I0 * Real.exp (-(ctRow *ᵥ ![1, 0]) 0) =
      I0 * Real.exp (-(ctRow *ᵥ ![0, 1]) 0) := by
  rw [ct_nullspace_pair.1]

/-- **General rate agreement.** Any two coefficient vectors
with the same finite design measurement have the same
transmitted intensity at every ray. -/
lemma ct_rates_of_measurement_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x y : Fin n → ℝ) (I0 : Fin m → ℝ) (h : A *ᵥ x = A *ᵥ y) (j : Fin m) :
    I0 j * Real.exp (-(A *ᵥ x) j) = I0 j * Real.exp (-(A *ᵥ y) j) := by
  rw [h]

end PhyslibExt.BiomedicalImaging.PhotonCTInstance
