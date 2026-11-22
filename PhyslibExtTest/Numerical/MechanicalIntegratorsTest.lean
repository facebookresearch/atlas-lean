/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Numerical.MechanicalIntegrators

/-!
# Mechanical integrator checks

Concrete consumers of `PhyslibExt.Numerical.MechanicalIntegrators`:
at `m = k = h = 1` the symplectic step sends `(0, 1)` to `(1, 1)` with
energies `1 / 2` and `1`, and both determinants take their stated
values.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit-parameter oscillator step

## iv. References

- `PhyslibExt.Numerical.MechanicalIntegrators`
-/

/-- The unit step on `(q, p) = (0, 1)`: image `(1, 1)`, energy `1`
against the initial `1 / 2`. -/
example : (MechanicalIntegrators.symplecticEulerMatrix 1 1 1).mulVec ![0, 1] =
      ![1, 1] ∧
    MechanicalIntegrators.oscillatorEnergy 1 1 ![1, 1] = 1 ∧
      MechanicalIntegrators.oscillatorEnergy 1 1 ![0, 1] = 1 / 2 := by
  refine ⟨?_, by norm_num [MechanicalIntegrators.oscillatorEnergy],
    by norm_num [MechanicalIntegrators.oscillatorEnergy]⟩
  ext i
  fin_cases i <;>
    simp [MechanicalIntegrators.symplecticEulerMatrix, Matrix.mulVec,
      Fin.sum_univ_two]

/-- Both determinants at unit parameters. -/
example : (MechanicalIntegrators.symplecticEulerMatrix 1 1 1).det = 1 ∧
    (MechanicalIntegrators.explicitEulerMatrix 1 1 1).det = 2 :=
  ⟨MechanicalIntegrators.symplecticEulerMatrix_det (by norm_num),
   by rw [MechanicalIntegrators.explicitEulerMatrix_det (by norm_num)];
      norm_num⟩
