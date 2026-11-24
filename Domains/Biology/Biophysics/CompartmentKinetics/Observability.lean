/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic

/-!
# Two-compartment observability

For central output `H = (1/V1, 0)`, the two-jet observability determinant is `k21 /
V1^2`; the initial jets identify the initial state exactly when `k21 ≠ 0` (with `V1 ≠ 0`; at `V1 = 0` the totalized output vanishes).
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.Observability

/-- **Two-compartment observability determinant.** For the
two-compartment generator `M = [[-(k10 + k12), k21], [k12, -k21]]`
and central output `H = (1 / V1, 0)`, the 2-jet observability matrix
`[H; H M]` has determinant `k21 / V1 ^ 2`. Consequently the two
initial jet observations identify the initial state exactly when
`k21 ≠ 0` (with `V1 ≠ 0`). -/
lemma observability_det {k10 k12 k21 V1 : ℝ} :
    Matrix.det ((Matrix.of !![(1:ℝ) / V1, 0; (1 / V1) * (-(k10 + k12)), (1 / V1) * k21] :
      Matrix (Fin 2) (Fin 2) ℝ)) =
      k21 / V1 ^ 2 := by
  change Matrix.det (!![(1:ℝ) / V1, 0; (1 / V1) * (-(k10 + k12)), (1 / V1) * k21] : Matrix (Fin
      2) (Fin 2) ℝ) = _
  rw [Matrix.det_fin_two_of]
  ring

/-- Identification from the two jets: if `k21 ≠ 0` and `V1 ≠ 0`, the
jet map is invertible, hence injective. -/
lemma jet_injective_of_k21_ne_zero {k10 k12 k21 V1 : ℝ}
    (hk21 : k21 ≠ 0) (hV1 : V1 ≠ 0) :
    Function.Injective
      (((Matrix.of !![(1:ℝ) / V1, 0; (1 / V1) * (-(k10 + k12)), (1 / V1) * k21] : Matrix (Fin
      2) (Fin 2) ℝ)) *ᵥ ·) := by
  rw [Matrix.mulVec_injective_iff_isUnit]
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [observability_det]
  exact isUnit_iff_ne_zero.mpr (div_ne_zero hk21 (pow_ne_zero 2 hV1))

end MathlibExt.Biology.Biophysics.CompartmentKinetics.Observability
