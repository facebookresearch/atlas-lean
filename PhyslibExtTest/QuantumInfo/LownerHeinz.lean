/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.LownerHeinz

/-!
# Tests for operator convexity of `t ^ p` on positive-semidefinite matrices

Applies `convexOn_cfc_rpow` at the exponents `3/2` and `2`

## i. Overview

Applies `convexOn_cfc_rpow` at the exponents `3/2` and `2`

## ii. Key results

- Applications at interior and endpoint exponents

## iii. Table of contents

- A. Applications

## iv. References

- E. A. Carlen, *Trace inequalities and quantum entropy*, lecture-notes draft of May 3,
  2009, Theorem 2.6

-/

open scoped ComplexOrder MatrixOrder

namespace PhyslibExtTest.QuantumInfo.LownerHeinz

open PhyslibExt.QuantumInfo.LownerHeinz

/-! ## A. Applications -/

/-- The exponent `3/2`. -/
example : ConvexOn ℝ {A : Matrix (Fin 2) (Fin 2) ℂ | A.PosSemidef}
    (fun A => cfc (· ^ (3 / 2 : ℝ) : ℝ → ℝ) A) :=
  convexOn_cfc_rpow (by norm_num) (by norm_num)

/-- The endpoint `2`, in its two-point form. -/
example {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    cfc (· ^ (2 : ℝ) : ℝ → ℝ) ((2⁻¹ : ℝ) • A + (2⁻¹ : ℝ) • B) ≤
      (2⁻¹ : ℝ) • cfc (· ^ (2 : ℝ) : ℝ → ℝ) A + (2⁻¹ : ℝ) • cfc (· ^ (2 : ℝ) : ℝ → ℝ) B :=
  (convexOn_cfc_rpow (n := Fin 2) (by norm_num) le_rfl).2 hA hB (by norm_num) (by norm_num)
    (by norm_num)

end PhyslibExtTest.QuantumInfo.LownerHeinz
