/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.LiebConcavity

/-!
# Tests for Lieb's concavity theorem for complex matrices

Applies `lieb_concavity_trace_rpow` to `2 × 2` matrices and checks that its domain is nonempty

## i. Overview

Applies `lieb_concavity_trace_rpow` to `2 × 2` matrices and checks that its domain is nonempty

## ii. Key results

- Applications with interior and boundary exponents

## iii. Table of contents

- A. Applications

## iv. References

- E. A. Carlen, *Trace inequalities and quantum entropy*, lecture-notes draft of May 3,
  2009, Theorem 6.1

-/

open scoped ComplexOrder

namespace PhyslibExtTest.QuantumInfo.LiebConcavity

open PhyslibExt.QuantumInfo.LiebConcavity

/-! ## A. Applications -/

/-- Interior exponents `q = r = 1/3`. -/
example (K : Matrix (Fin 2) (Fin 2) ℂ) :
    ConcaveOn ℝ
      {p : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => RCLike.re (K.conjTranspose * cfc (· ^ (3⁻¹ : ℝ) : ℝ → ℝ) p.1 * K *
        cfc (· ^ (3⁻¹ : ℝ) : ℝ → ℝ) p.2).trace) :=
  lieb_concavity_trace_rpow K (by norm_num) (by norm_num) (by norm_num)

/-- The endpoint `q + r = 1` (the Wigner–Yanase–Dyson case `q = r = 1/2`). -/
example (K : Matrix (Fin 3) (Fin 3) ℂ) :
    ConcaveOn ℝ
      {p : Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 3) (Fin 3) ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => RCLike.re (K.conjTranspose * cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) p.1 * K *
        cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) p.2).trace) :=
  lieb_concavity_trace_rpow K (by norm_num) (by norm_num) (by norm_num)

/-- The domain is nonempty: `(1, 1)` is a pair of positive-definite matrices. -/
example : ((1 : Matrix (Fin 2) (Fin 2) ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∈
    {p : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ | p.1.PosDef ∧ p.2.PosDef} :=
  ⟨Matrix.PosDef.one, Matrix.PosDef.one⟩

end PhyslibExtTest.QuantumInfo.LiebConcavity
