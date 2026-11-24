/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzCore
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Operator convexity of `t ^ p` for `1 ≤ p ≤ 2` on positive-semidefinite matrices, from Physlib

The convex half of the Loewner–Heinz theorem for complex matrices, transferred from Physlib's
C⋆-algebra version

## i. Overview

The Loewner–Heinz theorem (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory
course*, lecture-notes draft of May 3, 2009, Theorem 2.6) says that `t ↦ t ^ p` is operator
monotone and operator concave for `0 ≤ p ≤ 1` and operator convex for `1 ≤ p ≤ 2`. Mathlib proves
the first half in C⋆-algebras (`CFC.monotone_rpow`, `CFC.concaveOn_rpow`). Physlib proves the
convex half in every nontrivial C⋆-algebra as
`LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici`. This file applies it to complex
matrices, with the operator norm (which makes them a C⋆-algebra) and the Loewner order, and states
it as convexity of `A ↦ A ^ p` on positive-semidefinite matrices.

## ii. Key results

- `convexOn_cfc_rpow`: `A ↦ cfc (· ^ p) A` is convex on positive-semidefinite matrices for the
  Loewner order, for `1 ≤ p ≤ 2`.

## iii. Table of contents

- A. Operator convexity of `t ^ p` for `1 ≤ p ≤ 2`

## iv. References

- E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes
  draft of May 3, 2009 (published in Contemp. Math. 529, 2010), Definition 2.1 and Theorem 2.6.

-/

@[expose] public section

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace PhyslibExt.QuantumInfo.LownerHeinz

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A. Operator convexity of `t ^ p` for `1 ≤ p ≤ 2` -/

/-- **Operator convexity of `t ^ p` for `1 ≤ p ≤ 2` (Loewner–Heinz).** For `1 ≤ p ≤ 2` the map
`A ↦ A ^ p = cfc (· ^ p) A` is convex on positive-semidefinite complex matrices for the Loewner
order: `(t A + (1 - t) B) ^ p ≤ t A ^ p + (1 - t) B ^ p` (E. A. Carlen, *Trace inequalities and
quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 2.6). The
proof applies Physlib's `LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici` to the C⋆-algebra
of complex matrices. -/
theorem convexOn_cfc_rpow {p : ℝ} (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2) :
    ConvexOn ℝ {A : Matrix n n ℂ | A.PosSemidef} (fun A => cfc (· ^ p : ℝ → ℝ) A) := by
  have hset : {A : Matrix n n ℂ | A.PosSemidef} = Set.Ici 0 := by
    ext A; simp [Matrix.nonneg_iff_posSemidef]
  rw [hset]
  refine ⟨convex_Ici 0, fun A hA B hB a b ha hb hab => ?_⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · exact le_of_eq (Subsingleton.elim _ _)
  have hA' : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hA
  have hB' : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hB
  have h := LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici (𝓐 := Matrix n n ℂ) p
    ⟨hp₁, hp₂⟩ hA'.isHermitian hB'.isHermitian hb (by linarith)
    (fun x hx => spectrum_nonneg_of_nonneg hA hx) (fun x hx => spectrum_nonneg_of_nonneg hB hx)
  have ha' : 1 - b = a := by linarith
  rw [ha'] at h
  exact h

end PhyslibExt.QuantumInfo.LownerHeinz
