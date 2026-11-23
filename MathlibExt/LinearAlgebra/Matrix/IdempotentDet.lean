/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one.lean`
and
`P2M/Sol/S_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

import Mathlib.Tactic.Ring

@[expose] public section

namespace Matrix

/-- The Cayley--Hamilton identity for a `2 × 2` matrix, in explicit form:
`M * M = M.trace • M - M.det • 1`. -/
private theorem mul_self_eq_trace_smul_sub_det_smul_one {A : Type*} [CommRing A]
    (M : Matrix (Fin 2) (Fin 2) A) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) A) := by
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    Fin.one_eq_zero_iff, mul_zero, mul_one]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- A `2 × 2` idempotent matrix of trace one over a commutative ring has
determinant zero. -/
public theorem det_eq_zero_of_isIdempotentElem_of_trace_eq_one {A : Type*} [CommRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : IsIdempotentElem e) (htr : e.trace = 1) :
    e.det = 0 := by
  have hch := mul_self_eq_trace_smul_sub_det_smul_one e
  rw [he.eq, htr, one_smul] at hch
  have h0 : e.det • (1 : Matrix (Fin 2) (Fin 2) A) = 0 := sub_eq_self.mp hch.symm
  have h00 := congrFun (congrFun h0 0) 0
  simpa using h00

end Matrix
