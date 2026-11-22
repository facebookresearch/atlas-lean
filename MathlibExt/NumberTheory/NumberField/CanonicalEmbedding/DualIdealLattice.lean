/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice.lean`
and
`P2M/Sol/S_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice.lean`
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

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.DedekindDomain.Different

@[expose] public section

open NumberField NumberField.mixedEmbedding Module
open scoped Classical nonZeroDivisors

namespace NumberField.mixedEmbedding

private theorem trace_mixedEmbedding (K : Type*) [Field K] [NumberField K] (x : K) :
    Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  rw [Algebra.trace_eq_matrix_trace (latticeBasis K) (mixedEmbedding K x),
    Algebra.trace_eq_matrix_trace (integralBasis K) x, Matrix.trace, Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]

private theorem traceForm_mixedSpace_nondegenerate (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero _ (latticeBasis K)
  have h : LinearMap.BilinForm.toMatrix (latticeBasis K) (Algebra.traceForm ℝ (mixedSpace K))
      = (Algebra.traceMatrix ℚ (integralBasis K)).map (algebraMap ℚ ℝ) := by
    ext i j
    rw [Algebra.traceForm_toMatrix, Matrix.map_apply, Algebra.traceMatrix_apply,
      latticeBasis_apply, latticeBasis_apply, ← map_mul, trace_mixedEmbedding,
      Algebra.traceForm_apply, eq_ratCast]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Algebra.discr_def, map_ne_zero]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)

/-- The dual of the ideal lattice of a fractional ideal under the (flipped) trace
form on the mixed space is the mixed embedding of the trace dual fractional ideal. -/
public theorem coe_dualSubmodule_flip_traceForm_idealLattice
    (K : Type*) [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
        (mixedEmbedding.idealLattice K I) : Set (mixedSpace K))
      = mixedEmbedding K '' (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
  have hB : (Algebra.traceForm ℝ (mixedSpace K)).flip.Nondegenerate :=
    (traceForm_mixedSpace_nondegenerate K).flip
  have hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := Units.ne_zero I
  have hspan : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ
      = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) := by
    ext x
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe, mem_span_basisOfFractionalIdeal]
    rfl
  have hdual : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ
      = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I).traceDual) := by
    rw [FractionalIdeal.coe_dual ℤ ℚ hI]
    exact Submodule.traceDual_span_of_basis ℤ _ (basisOfFractionalIdeal K I) hspan
  have hdb : ⇑((Algebra.traceForm ℝ (mixedSpace K)).flip.dualBasis hB
        (fractionalIdealLatticeBasis K I))
      = fun i => mixedEmbedding K ((basisOfFractionalIdeal K I).traceDual i) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    rw [LinearMap.BilinForm.flip_apply, fractionalIdealLatticeBasis_apply, Algebra.traceForm_apply,
      ← map_mul, trace_mixedEmbedding, Basis.trace_mul_traceDual]
    split_ifs <;> simp
  have himage : (⇑(mixedEmbedding K) '' (FractionalIdeal.dual ℤ ℚ
        (I : FractionalIdeal (𝓞 K)⁰ K) : Set K))
      = ((Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I).traceDual)).map
          (mixedEmbedding K).toIntAlgHom.toLinearMap : Set (mixedSpace K)) := by
    rw [Submodule.map_coe, ← hdual]
    rfl
  rw [← span_idealLatticeBasis, LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB, hdb, himage,
    Submodule.map_span, ← Set.range_comp]
  rfl

end NumberField.mixedEmbedding
