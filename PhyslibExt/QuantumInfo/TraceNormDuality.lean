/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Bounds.Basic

/-!
# Trace-norm duality

## i. Overview

This module proves trace-norm duality for complex matrices with attainment:
the trace norm of a matrix is the greatest value of the norm of the trace
against a unitary, and the maximum is attained. The upper bound holds for
every unitary, and the trace norm of a diagonal matrix is the sum of the
norms of its diagonal entries.

The proofs build on the provider real-part form
`Matrix.traceNorm_eq_max_re_tr_U` and the supplied provider definition of
`Matrix.traceNorm`, which are not reproved here.

## ii. Key results

* `traceNorm_eq_max_norm_tr_U`: trace-norm duality with attainment.
* `exists_unitary_norm_tr_eq_traceNorm`: attainment for trace-norm duality.
* `norm_tr_unitary_conjTranspose_mul_le_traceNorm`: the upper bound for
  trace-norm duality.
* `traceNorm_diagonal`: the trace norm of a diagonal matrix is the sum of
  the norms of its diagonal entries.

## iii. Table of contents

* §A: instance transport across decidable-equality instances.
* §B: trace-norm duality with attainment.
* §C: attainment for trace-norm duality.
* §D: the upper bound for trace-norm duality.
* §E: the trace norm of a diagonal matrix.

## iv. References

* John Watrous, The Theory of Quantum Information, Eqs. (1.181)-(1.182).
-/

@[expose] public section

namespace PhyslibExt.QuantumInfo.TraceNormDuality

/-! ## A Instance transport across decidable-equality instances -/

open Classical in
/-- Classical-instance form of `traceNorm_diagonal`, proved from the supplied
provider definition of `Matrix.traceNorm`. The public `traceNorm_diagonal`
transports this across the subsingleton `DecidableEq n`. -/
private theorem traceNorm_diagonal_classical {n : Type*} [Fintype n] (d : n → ℂ) :
    (Matrix.diagonal d).traceNorm = ∑ i, ‖d i‖ := by
  have hmul : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d
      = Matrix.diagonal (fun i => ((‖d i‖ : ℝ) : ℂ))
        * Matrix.diagonal (fun i => ((‖d i‖ : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_mul, pow_two]
    rfl
  have hpos := open MatrixOrder ComplexOrder in
    Matrix.PosSemidef.nonneg
      (Matrix.PosSemidef.diagonal (d := fun i => ((‖d i‖ : ℝ) : ℂ))
        (fun i => RCLike.ofReal_nonneg (K := ℂ) (x := ‖d i‖).mpr
          (norm_nonneg (d i))))
  have hsqrt := open MatrixOrder in CFC.sqrt_mul_self _ hpos
  unfold Matrix.traceNorm
  rw [hmul, hsqrt, Matrix.trace_diagonal, ← Complex.ofReal_sum]
  exact RCLike.ofReal_re _

/-- Membership in the unitary group with the classical decidable-equality
instance, from membership with the caller's instance. -/
private theorem mem_unitaryGroup_classical_of_ambient {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n ℂ) (hM : M ∈ Matrix.unitaryGroup n ℂ) :
    M ∈ @Matrix.unitaryGroup n (fun a b => Classical.propDecidable (a = b)) _ ℂ _ _ := by
  have hiff_amb := @Matrix.mem_unitaryGroup_iff n _ _ ℂ _ _ M
  have hiff_cla := @Matrix.mem_unitaryGroup_iff n
    (fun a b => Classical.propDecidable (a = b)) _ ℂ _ _ M
  have hAMB := hiff_amb.mp hM
  rw [hiff_cla]
  ext i j
  have e := congrArg (fun X : Matrix n n ℂ => X i j) hAMB
  simp only [Matrix.mul_apply] at e ⊢
  rw [e]
  simp only [Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-- Membership in the unitary group with the caller's decidable-equality
instance, from membership with the classical instance. -/
private theorem mem_unitaryGroup_ambient_of_classical {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n ℂ)
    (hM : M ∈ @Matrix.unitaryGroup n (fun a b => Classical.propDecidable (a = b)) _ ℂ _ _) :
    M ∈ Matrix.unitaryGroup n ℂ := by
  have hiff_amb := @Matrix.mem_unitaryGroup_iff n _ _ ℂ _ _ M
  have hiff_cla := @Matrix.mem_unitaryGroup_iff n
    (fun a b => Classical.propDecidable (a = b)) _ ℂ _ _ M
  have hCLA := hiff_cla.mp hM
  rw [hiff_amb]
  ext i j
  have e := congrArg (fun X : Matrix n n ℂ => X i j) hCLA
  simp only [Matrix.mul_apply] at e ⊢
  rw [e]
  simp only [Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

open Classical in
/-- Isometry facts with the classical decidable-equality instance, from
membership with the classical instance, for the provider lemmas. -/
private theorem isometry_of_mem_unitaryGroup_classical {n : Type*} [Fintype n]
    (M : Matrix n n ℂ)
    (hM : M ∈ @Matrix.unitaryGroup n (fun a b => Classical.propDecidable (a = b)) _ ℂ _ _) :
    M.Isometry ∧ M.conjTranspose.Isometry :=
  (Matrix.mem_unitaryGroup_iff_isometry M).mp hM

/-! ## B Trace-norm duality with attainment -/

/-- Trace-norm duality with attainment (Watrous, Eq. (1.182)).
Derived from the provider real-part form `Matrix.traceNorm_eq_max_re_tr_U`,
which is not reproved here. -/
theorem traceNorm_eq_max_norm_tr_U {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ U : Matrix.unitaryGroup n ℂ,
      ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ = x} A.traceNorm := by
  have bound : ∀ U : Matrix.unitaryGroup n ℂ,
      ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ ≤ A.traceNorm := by
    intro U
    have hU :=
      (isometry_of_mem_unitaryGroup_classical _
        (mem_unitaryGroup_classical_of_ambient _ U.2)).2
    calc ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖
        ≤ ((U : Matrix n n ℂ).conjTranspose * A).traceNorm :=
          Matrix.abs_trace_le_traceNorm _
      _ = A.traceNorm := Matrix.traceNorm_isometry_left hU
  have attain : ∃ U : Matrix.unitaryGroup n ℂ,
      ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ = A.traceNorm := by
    obtain ⟨U₀, hU₀⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1
    have hU₀mem := isometry_of_mem_unitaryGroup_classical U₀.val U₀.2
    have hmem : U₀.val.conjTranspose ∈ Matrix.unitaryGroup n ℂ := by
      have hstar := mem_unitaryGroup_ambient_of_classical _ (star U₀).2
      have hval : (star U₀).val = star (U₀.val) := rfl
      rw [hval, Matrix.star_eq_conjTranspose] at hstar
      exact hstar
    have hle : ‖(U₀.val * A).trace‖ ≤ A.traceNorm := by
      calc ‖(U₀.val * A).trace‖
          ≤ (U₀.val * A).traceNorm := Matrix.abs_trace_le_traceNorm _
        _ = A.traceNorm := Matrix.traceNorm_isometry_left hU₀mem.1
    refine ⟨⟨U₀.val.conjTranspose, hmem⟩, ?_⟩
    change ‖((U₀.val.conjTranspose).conjTranspose * A).trace‖ = A.traceNorm
    rw [Matrix.conjTranspose_conjTranspose]
    apply le_antisymm hle
    rw [← hU₀]
    exact Complex.re_le_norm _
  refine ⟨attain, ?_⟩
  intro x hx
  obtain ⟨U, rfl⟩ := hx
  exact bound U

/-! ## C Attainment for trace-norm duality -/

/-- Attainment for trace-norm duality (Watrous, Eq. (1.182)).
Derived from the provider real-part form `Matrix.traceNorm_eq_max_re_tr_U`,
which is not reproved here. -/
theorem exists_unitary_norm_tr_eq_traceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ = A.traceNorm := by
  obtain ⟨U, hU⟩ := (traceNorm_eq_max_norm_tr_U A).1
  exact ⟨U, hU⟩

/-! ## D The upper bound for trace-norm duality -/

/-- Upper bound for trace-norm duality (Watrous, Eq. (1.182)).
Derived from the provider real-part form `Matrix.traceNorm_eq_max_re_tr_U`,
which is not reproved here. -/
theorem norm_tr_unitary_conjTranspose_mul_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ) :
    ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ ≤ A.traceNorm := by
  exact (traceNorm_eq_max_norm_tr_U A).2 ⟨U, rfl⟩

/-! ## E The trace norm of a diagonal matrix -/

/-- Diagonal trace norm is the sum of entry norms (Watrous, Eq. (1.181)).
Computed from the supplied provider definition of `Matrix.traceNorm`;
the provider duality statement is not reproved here. -/
theorem traceNorm_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    (Matrix.diagonal d).traceNorm = ∑ i, ‖d i‖ := by
  have hcla := traceNorm_diagonal_classical d
  convert hcla using 2
  congr 1
  exact Subsingleton.elim _ _

end PhyslibExt.QuantumInfo.TraceNormDuality
