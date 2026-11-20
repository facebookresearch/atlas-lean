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

@[expose] public section

namespace PhyslibExt.QuantumInfo.TraceNormDuality

open Classical in
/-- Trace-norm duality with attainment (Watrous, Eq. (1.182)).
Derived from the provider real-part form `Matrix.traceNorm_eq_max_re_tr_U`,
which is not reproved here. -/
theorem traceNorm_eq_max_norm_tr_U {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ U : Matrix.unitaryGroup n ℂ,
      ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ = x} A.traceNorm := by
  have bound : ∀ U : Matrix.unitaryGroup n ℂ,
      ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ ≤ A.traceNorm := by
    intro U
    have hU : ((U : Matrix n n ℂ).conjTranspose).Isometry :=
      ((Matrix.mem_unitaryGroup_iff_isometry U.val).mp U.2).2
    calc ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖
        ≤ ((U : Matrix n n ℂ).conjTranspose * A).traceNorm :=
          Matrix.abs_trace_le_traceNorm _
      _ = A.traceNorm := Matrix.traceNorm_isometry_left hU
  have attain : ∃ U : Matrix.unitaryGroup n ℂ,
      ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ = A.traceNorm := by
    obtain ⟨U₀, hU₀⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1
    have hU₀mem :=
      (Matrix.mem_unitaryGroup_iff_isometry U₀.val).mp U₀.2
    have hmem : U₀.val.conjTranspose ∈ Matrix.unitaryGroup n ℂ := by
      refine (Matrix.mem_unitaryGroup_iff_isometry _).mpr ⟨hU₀mem.2, ?_⟩
      rw [Matrix.conjTranspose_conjTranspose]
      exact hU₀mem.1
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

open Classical in
/-- Attainment for trace-norm duality (Watrous, Eq. (1.182)).
Derived from the provider real-part form `Matrix.traceNorm_eq_max_re_tr_U`,
which is not reproved here. -/
theorem exists_unitary_norm_tr_eq_traceNorm {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ = A.traceNorm := by
  obtain ⟨U₀, hU₀⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1
  have hU₀mem :=
    (Matrix.mem_unitaryGroup_iff_isometry U₀.val).mp U₀.2
  have hmem : U₀.val.conjTranspose ∈ Matrix.unitaryGroup n ℂ := by
    refine (Matrix.mem_unitaryGroup_iff_isometry _).mpr ⟨hU₀mem.2, ?_⟩
    rw [Matrix.conjTranspose_conjTranspose]
    exact hU₀mem.1
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

open Classical in
/-- Upper bound for trace-norm duality (Watrous, Eq. (1.182)).
Derived from the provider real-part form `Matrix.traceNorm_eq_max_re_tr_U`,
which is not reproved here. -/
theorem norm_tr_unitary_conjTranspose_mul_le_traceNorm {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ) :
    ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖ ≤ A.traceNorm := by
  have hU : ((U : Matrix n n ℂ).conjTranspose).Isometry :=
    ((Matrix.mem_unitaryGroup_iff_isometry U.val).mp U.2).2
  calc ‖((U : Matrix n n ℂ).conjTranspose * A).trace‖
      ≤ ((U : Matrix n n ℂ).conjTranspose * A).traceNorm :=
        Matrix.abs_trace_le_traceNorm _
    _ = A.traceNorm := Matrix.traceNorm_isometry_left hU

open Classical in
/-- Diagonal trace norm is the sum of entry norms (Watrous, Eq. (1.181)).
Computed from the supplied provider definition of `Matrix.traceNorm`;
the provider duality statement is not reproved here. -/
theorem traceNorm_diagonal {n : Type*} [Fintype n] (d : n → ℂ) :
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

end PhyslibExt.QuantumInfo.TraceNormDuality
