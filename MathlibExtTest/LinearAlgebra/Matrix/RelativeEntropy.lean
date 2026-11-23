/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.RelativeEntropy

/-!
# Tests for `MathlibExt.LinearAlgebra.Matrix.RelativeEntropy`

The convexity of the positive-definite cone is used at a midpoint and at an endpoint. The trace
formula is checked on constant functions, where it says that the squared moduli of the
entries of the unitary `U* V` add up to the dimension. Klein's inequality, the variational formula
and the joint convexity are evaluated on scalar `2 × 2` matrices `r • 1`, where they become the
scalar inequalities `log 2 ≤ 1`, `1 / 2 ≤ log 2` and `log 2 ≤ 2 log (3 / 2)`.
-/

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.RelativeEntropy
open scoped ComplexOrder

namespace MathlibExtTest.LinearAlgebra.Matrix.RelativeEntropy

/-- The scalar matrix `r • 1` of size two. -/
noncomputable abbrev sc (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := algebraMap ℝ _ r

lemma posDef_sc {r : ℝ} (hr : 0 < r) : (sc r).PosDef := by
  rw [sc, Matrix.algebraMap_eq_diagonal]
  exact Matrix.PosDef.diagonal fun _ => by simpa using hr

lemma re_trace_sc (r : ℝ) : RCLike.re (sc r).trace = 2 * r := by
  simp [Matrix.algebraMap_eq_diagonal, Matrix.trace_diagonal]

lemma cfc_log_sc (r : ℝ) : cfc Real.log (sc r) = sc (Real.log r) :=
  cfc_algebraMap r Real.log

lemma sc_mul_sc (r t : ℝ) : sc r * sc t = sc (r * t) :=
  (map_mul (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ)) r t).symm

lemma smul_sc (c r : ℝ) : c • sc r = sc (c * r) := by
  rw [Algebra.smul_def, ← map_mul]

/-- The convexity of the positive-definite cone at the midpoint: the average of two
positive-definite matrices is positive definite. -/
example {n : Type*} {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).PosDef :=
  Matrix.convex_setOfPred_posDef hA hB (by norm_num) (by norm_num) (by norm_num)

/-- An endpoint of the segment: with weights `1` and `0` the combination is the first matrix. -/
example : ((1 : ℝ) • sc 2 + (0 : ℝ) • sc 3).PosDef :=
  Matrix.convex_setOfPred_posDef (posDef_sc two_pos) (posDef_sc (by norm_num)) (by norm_num)
    (by norm_num) (by norm_num)

/-- With `f = g = 1`, `trace_cfc_mul_cfc` says that the squared moduli of the entries of the
unitary matrix `U* V` add up to the dimension. -/
example {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ∑ i, ∑ j, ‖(star (hA.eigenvectorUnitary : Matrix n n ℂ) * hB.eigenvectorUnitary) i j‖ ^ 2 =
      Fintype.card n := by
  have h := congrArg RCLike.re (trace_cfc_mul_cfc hA hB (fun _ => 1) (fun _ => 1))
  rw [cfc_const_one ℝ A, cfc_const_one ℝ B, Matrix.mul_one, Matrix.trace_one] at h
  simp only [map_sum, RCLike.ofReal_re, RCLike.natCast_re, one_mul] at h
  exact h.symm

/-- Klein's inequality for `X = 1` and `Y = 2 • 1` is `2 log 2 ≤ 2`. -/
example : Real.log 2 ≤ 1 := by
  have h := re_trace_mul_cfc_log_sub_le (posDef_sc one_pos) (posDef_sc two_pos)
  simp only [cfc_log_sc, sc_mul_sc, re_trace_sc, Real.log_one] at h
  linarith

/-- The variational formula at `M = 0`, evaluated at `X = 2 • 1`: `4 - 4 log 2 ≤ tr e^0 = 2`. -/
example : 1 / 2 ≤ Real.log 2 := by
  have h := (isGreatest_re_trace_exp (Matrix.isHermitian_zero (n := Fin 2) (α := ℂ))).2
    ⟨sc 2, posDef_sc two_pos, rfl⟩
  simp only [cfc_log_sc, sc_mul_sc, re_trace_sc, Matrix.mul_zero, Matrix.trace_zero, map_zero,
    NormedSpace.exp_zero, Matrix.trace_one, Fintype.card_fin] at h
  norm_num at h
  linarith

/-- The maximum of the variational formula is attained at `X = e^M`, so it is not a mere upper
bound: at `M = 0` it is `re tr 1 = 2`. -/
example : (2 : ℝ) ∈ (fun X : Matrix (Fin 2) (Fin 2) ℂ => RCLike.re (X * 0).trace -
    RCLike.re (X * cfc Real.log X).trace + RCLike.re X.trace) '' {X | X.PosDef} := by
  have h := (isGreatest_re_trace_exp (Matrix.isHermitian_zero (n := Fin 2) (α := ℂ))).1
  simpa [Matrix.trace_one] using h

/-- Joint convexity at the midpoint of `(1, 1)` and `(1, 2 • 1)`: the relative entropies are
`0`, `-2 log 2` and, at the midpoint `(1, (3/2) • 1)`, `-2 log (3/2)`. -/
example : Real.log 2 ≤ 2 * Real.log (3 / 2) := by
  have hx : (sc 1, sc 1) ∈ {p : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ |
      p.1.PosDef ∧ p.2.PosDef} := ⟨posDef_sc one_pos, posDef_sc one_pos⟩
  have hy : (sc 1, sc 2) ∈ {p : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ |
      p.1.PosDef ∧ p.2.PosDef} := ⟨posDef_sc one_pos, posDef_sc two_pos⟩
  have h := convexOn_relativeEntropy.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_sc, ← map_add, cfc_log_sc, sc_mul_sc,
    re_trace_sc, Real.log_one, smul_eq_mul] at h
  norm_num at h
  linarith

end MathlibExtTest.LinearAlgebra.Matrix.RelativeEntropy
