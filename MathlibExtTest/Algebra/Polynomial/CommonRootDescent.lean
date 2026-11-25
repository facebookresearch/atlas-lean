/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact source consumer repeats the statement in
`Theorems/Thm_Polynomial_mem_range_of_unique_common_root.lean` at FLT
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC; Apache-2.0. The source names no individual
AI-agent author. The applications and their proofs below are independent.
-/

module

public import MathlibExt.Algebra.Polynomial.CommonRootDescent
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Real.Sqrt
import MathlibExt.Algebra.Polynomial.DoubleRoot

/-!
# Applications and boundary tests for common-root descent

The matrix and repeated-zero fixtures certify their hypotheses independently
of the descent theorem, then exercise the importing clients.
-/

public section

open Polynomial

namespace CommonRootDescentTest

/-- The raw source binders, premise order, and conclusion are unchanged. -/
theorem source_consumer {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A B : Polynomial F) (hA : A ≠ 0)
    (hAs : (A.map (algebraMap F L)).Splits)
    (hAnd : (A.map (algebraMap F L)).roots.Nodup) (x : L)
    (hxA : Polynomial.aeval x A = 0) (hxB : Polynomial.aeval x B = 0)
    (huniq : ∀ y : L, Polynomial.aeval y A = 0 →
      Polynomial.aeval y B = 0 → y = x) :
    x ∈ (algebraMap F L).range :=
  mem_range_of_unique_common_root A B hA hAs hAnd x hxA hxB huniq

/-- A unique common spectral value descends, without assuming commutation. -/
theorem unique_common_eigenvalue {F L ι : Type*}
    [Field F] [Field L] [Algebra F L] [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι F)
    (hUs : (U.map (algebraMap F L)).charpoly.Splits)
    (hUnd : (U.map (algebraMap F L)).charpoly.roots.Nodup) (x : L)
    (hxU : x ∈ spectrum L (U.map (algebraMap F L)))
    (hxV : x ∈ spectrum L (V.map (algebraMap F L)))
    (huniq : ∀ y : L, y ∈ spectrum L (U.map (algebraMap F L)) →
      y ∈ spectrum L (V.map (algebraMap F L)) → y = x) :
    x ∈ (algebraMap F L).range := by
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map,
    IsRoot.def, eval_map_algebraMap] at hxU hxV huniq
  simp only [Matrix.charpoly_map] at hUs hUnd
  exact mem_range_of_unique_common_root U.charpoly V.charpoly
    U.charpoly_monic.ne_zero hUs hUnd x hxU hxV huniq

/-- A rational matrix with two irrational real eigenvalues. -/
def companion : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, -4; 1, 0, 2; 0, 1, 2]

/-- A second rational matrix, sharing just the spectral value two. -/
def diagonal : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![2, 3, 5]

/-- The characteristic polynomial is certified by its three-by-three
determinant, without using the descent theorem. -/
theorem companion_charpoly :
    companion.charpoly = (X - C 2) * (X ^ 2 - C 2) := by
  norm_num [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply,
    Matrix.diagonal, companion, map_ofNat]
  ring

/-- The diagonal matrix's characteristic polynomial is computed separately. -/
theorem diagonal_charpoly :
    diagonal.charpoly = (X - C 2) * (X - C 3) * (X - C 5) := by
  simp [diagonal, Matrix.charpoly_diagonal, Fin.prod_univ_succ, mul_assoc]

/-- The two matrices do not commute: their (1,0) product entries differ. -/
theorem matrices_noncommuting :
    companion * diagonal ≠ diagonal * companion := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ ↦ M 1 0) h
  norm_num [companion, diagonal, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.diagonal] at he

/-- The quadratic factor splits over the reals by the square-root identity. -/
theorem quadratic_factorization :
    (X ^ 2 - C 2 : ℝ[X]) =
      (X - C (Real.sqrt 2)) * (X - C (-Real.sqrt 2)) := by
  have hc : C (Real.sqrt 2) ^ 2 = (C 2 : ℝ[X]) := by
    rw [← map_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← hc, map_neg]
  ring

/-- All splitting and simple-root hypotheses for the real cubic are proved
without using common-root descent. -/
theorem cubic_split_simple :
    ((X - C 2) * (X ^ 2 - C 2) : ℝ[X]).Splits ∧
      ((X - C 2) * (X ^ 2 - C 2) : ℝ[X]).roots.Nodup := by
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hn : (2 : ℝ) ≠ -Real.sqrt 2 := by linarith
  have hs : Real.sqrt 2 ≠ -Real.sqrt 2 := by linarith
  rw [quadratic_factorization]
  refine ⟨(Splits.X_sub_C _).mul
    ((Splits.X_sub_C _).mul (Splits.X_sub_C _)), ?_⟩
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero (2 : ℝ))
      (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  simp [hlt.ne, hn, hs]

/-- Closed certificates for every hypothesis of the spectral application. -/
theorem matrix_hypotheses :
    (companion.map (algebraMap ℚ ℝ)).charpoly.Splits ∧
    (companion.map (algebraMap ℚ ℝ)).charpoly.roots.Nodup ∧
    (2 : ℝ) ∈ spectrum ℝ (companion.map (algebraMap ℚ ℝ)) ∧
    (2 : ℝ) ∈ spectrum ℝ (diagonal.map (algebraMap ℚ ℝ)) ∧
    (∀ y : ℝ, y ∈ spectrum ℝ (companion.map (algebraMap ℚ ℝ)) →
      y ∈ spectrum ℝ (diagonal.map (algebraMap ℚ ℝ)) → y = 2) := by
  have h2 : algebraMap ℚ ℝ (2 : ℚ) = 2 := by norm_num
  have h3 : algebraMap ℚ ℝ (3 : ℚ) = 3 := by norm_num
  have h5 : algebraMap ℚ ℝ (5 : ℚ) = 5 := by norm_num
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map,
    companion_charpoly, diagonal_charpoly, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, h2, h3, h5]
  refine ⟨cubic_split_simple.1, cubic_split_simple.2, ?_, ?_, ?_⟩
  · norm_num [IsRoot.def]
  · norm_num [IsRoot.def]
  · intro y hyA hyB
    simp only [IsRoot.def, eval_mul, eval_sub, eval_pow, eval_X, eval_C,
      mul_eq_zero, sub_eq_zero] at hyA hyB
    rcases hyB with (h | h) | h
    · exact h
    · subst y; norm_num at hyA
    · subst y; norm_num at hyA

/-- The genuine spectral client is exercised on the noncommuting fixture. -/
theorem matrix_descent : (2 : ℝ) ∈ (algebraMap ℚ ℝ).range :=
  unique_common_eigenvalue companion diagonal matrix_hypotheses.1
    matrix_hypotheses.2.1 2 matrix_hypotheses.2.2.1
    matrix_hypotheses.2.2.2.1 matrix_hypotheses.2.2.2.2

/-- A unique squared-linear divisor descends when the derivative is nonzero,
split, and simple-rooted. No separability of Q is assumed. -/
theorem unique_repeated_zero {F L : Type*}
    [Field F] [Field L] [Algebra F L] (Q : F[X])
    (hQ : Q.derivative ≠ 0)
    (hs : (Q.derivative.map (algebraMap F L)).Splits)
    (hn : (Q.derivative.map (algebraMap F L)).roots.Nodup) (x : L)
    (hx : (X - C x) ^ 2 ∣ Q.map (algebraMap F L))
    (huniq : ∀ y : L, (X - C y) ^ 2 ∣ Q.map (algebraMap F L) → y = x) :
    x ∈ (algebraMap F L).range := by
  have hz (y : L) : (X - C y) ^ 2 ∣ Q.map (algebraMap F L) ↔
      aeval y Q = 0 ∧ aeval y Q.derivative = 0 := by
    rw [sq_dvd_iff_eval_and_derivative_eval_eq_zero, derivative_map]
    simp only [eval_map_algebraMap]
  have hx' := (hz x).mp hx
  apply mem_range_of_unique_common_root Q.derivative Q hQ hs hn x hx'.2 hx'.1
  intro y hyD hyQ
  exact huniq y ((hz y).mpr ⟨hyQ, hyD⟩)

/-- A rational cubic whose only repeated zero is one. -/
noncomputable def repeatedPolynomial : ℚ[X] := (X - 1) ^ 2 * (X + 2)

/-- The derivative factorization is computed independently of descent. -/
theorem repeated_derivative :
    repeatedPolynomial.derivative = C 3 * (X - 1) * (X + 1) := by
  simp [repeatedPolynomial, derivative_mul, derivative_pow, map_ofNat]
  ring

/-- Scalar extension preserves the independently computed derivative. -/
theorem repeated_mapped_derivative :
    repeatedPolynomial.derivative.map (algebraMap ℚ ℝ) =
      C 3 * (X - 1) * (X + 1) := by
  rw [repeated_derivative]
  norm_num [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add]

/-- The derivative's nonzero, splitting, and nodup hypotheses are inhabited. -/
theorem repeated_derivative_data :
    repeatedPolynomial.derivative ≠ 0 ∧
    (repeatedPolynomial.derivative.map (algebraMap ℚ ℝ)).Splits ∧
    (repeatedPolynomial.derivative.map (algebraMap ℚ ℝ)).roots.Nodup := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrArg (eval (0 : ℚ)) h
    norm_num [repeated_derivative] at he
  · rw [repeated_mapped_derivative]
    exact ((Splits.C 3).mul (Splits.X_sub_C 1)).mul (Splits.X_add_C 1)
  · rw [repeated_mapped_derivative, mul_assoc,
      roots_C_mul _ (by norm_num : (3 : ℝ) ≠ 0),
      roots_mul (show ((X - 1) * (X + 1) : ℝ[X]) ≠ 0 from
        mul_ne_zero (by simpa using X_sub_C_ne_zero (1 : ℝ))
          (by simpa using X_add_C_ne_zero (1 : ℝ))),
      show (X - 1 : ℝ[X]).roots = {1} by
        simpa only [C_1] using roots_X_sub_C (1 : ℝ),
      show (X + 1 : ℝ[X]).roots = {-1} by
        simpa only [C_1] using roots_X_add_C (1 : ℝ)]
    norm_num

/-- One is a repeated zero, and minus one is excluded by Q(-1)=4. -/
theorem repeated_zero_hypotheses :
    (X - C (1 : ℝ)) ^ 2 ∣ repeatedPolynomial.map (algebraMap ℚ ℝ) ∧
    (∀ y : ℝ, (X - C y) ^ 2 ∣
      repeatedPolynomial.map (algebraMap ℚ ℝ) → y = 1) := by
  constructor
  · refine ⟨X + 2, ?_⟩
    norm_num [repeatedPolynomial, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_add]
  · intro y hy
    obtain ⟨hQ, hD⟩ :=
      (sq_dvd_iff_eval_and_derivative_eval_eq_zero _ _).mp hy
    rw [derivative_map, repeated_mapped_derivative] at hD
    norm_num [mul_eq_zero] at hD
    rcases hD with h | h
    · linarith
    · have he : y = -1 := by linarith
      subst y
      norm_num [repeatedPolynomial, eval_map_algebraMap] at hQ

/-- The repeated-zero application really permits a nonmonic first polynomial. -/
theorem repeated_nonmonic : ¬repeatedPolynomial.derivative.Monic := by
  intro h
  have he := h.leadingCoeff
  have hm : (X - 1 : ℚ[X]).leadingCoeff = 1 := by
    simpa only [C_1] using leadingCoeff_X_sub_C (1 : ℚ)
  have hp : (X + 1 : ℚ[X]).leadingCoeff = 1 := by
    simpa only [C_1] using leadingCoeff_X_add_C (1 : ℚ)
  norm_num [repeated_derivative, leadingCoeff_mul, hm, hp] at he

/-- Q is genuinely nonseparable, so no such premise can be added on B. -/
theorem repeated_nonseparable : ¬repeatedPolynomial.Separable := by
  intro h
  have hz : aeval (1 : ℚ) repeatedPolynomial = 0 := by
    norm_num [repeatedPolynomial]
  apply h.aeval_derivative_ne_zero hz
  norm_num [repeated_derivative]

/-- The repeated-zero client is exercised with nonmonic A and nonseparable B. -/
theorem repeated_descent : (1 : ℝ) ∈ (algebraMap ℚ ℝ).range :=
  unique_repeated_zero repeatedPolynomial repeated_derivative_data.1
    repeated_derivative_data.2.1 repeated_derivative_data.2.2 1
    repeated_zero_hypotheses.1 repeated_zero_hypotheses.2

/-- The exact API accepts B=0, without a nonzero or separability
premise on B. -/
theorem zero_second_polynomial : (2 : ℝ) ∈ (algebraMap ℚ ℝ).range := by
  apply mem_range_of_unique_common_root (X - C (2 : ℚ)) 0
    (X_sub_C_ne_zero _) ?_ ?_ 2 ?_ ?_ ?_
  · simpa only [Polynomial.map_sub, map_X, map_C] using
      Splits.X_sub_C (algebraMap ℚ ℝ (2 : ℚ))
  · simp only [Polynomial.map_sub, map_X, map_C, roots_X_sub_C]
    exact Multiset.nodup_singleton _
  · norm_num
  · simp
  · intro y hy _
    simpa [sub_eq_zero] using hy

/-- A genuinely nonmonic cubic, not a characteristic polynomial. -/
noncomputable def nonmonicPolynomial : ℚ[X] :=
  C 3 * ((X - C 2) * (X ^ 2 - C 2))

/-- The scaled cubic retains all the required first-polynomial hypotheses. -/
theorem nonmonic_data :
    nonmonicPolynomial ≠ 0 ∧ ¬nonmonicPolynomial.Monic ∧
    (nonmonicPolynomial.map (algebraMap ℚ ℝ)).Splits ∧
    (nonmonicPolynomial.map (algebraMap ℚ ℝ)).roots.Nodup := by
  have hm : nonmonicPolynomial.map (algebraMap ℚ ℝ) =
      C 3 * ((X - C 2) * (X ^ 2 - C 2)) := by
    norm_num [nonmonicPolynomial, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have he := congrArg (eval (0 : ℚ)) h
    norm_num [nonmonicPolynomial] at he
  · intro h
    have he := h.leadingCoeff
    rw [nonmonicPolynomial, leadingCoeff_mul, leadingCoeff_C,
      ← companion_charpoly, companion.charpoly_monic.leadingCoeff] at he
    norm_num at he
  · rw [hm]
    exact cubic_split_simple.1.C_mul 3
  · rw [hm, roots_C_mul _ (by norm_num : (3 : ℝ) ≠ 0)]
    exact cubic_split_simple.2

/-- The exact API is exercised on 3(X-2)(X²-2), with B=X-2. -/
theorem nonmonic_descent : (2 : ℝ) ∈ (algebraMap ℚ ℝ).range := by
  apply mem_range_of_unique_common_root nonmonicPolynomial (X - C (2 : ℚ))
    nonmonic_data.1 nonmonic_data.2.2.1 nonmonic_data.2.2.2 2
  · norm_num [nonmonicPolynomial]
  · norm_num
  · intro y _ hy
    simpa [sub_eq_zero] using hy

end CommonRootDescentTest
