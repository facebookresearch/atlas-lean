/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear recurrences as observations of matrix dynamics

* `MetaMathlibExt.LinearRecurrence.companionMatrix` represents `LinearRecurrence.tupleSucc`
  in the standard coordinate basis. `companionMatrix_apply` gives its superdiagonal and last row,
  and `companionMatrix_mulVec` identifies its action on a column vector.
* `companionMatrix_pow_mulVec_of_isSolution` identifies the whole orbit with the successive
  windows of a solution.
  `isSolution_iff_forall_eq_companionMatrix_pow_mulVec` characterizes solutions by the first
  coordinate of that orbit, starting with the first terms of the sequence.
* `charpolyRecurrence` encodes the recurrence of a square matrix's characteristic polynomial.
* `charPoly_charpolyRecurrence` identifies the polynomial, and
  `isSolution_charpolyRecurrence_dotProduct_pow_mulVec` proves the recurrence
  for matrix observations.

Source: J. Ouaknine and J. Worrell, *Positivity Problems for Low-Order Linear Recurrence Sequences*,
SODA 2014, [arXiv:1307.2779, §2](https://arxiv.org/pdf/1307.2779). The source uses the transpose of
its companion matrix and puts the initial terms in reverse order in the left observation vector.
Here the initial terms are an increasing-index column state, shifted by the matrix on the left,
and the first coordinate is observed.

The source requires the last coefficient `a_k` (of the oldest term) to be nonzero. It states the
Cayley–Hamilton converse for the tail `n ≥ k` and notes in footnote 6 that the whole sequence is
an LRS if `M` has no zero eigenvalue. Mathlib's `LinearRecurrence` allows zero coefficients, so
Cayley–Hamilton gives the characteristic-polynomial recurrence from `n = 0` even for singular
matrices. This order-`k` recurrence need not be minimal.
-/

@[expose] public section

open Matrix

namespace MetaMathlibExt.LinearRecurrence

section CommSemiring

variable {R : Type*} [CommSemiring R] (E : _root_.LinearRecurrence R)

/-- The column-state companion matrix of a recurrence, representing its tuple successor map. -/
noncomputable def companionMatrix : Matrix (Fin E.order) (Fin E.order) R :=
  LinearMap.toMatrix' E.tupleSucc

/-- In zero-based indexing the non-last rows have a `1` in column `i + 1` and zeros elsewhere;
the last row is the coefficient vector in increasing index order. -/
theorem companionMatrix_apply (i j : Fin E.order) :
    companionMatrix E i j =
      if (i : ℕ) + 1 < E.order then (if (j : ℕ) = (i : ℕ) + 1 then 1 else 0) else E.coeffs j := by
  rw [companionMatrix, LinearMap.toMatrix'_apply]
  let e : Fin E.order → R := Pi.single j 1
  change (if h : (i : ℕ) + 1 < E.order then e ⟨i + 1, h⟩
    else ∑ l, E.coeffs l * e l) = _
  split_ifs with hi hij
  · have h : j = ⟨i + 1, hi⟩ := Fin.ext hij
    simp [e, h]
  · have h : j ≠ ⟨i + 1, hi⟩ := fun h ↦ hij (congrArg Fin.val h)
    simp [e, Ne.symm h]
  · simp [e, Pi.single_apply, mul_ite]

/-- Multiplying a column state by the companion matrix applies Mathlib's tuple successor. -/
theorem companionMatrix_mulVec (s : Fin E.order → R) :
    companionMatrix E *ᵥ s = E.tupleSucc s :=
  LinearMap.toMatrix'_mulVec _ _

/-- Starting from the first `E.order` terms of a solution, the state at time `n`
is the window of `E.order` terms beginning at `n`. -/
theorem companionMatrix_pow_mulVec_of_isSolution {u : ℕ → R} (hu : E.IsSolution u) (n : ℕ) :
    (companionMatrix E ^ n) *ᵥ (fun i ↦ u i) = fun i : Fin E.order ↦ u (n + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, companionMatrix_mulVec]
    funext i
    change (if h : (i : ℕ) + 1 < E.order then u (n + (i + 1))
      else ∑ j, E.coeffs j * u (n + j)) = u (n + 1 + i)
    split_ifs with hi
    · congr 1
      omega
    · rw [← hu n]
      exact congrArg u (by omega)

/-- A sequence solves a positive-order recurrence exactly when each term is the first coordinate
of the companion-matrix orbit with initial state given by its first `E.order` terms. -/
theorem isSolution_iff_forall_eq_companionMatrix_pow_mulVec (hE : 0 < E.order) (u : ℕ → R) :
    E.IsSolution u ↔
      ∀ n, u n = ((companionMatrix E ^ n) *ᵥ (fun i ↦ u i)) ⟨0, hE⟩ := by
  have observe {v : ℕ → R} (hv : E.IsSolution v) (n : ℕ) :
      v n = ((companionMatrix E ^ n) *ᵥ (fun i ↦ v i)) ⟨0, hE⟩ := by
    rw [companionMatrix_pow_mulVec_of_isSolution E hv]
    simp
  refine ⟨observe, fun h ↦ ?_⟩
  let s : Fin E.order → R := fun i ↦ u i
  have hs : (fun i : Fin E.order ↦ E.mkSol s i) = s :=
    funext (E.mkSol_eq_init s)
  have heq : u = E.mkSol s := by
    funext n
    rw [h n, observe (E.is_sol_mkSol s) n, hs]
  rw [heq]
  exact E.is_sol_mkSol s

end CommSemiring

section CommRing

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- For a square matrix of size `k`, the order-`k` recurrence whose coefficients are the
negatives of the coefficients of degrees `0` through `k - 1` of its characteristic polynomial. -/
noncomputable def charpolyRecurrence (M : Matrix ι ι R) : _root_.LinearRecurrence R where
  order := Fintype.card ι
  coeffs i := -M.charpoly.coeff i

/-- The characteristic polynomial of the specified recurrence is exactly the matrix's
characteristic polynomial. This does not assert that the recurrence has minimal order. -/
theorem charPoly_charpolyRecurrence (M : Matrix ι ι R) :
    (charpolyRecurrence M).charPoly = M.charpoly := by
  nontriviality R
  have hdeg := Matrix.charpoly_natDegree_eq_dim M
  have hlead : M.charpoly.coeff (Fintype.card ι) = 1 := by
    rw [← hdeg]
    exact M.charpoly_monic.leadingCoeff
  have hsum := M.charpoly.as_sum_range
  rw [hdeg, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range, hlead] at hsum
  rw [_root_.LinearRecurrence.charPoly]
  simp only [charpolyRecurrence, Polynomial.monomial_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  exact (add_comm _ _).trans hsum.symm

/-- Each sequence `n ↦ cᵀ M^n x` satisfies the order-`k` recurrence from the characteristic
polynomial of the `k × k` matrix `M`, by Cayley–Hamilton. Mathlib allows zero coefficients,
so the recurrence holds from `n = 0` even when `M` is singular.
A smaller recurrence may also hold. -/
theorem isSolution_charpolyRecurrence_dotProduct_pow_mulVec
    (M : Matrix ι ι R) (c x : ι → R) :
    (charpolyRecurrence M).IsSolution (fun n ↦ c ⬝ᵥ (M ^ n *ᵥ x)) := by
  have h := Matrix.aeval_self_charpoly M
  rw [← charPoly_charpolyRecurrence, _root_.LinearRecurrence.charPoly, map_sub, map_sum,
    sub_eq_zero] at h
  simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    one_smul] at h
  intro n
  have hobs := congrArg (fun A : Matrix ι ι R ↦ c ⬝ᵥ ((M ^ n * A) *ᵥ x)) h
  simpa only [← pow_add, Finset.mul_sum, mul_smul_comm, Matrix.sum_mulVec, Matrix.smul_mulVec,
    dotProduct_sum, dotProduct_smul, smul_eq_mul, charpolyRecurrence] using hobs

end CommRing

end MetaMathlibExt.LinearRecurrence
