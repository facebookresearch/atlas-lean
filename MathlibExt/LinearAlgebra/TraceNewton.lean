/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/LinearAlgebra/TraceNewton.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), the definition of `charpolyDescendingCoeff` and
the statement of `trace_cayley_hamilton_newton`.
The benchmark manifest records revision 1 of the problem, submitted by Kim Morrison.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

The wanted module placed these declarations in the ATLAS namespace. This module moves them
to the proved library and supplies the proof.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Newton's trace identities

`trace_cayley_hamilton_newton` relates the descending coefficients of the characteristic
polynomial to the traces of matrix powers over a commutative ring. We differentiate
the determinant of `I - X A` and use the adjugate identity to extract its coefficients.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.TraceNewtonWanted
namespace LinearAlgebra.TraceNewton

open Matrix Polynomial
open scoped BigOperators Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.dupNamespace false in
/-- **Characteristic-polynomial coefficients in descending order.** Let $A$ be a square matrix
over a commutative ring $R$ whose rows and columns are indexed by a finite set of size $N$, and
write its characteristic polynomial as $\chi_A(X) = \det(X I - A) = X^N + c_1 X^{N-1} + \dots +
c_N$. For a natural number $k$, the descending coefficient $c_k$ of $A$ is the coefficient of
$X^{N-k}$ in $\chi_A$ when $k \le N$, and $0$ when $k > N$.

Setting $c_k = 0$ for $k > N$ lets the trace recurrence be stated uniformly for all positive $k$. -/
noncomputable def charpolyDescendingCoeff {R : Type*} [CommRing R]
    (A : Matrix n n R) (k : ℕ) : R :=
  if k ≤ Fintype.card n then
    A.charpoly.coeff (Fintype.card n - k)
  else
    0

section

variable {R : Type*} [CommRing R]

private theorem descendingCoeff_eq_coeff_charpolyRev (A : Matrix n n R) (k : ℕ) :
    charpolyDescendingCoeff A k = A.charpolyRev.coeff k := by
  nontriviality R
  rw [← A.reverse_charpoly, coeff_reverse, A.charpoly_natDegree_eq_dim, charpolyDescendingCoeff]
  split_ifs with hk
  · rw [revAt_le hk]
  · rw [revAt_eq_self_of_lt (lt_of_not_ge hk)]
    exact (coeff_eq_zero_of_natDegree_lt (A.charpoly_natDegree_eq_dim.trans_lt
      (lt_of_not_ge hk))).symm

-- Jacobi's formula, obtained by differentiating one column at a time.
private theorem derivative_det (B : Matrix n n R[X]) :
    derivative B.det = (B.adjugate * B.map derivative).trace := by
  classical
  calc
    derivative B.det = ∑ i, (B.updateCol i (fun j ↦ derivative (B j i))).det := by
      rw [Matrix.det_apply, map_sum]
      simp only [Units.smul_def, map_zsmul, derivative_prod_finset, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      congr 1
      rw [← Finset.prod_erase_mul Finset.univ
        (fun j ↦ B.updateCol i (fun l ↦ derivative (B l i)) (σ j) j) (Finset.mem_univ i),
        Matrix.updateCol_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ (Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
      rfl

-- Iterating the polynomial recurrence once per coefficient gives a finite convolution.
private theorem coeff_recurrence (T : ℕ → R[X]) (p : R[X]) (s : ℕ → R)
    (h : ∀ j, T j = X * T (j + 1) + C (s j) * p) (j d : ℕ) :
    (T j).coeff d = ∑ i ∈ Finset.range (d + 1), s (j + i) * p.coeff (d - i) := by
  induction d generalizing j with
  | zero =>
    simpa using congrArg (fun q : R[X] ↦ q.coeff 0) (h j)
  | succ d ih =>
    rw [Finset.sum_range_succ', h j, coeff_add, coeff_X_mul, coeff_C_mul, ih]
    simp [Nat.add_assoc, Nat.add_right_comm j]

end

set_option linter.dupNamespace false in
/-- **Newton's trace identities for the characteristic polynomial.** Let $A$ be a square matrix
over a commutative ring $R$ whose rows and columns are indexed by a finite set of size $N$. For
each natural number $k$, let $c_k$ be the coefficient of $X^{N-k}$ in the characteristic
polynomial $\chi_A(X) = \det(X I - A)$ when $k \le N$, and $c_k = 0$ when $k > N$, so that
$\chi_A(X) = X^N + c_1 X^{N-1} + \dots + c_N$. Then for every natural number $k \ge 1$,
$$k \, c_k + \sum_{j=1}^{k} \operatorname{tr}(A^j) \, c_{k-j} = 0,$$
where $k$ is read as an element of $R$.

Source: Knill, *Some fundamental theorems in mathematics*, §220. Via
leanprover/lean-eval@38361be, problem `trace_cayley_hamilton_newton`. -/
public theorem trace_cayley_hamilton_newton {R : Type*} [CommRing R]
    (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    (k : R) * charpolyDescendingCoeff A k +
        ∑ j ∈ Finset.Icc 1 k,
          trace (A ^ j) * charpolyDescendingCoeff A (k - j) = 0 := by
  let M := A.map (C : R →+* R[X])
  let B := 1 - (X : R[X]) • M
  let T := fun j : ℕ ↦ (B.adjugate * M ^ j).trace
  have hder : derivative A.charpolyRev = -T 1 := by
    have hB : B.map derivative = -M := by
      ext i j
      by_cases hij : i = j <;> simp [B, M, hij]
    change derivative B.det = _
    rw [derivative_det, hB]
    simp [T]
  -- Multiply adj(B) B = det(B) I by Mʲ and take its trace.
  have hrec (j : ℕ) : T j = X * T (j + 1) + C (trace (A ^ j)) * A.charpolyRev := by
    have hab := congrArg (fun P : Matrix n n R[X] ↦ (P * M ^ j).trace) B.adjugate_mul
    change ((B.adjugate * (1 - X • M)) * M ^ j).trace = (B.det • 1 * M ^ j).trace at hab
    rw [Matrix.mul_sub, mul_one, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul,
      mul_assoc, ← pow_succ', Matrix.trace_sub, Matrix.trace_smul, Matrix.smul_mul, one_mul,
      Matrix.trace_smul, smul_eq_mul, smul_eq_mul] at hab
    change T j - X * T (j + 1) = A.charpolyRev * (M ^ j).trace at hab
    have htr : (M ^ j).trace = C (trace (A ^ j)) := by
      rw [AddMonoidHom.map_trace C, Matrix.map_pow]
    rw [htr, mul_comm A.charpolyRev, sub_eq_iff_eq_add, add_comm] at hab
    exact hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp_rw [descendingCoeff_eq_coeff_charpolyRev]
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have h := congrArg (fun q : R[X] ↦ q.coeff d) hder
  rw [coeff_derivative, coeff_neg, coeff_recurrence T _ _ hrec] at h
  simpa [Nat.succ_eq_add_one, add_comm, mul_comm, eq_neg_iff_add_eq_zero] using h

end LinearAlgebra.TraceNewton

end MathlibExt.LinearAlgebra.TraceNewtonWanted
