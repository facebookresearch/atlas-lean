/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GoldenThompson
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Normed
import MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula
import MathlibExt.LinearAlgebra.Matrix.Factorizations.Schur

/-!
# The Golden–Thompson inequality

For finite Hermitian matrices `A` and `B`, `golden_thompson` bounds the trace of `exp (A + B)`
by the trace of `exp A * exp B`. We follow the dyadic argument of Forrester and Thompson,
arXiv:1408.2008v1, Sections 2.2–2.3. Schur triangularization gives the required powers-of-two
case of their trace bound (2.11), and the Lie–Trotter product formula gives the limit.
-/

@[expose] public section

open scoped ComplexOrder
open Filter Topology
open MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula

namespace MathlibExt.LinearAlgebra.Matrix.GoldenThompsonWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The squared norm of a diagonal entry is one term in the squared norm of its column. -/
private lemma diag_norm_sq_le (T : Matrix n n ℂ) (i : n) :
    ‖T i i‖ ^ 2 ≤ ((star T * T) i i).re := by
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def, Complex.conj_mul',
    Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖T j i‖) (Finset.mem_univ i)

/-- Repeated squaring bounds a diagonal entry by the corresponding entry of the Gram power. -/
private lemma diag_dyadic_le (T : Matrix n n ℂ) (k : ℕ) (i : n) :
    ‖T i i‖ ^ (2 ^ (k + 1)) ≤ (((star T * T) ^ (2 ^ k)) i i).re := by
  induction k with
  | zero => simpa using diag_norm_sq_le T i
  | succ k ih =>
    let S := (star T * T) ^ (2 ^ k)
    have hS : star S = S := by simp [S, star_pow, star_mul]
    calc
      ‖T i i‖ ^ (2 ^ (k + 1 + 1)) = (‖T i i‖ ^ (2 ^ (k + 1))) ^ 2 := by
        rw [← pow_mul, ← pow_succ]
      _ ≤ ‖S i i‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) (ih.trans (Complex.re_le_norm _)) 2
      _ ≤ ((star S * S) i i).re := diag_norm_sq_le S i
      _ = _ := by rw [hS, ← sq, ← pow_mul, ← pow_succ]

private lemma triangular_pow_diag [LinearOrder n] {T : Matrix n n ℂ}
    (hT : T.IsUpperTriangular) (p : ℕ) (i : n) :
    (T ^ p) i i = T i i ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Finset.sum_eq_single i, ih]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · rw [hT.pow p h, zero_mul]
      · rw [hT h, mul_zero]
    · simp

/-- The dyadic trace bound in a Schur basis. -/
private lemma re_trace_dyadic_le_gram (M : Matrix n n ℂ) (k : ℕ) :
    (M ^ (2 ^ (k + 1))).trace.re ≤ ((star M * M) ^ (2 ^ k)).trace.re := by
  let : LinearOrder n := (Fintype.equivFin n).linearOrder
  obtain ⟨U, T, hT, hM⟩ := M.exists_unitaryGroup_isUpperTriangular
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have htrace (X : Matrix n n ℂ) : (e X).trace = X.trace := by
    change ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)).trace = _
    rw [Matrix.trace_mul_cycle, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]
  change M = e T at hM
  rw [hM, ← map_pow, htrace, ← map_star, ← map_mul, ← map_pow, htrace]
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [triangular_pow_diag hT]
  calc
    _ ≤ ‖T i i ^ (2 ^ (k + 1))‖ := Complex.re_le_norm _
    _ = ‖T i i‖ ^ (2 ^ (k + 1)) := norm_pow _ _
    _ ≤ _ := diag_dyadic_le T k i

/-- Cyclically moving the outer factor rewrites the Gram power of a Hermitian product. -/
private lemma re_trace_dyadic_mul_le {X Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (k : ℕ) :
    ((X * Y) ^ (2 ^ (k + 1))).trace.re ≤ ((X ^ 2 * Y ^ 2) ^ (2 ^ k)).trace.re := by
  have h := re_trace_dyadic_le_gram (X * Y) k
  rw [star_mul, hX.isSelfAdjoint.star_eq, hY.isSelfAdjoint.star_eq] at h
  have heq : Y * X * (X * Y) = Y * (X ^ 2 * Y) := by simp [sq, mul_assoc]
  rwa [heq, Matrix.trace_mul_pow_comm Y, mul_assoc, ← sq] at h

private lemma re_trace_dyadic_le {X Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (k : ℕ) :
    ((X * Y) ^ (2 ^ k)).trace.re ≤ (X ^ (2 ^ k) * Y ^ (2 ^ k)).trace.re := by
  induction k generalizing X Y with
  | zero => simp
  | succ k ih =>
    refine (re_trace_dyadic_mul_le hX hY k).trans ?_
    simpa only [← pow_mul, ← pow_succ'] using ih (hX.pow 2) (hY.pow 2)

/-- **Golden–Thompson inequality.** For Hermitian complex matrices `A` and `B`,
`tr e^{A + B} ≤ tr (e^A e^B)` (P. J. Forrester and C. J. Thompson, *The Golden–Thompson
inequality — historical aspects and random matrix applications*, arXiv:1408.2008v1, equation
(1.1); S. Golden, Phys. Rev. 137 (1965) B1127; C. J. Thompson, J. Math. Phys. 6 (1965) 1812).
The inequality is taken in the partial order of `ℂ`, so it also asserts that the right side is
real, as it is. -/
theorem golden_thompson {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (NormedSpace.exp (A + B)).trace ≤ (NormedSpace.exp A * NormedSpace.exp B).trace := by
  cases isEmpty_or_nonempty n with
  | inl h => simp [Matrix.trace]
  | inr h =>
    have hleft : IsSelfAdjoint (NormedSpace.exp (A + B)).trace := by
      rw [IsSelfAdjoint, ← Matrix.trace_conjTranspose, (hA.add hB).exp.eq]
    have hright := Complex.nonneg_iff.mp (GoldenThompson.trace_exp_mul_exp_nonneg hA hB)
    refine Complex.le_def.mpr ⟨?_, ((Complex.im_eq_zero_iff_isSelfAdjoint _).2 hleft).trans
      hright.2⟩
    open scoped Matrix.Norms.Operator in
    have ht := tendsto_trotter_product A B
    have hd : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))
    apply le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp
      (continuous_id.matrix_trace.continuousAt.tendsto.comp (ht.comp hd)))
    filter_upwards with k
    let m : ℕ := 2 ^ k
    let r := (m : ℚ)⁻¹
    have hexp (X : Matrix n n ℂ) : NormedSpace.exp (r • X) ^ m = NormedSpace.exp X := by
      rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
        mul_inv_cancel₀ (by positivity : (m : ℚ) ≠ 0), one_smul]
    have hXY := re_trace_dyadic_le
      (Matrix.IsHermitian.exp ((IsSelfAdjoint.all r).smul hA))
      (Matrix.IsHermitian.exp ((IsSelfAdjoint.all r).smul hB)) k
    exact hXY.trans_eq (by rw [show 2 ^ k = m from rfl, hexp, hexp])

end MathlibExt.LinearAlgebra.Matrix.GoldenThompsonWanted
