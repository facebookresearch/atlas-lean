/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.LinearAlgebra.Matrix.LowerToeplitz
public import MathlibExt.LinearAlgebra.Matrix.NonnegativeMinors
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import MathlibExt.Combinatorics.Enumerative.RiordanArraySum

/-!
# Total positivity of Bell-type Riordan arrays

A Bell-type Riordan array has nonnegative minors if the lower Toeplitz matrix
of its A-sequence has nonnegative minors. Writing `Dₙ` and `Tₙ` for the leading
square truncations of the Bell and Toeplitz matrices, the proof factors `Dₙ₊₁` as
the block diagonal matrix with blocks `1` and `Dₙ` times `Tₙ₊₁`.
-/

namespace MetaMathlibExt
namespace BellRiordan

open exteriorPower PowerSeries

/-- The finite Cauchy–Binet argument, expanding the wedge of the selected rows
in the exterior power of the coordinate basis. -/
private theorem totallyNonneg_mul {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg) : (A * B).IsTotallyNonneg := by
  classical
  intro k r c hr hc
  let b := Pi.basisFun ℝ (Fin N)
  let v := ιMulti ℝ k (fun i => A (r i))
  let C := B.submatrix id c
  let L := alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap C.vecMulLinear)
  suffices 0 ≤ L v by
    rw [alternatingMapLinearEquiv_apply_ιMulti] at this
    exact this
  rw [← (b.exteriorPower k).sum_repr v, map_sum]
  apply Finset.sum_nonneg
  intro s _
  let e := Set.powersetCard.ofFinEmbEquiv.symm s
  rw [map_smul, smul_eq_mul]
  apply mul_nonneg
  · rw [basis_repr_apply, ιMultiDual_apply_ιMulti]
    simp only [b, Module.Basis.coord_apply, Pi.basisFun_repr]
    exact hA hr e.strictMono
  · simp only [L, basis_apply, ιMulti_family, alternatingMapLinearEquiv_apply_ιMulti,
      AlternatingMap.compLinearMap_apply, Function.comp_apply, b, Pi.basisFun_apply,
      Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]
    exact hB e.strictMono hc

/-- Adjoining a leading unit block preserves nonnegativity of the minors. -/
private theorem totallyNonneg_border {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h00 : M 0 0 = 1) (hrow : ∀ j ≠ 0, M 0 j = 0) (hcol : ∀ i ≠ 0, M i 0 = 0)
    (hM : (M.submatrix Fin.succ Fin.succ).IsTotallyNonneg) : M.IsTotallyNonneg := by
  have interior {k : ℕ} {r c : Fin k → Fin (N + 1)} (hr : StrictMono r) (hc : StrictMono c)
      (hr0 : ∀ i, r i ≠ 0) (hc0 : ∀ j, c j ≠ 0) : 0 ≤ (M.submatrix r c).det := by
    simpa [Matrix.submatrix_submatrix, Function.comp_def] using
      hM (Fin.strictMono_pred_comp hr0 hr) (Fin.strictMono_pred_comp hc0 hc)
  intro k r c hr hc
  cases k with
  | zero => simp
  | succ k =>
    have pos {f : Fin (k + 1) → Fin (N + 1)} (hf : StrictMono f) {j : Fin (k + 1)}
        (hj : j ≠ 0) : f j ≠ 0 :=
      (lt_of_le_of_lt (Fin.zero_le _) (hf (Fin.pos_iff_ne_zero.mpr hj))).ne'
    by_cases hr0 : r 0 = 0
    · by_cases hc0 : c 0 = 0
      · rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
        · simpa [hr0, hc0, h00, Matrix.submatrix_submatrix] using
            interior (hr.comp Fin.strictMono_succ) (hc.comp Fin.strictMono_succ)
              (fun _ => pos hr (Fin.succ_ne_zero _)) (fun _ => pos hc (Fin.succ_ne_zero _))
        · intro j _ hj
          simp [hr0, hrow _ (pos hc hj)]
        · simp
      · rw [Matrix.det_eq_zero_of_row_eq_zero 0]
        intro j
        have hj := (Fin.pos_iff_ne_zero.mpr hc0).trans_le (hc.monotone (Fin.zero_le j))
        simpa [hr0] using hrow _ hj.ne'
    · have hr' (i) : r i ≠ 0 :=
        ((Fin.pos_iff_ne_zero.mpr hr0).trans_le (hr.monotone (Fin.zero_le i))).ne'
      by_cases hc0 : c 0 = 0
      · rw [Matrix.det_eq_zero_of_column_eq_zero 0]
        intro i
        simpa [hc0] using hcol _ (hr' i)
      · exact interior hr hc hr' fun j =>
          ((Fin.pos_iff_ne_zero.mpr hc0).trans_le (hc.monotone (Fin.zero_le j))).ne'

/-- Successive square truncations of the array are obtained by adjoining a unit
in the top left corner and multiplying by a Toeplitz truncation. -/
private theorem factor_truncation (g : PowerSeries ℝ) (a : ℕ → ℝ)
    (hsubst : (mk a).subst (X * g) = g) (N : ℕ) :
    (Matrix.of fun n k : Fin N => coeff n.val (g * (X * g) ^ k.val)) =
      (Matrix.of fun n j : Fin N => coeff n.val ((X * g) ^ j.val)) *
        (_root_.Matrix.lowerToeplitz a).submatrix Fin.val Fin.val := by
  have h0 : constantCoeff (X * g) = 0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' h0
  ext n k
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => coeff n.val ((X * g) ^ j) * _root_.Matrix.lowerToeplitz a j k.val)]
  have h := riordan_array_sum_eq_coeff_subst 1 (X * g) (X ^ k.val * mk a) h0 n.val
  simp only [one_mul, coeff_X_pow_mul', coeff_mk, subst_mul hs, subst_pow hs,
    subst_X hs, hsubst] at h
  rw [mul_comm g, ← h]
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono (by omega))
  · intro j hj
    have hnj : ¬ j ≤ n.val := by simpa using (Finset.mem_sdiff.mp hj).2
    simp [mul_pow, coeff_X_pow_mul', hnj]
  · simp [Matrix.lowerToeplitz]

private theorem truncation_totallyNonneg (g : PowerSeries ℝ) (a : ℕ → ℝ)
    (hsubst : (mk a).subst (X * g) = g) (hpf : (Matrix.lowerToeplitz a).IsTotallyNonneg)
    (N : ℕ) :
    (Matrix.of fun n k : Fin N => coeff n.val (g * (X * g) ^ k.val)).IsTotallyNonneg := by
  induction N with
  | zero =>
    convert (Matrix.IsTotallyNonneg.one : (1 : Matrix (Fin 0) (Fin 0) ℝ).IsTotallyNonneg) using 1
    exact Subsingleton.elim _ _
  | succ N ih =>
    rw [factor_truncation g a hsubst]
    apply totallyNonneg_mul _ (hpf.submatrix Fin.val_strictMono Fin.val_strictMono)
    apply totallyNonneg_border
    · simp
    · intro j hj
      have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [coeff_zero_eq_constantCoeff, zero_pow hj']
    · intro i hi
      simp [coeff_one, show i.val ≠ 0 from fun h => hi (Fin.ext h)]
    · have shift (n k : ℕ) :
          coeff (n + 1) ((X * g) ^ (k + 1)) = coeff n (g * (X * g) ^ k) := by
        rw [pow_succ', mul_assoc, coeff_succ_X_mul]
      simpa only [Matrix.submatrix, Fin.val_succ, Matrix.of_apply, shift] using ih

/-- The finitely many indices of a minor fit in one leading square truncation. -/
private theorem nonnegativeMinors_of_truncations (M : Matrix ℕ ℕ ℝ)
    (hT : ∀ N, (M.submatrix (Fin.val (n := N)) Fin.val).IsTotallyNonneg) :
    Matrix.HasNonnegativeMinors M := by
  intro k r c hr hc
  obtain ⟨R, hR⟩ := (Set.finite_range r).bddAbove
  obtain ⟨C, hC⟩ := (Set.finite_range c).bddAbove
  let row (i) : Fin (max R C + 1) := ⟨r i, by
    have := hR (Set.mem_range_self i)
    omega⟩
  let col (i) : Fin (max R C + 1) := ⟨c i, by
    have := hC (Set.mem_range_self i)
    omega⟩
  exact hT (max R C + 1) (show StrictMono row from fun _ _ hij => hr hij)
    (show StrictMono col from fun _ _ hij => hc hij)

end BellRiordan

open PowerSeries

/-- **Bell-type Riordan arrays with a Pólya frequency A-sequence are totally positive.** Let $g$
be a formal power series over $\mathbb{R}$ with $g(0) \neq 0$, write $[x^n]F$ for the coefficient
of $x^n$ in a power series $F$, and let $D = (d_{n,k})_{n,k \ge 0}$ be the Bell-type Riordan array
$(g(x), x g(x))$, with entries $d_{n,k} = [x^n]\, g(x) (x g(x))^k$. Let $(a_j)_{j \ge 0}$ be a
real sequence, the $A$-sequence of $D$, such that for all $n, k \ge 0$
$$d_{n+1,k+1} = \sum_{j=0}^{n} a_j\, d_{n,k+j}.$$
If $(a_j)$ is a Pólya frequency sequence, that is, every minor of its lower Toeplitz matrix
(whose entry in row $n$ and column $k$ is $a_{n-k}$ for $k \le n$ and $0$ otherwise) is
nonnegative, then $D$ is totally positive: every minor of $D$ is nonnegative.

The sum stops at $j = n$ because $d_{n,m} = 0$ for $m > n$.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Proposition 5. -/
public theorem bellRiordan_hasNonnegativeMinors_of_aSequence (g : PowerSeries ℝ)
    (hg : PowerSeries.constantCoeff g ≠ 0) (a : ℕ → ℝ)
    (ha : ∀ n k : ℕ, PowerSeries.coeff (n + 1) (g * (PowerSeries.X * g) ^ (k + 1)) =
      ∑ j ∈ Finset.range (n + 1),
        a j * PowerSeries.coeff n (g * (PowerSeries.X * g) ^ (k + j)))
    (hpf : Matrix.HasNonnegativeMinors (Matrix.lowerToeplitz a)) :
    Matrix.HasNonnegativeMinors
      (Matrix.of fun n k : ℕ => PowerSeries.coeff n (g * (PowerSeries.X * g) ^ k)) := by
  have h0 : constantCoeff (X * g) = 0 := by simp
  have hg' : g ≠ 0 := fun h => hg (by simp [h])
  have hsubst : (mk a).subst (X * g) = g := by
    apply mul_left_cancel₀ hg'
    apply PowerSeries.ext
    intro n
    rw [← riordan_array_sum_eq_coeff_subst g (X * g) (mk a) h0]
    have h := ha n 0
    rw [zero_add, pow_one, mul_left_comm g X g, coeff_succ_X_mul] at h
    simpa only [coeff_mk, Nat.zero_add, mul_comm (a _)] using h.symm
  apply BellRiordan.nonnegativeMinors_of_truncations
  exact BellRiordan.truncation_totallyNonneg g a hsubst
    ((Matrix.hasNonnegativeMinors_iff_isTotallyNonneg _).mp hpf)

end MetaMathlibExt
