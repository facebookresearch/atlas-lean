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
# Total positivity of Riordan arrays

A Riordan array has nonnegative minors if its coefficient matrix does. The proof factors
successive leading truncations as in equation (2.1) of Xi Chen, Huyile Liang and Yi Wang,
[*Total positivity of Riordan arrays*](https://arxiv.org/abs/1601.05637).

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

/-- For a matrix with first row $(1,0,\ldots)$, cofactor expansion reduces total
nonnegativity to the minors omitting that row. -/
private theorem totallyNonneg_of_firstRow {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h00 : M 0 0 = 1) (hrow : ∀ j ≠ 0, M 0 j = 0)
    (below : ∀ {k : ℕ} {r c : Fin k → Fin (N + 1)}, StrictMono r → StrictMono c →
      (∀ i, r i ≠ 0) → 0 ≤ (M.submatrix r c).det) : M.IsTotallyNonneg := by
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
            below (hr.comp Fin.strictMono_succ) (hc.comp Fin.strictMono_succ)
              (fun _ => pos hr (Fin.succ_ne_zero _))
        · intro j _ hj
          simp [hr0, hrow _ (pos hc hj)]
        · simp
      · rw [Matrix.det_eq_zero_of_row_eq_zero 0]
        intro j
        have hj := (Fin.pos_iff_ne_zero.mpr hc0).trans_le (hc.monotone (Fin.zero_le j))
        simpa [hr0] using hrow _ hj.ne'
    · exact below hr hc fun i =>
        ((Fin.pos_iff_ne_zero.mpr hr0).trans_le (hr.monotone (Fin.zero_le i))).ne'

/-- Adjoining a leading unit block preserves nonnegativity of the minors. -/
private theorem totallyNonneg_border {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h00 : M 0 0 = 1) (hrow : ∀ j ≠ 0, M 0 j = 0) (hcol : ∀ i ≠ 0, M i 0 = 0)
    (hM : (M.submatrix Fin.succ Fin.succ).IsTotallyNonneg) : M.IsTotallyNonneg := by
  apply totallyNonneg_of_firstRow M h00 hrow
  intro k r c hr hc hr0
  by_cases hc0 : ∀ j, c j ≠ 0
  · simpa [Matrix.submatrix_submatrix, Function.comp_def] using
      hM (Fin.strictMono_pred_comp hr0 hr) (Fin.strictMono_pred_comp hc0 hc)
  · obtain ⟨j, hj⟩ := not_forall.mp hc0
    rw [Matrix.det_eq_zero_of_column_eq_zero j]
    intro i
    simpa [not_ne_iff.mp hj] using hcol _ (hr0 i)

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

@[expose] public section

/-- **Riordan array with given A- and Z-sequences.** For real sequences $(a_n)_{n \ge 0}$ and
$(z_n)_{n \ge 0}$, an infinite real matrix $R = (r_{n,k})_{n,k \ge 0}$ is the Riordan array with
$A$-sequence $(a_n)$ and $Z$-sequence $(z_n)$ when $r_{0,0} = 1$, $r_{0,k} = 0$ for $k \ge 1$, and
for all $n, k \ge 0$
$$r_{n+1,0} = \sum_{j=0}^{n} z_j\, r_{n,j}, \qquad r_{n+1,k+1} = \sum_{j=0}^{n} a_j\, r_{n,k+j}.$$

The sums stop at $j = n$ because the recurrence forces $r_{n,m} = 0$ for $m > n$.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Section 1, equation (1). -/
def IsRiordanArrayAZ (a z : ℕ → ℝ) (R : ℕ → ℕ → ℝ) : Prop :=
  R 0 0 = 1 ∧ (∀ k, R 0 (k + 1) = 0) ∧
    (∀ n, R (n + 1) 0 = ∑ j ∈ Finset.range (n + 1), z j * R n j) ∧
    ∀ n k, R (n + 1) (k + 1) = ∑ j ∈ Finset.range (n + 1), a j * R n (k + j)

/-- **Entries in row 1 of a Riordan array.** If $R = (r_{n,k})_{n,k \ge 0}$ is the Riordan array
with $A$-sequence $(a_n)$ and $Z$-sequence $(z_n)$, for real sequences $(a_n)$ and $(z_n)$, then
$r_{1,0} = z_0$ and $r_{1,1} = a_0$.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Section 1, equation (1). -/
theorem IsRiordanArrayAZ.one_zero_and_one_one {a z : ℕ → ℝ} {R : ℕ → ℕ → ℝ}
    (h : IsRiordanArrayAZ a z R) : R 1 0 = z 0 ∧ R 1 1 = a 0 := by
  obtain ⟨h00, -, hz, ha⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hz 0]; simp [h00]
  · rw [ha 0 0]; simp [h00]

/-- **Coefficient matrix of a Riordan array.** For real sequences $(z_n)_{n \ge 0}$ and
$(a_n)_{n \ge 0}$ with generating functions $Z(x)$ and $A(x)$, the coefficient matrix
$J(Z(x), A(x))$ is the infinite real matrix, with rows and columns indexed by $n, k \ge 0$, whose
entry in row $n$ and column $k$ is $z_n$ if $k = 0$, is $a_{n+1-k}$ if $1 \le k \le n + 1$, and is
$0$ if $k > n + 1$. Thus row $n$ reads $z_n, a_n, a_{n-1}, \ldots, a_0, 0, 0, \ldots$

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Section 1. -/
def riordanCoeffMatrix (z a : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  Matrix.of fun n k => if k = 0 then z n else if k ≤ n + 1 then a (n + 1 - k) else 0

/-- **First two columns of the coefficient matrix of a Riordan array.** For real sequences
$(z_n)$ and $(a_n)$ with generating functions $Z(x)$ and $A(x)$, and for every $n \ge 0$, the
coefficient matrix $J(Z(x), A(x))$ has entry $z_n$ in row $n$, column $0$, and entry $a_n$ in
row $n$, column $1$.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Section 1. -/
theorem riordanCoeffMatrix_zero_one (z a : ℕ → ℝ) (n : ℕ) :
    riordanCoeffMatrix z a n 0 = z n ∧ riordanCoeffMatrix z a n 1 = a n := by
  simp [riordanCoeffMatrix]

end

namespace Riordan

private theorem entry_eq_zero {a z : ℕ → ℝ} {R : ℕ → ℕ → ℝ} (hR : IsRiordanArrayAZ a z R)
    {n k : ℕ} (hnk : n < k) : R n k = 0 := by
  induction n generalizing k with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnk.ne'
    exact hR.2.1 k
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [hR.2.2.2]
    exact Finset.sum_eq_zero fun j _ => by rw [ih (by omega : n < k + j), mul_zero]

/-- Each row after the first is the preceding row times the coefficient matrix.
The sum can stop at any bound strictly larger than the preceding row index. -/
private theorem row_succ {a z : ℕ → ℝ} {R : ℕ → ℕ → ℝ} (hR : IsRiordanArrayAZ a z R)
    {n N : ℕ} (hn : n < N) (k : ℕ) :
    R (n + 1) k = ∑ j : Fin N, R n j * riordanCoeffMatrix z a j k := by
  rw [Fin.sum_univ_eq_sum_range (fun j => R n j * riordanCoeffMatrix z a j k)]
  cases k with
  | zero =>
    rw [hR.2.2.1]
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono hn)
    · intro j hj
      have hnj : n < j := by simpa using (Finset.mem_sdiff.mp hj).2
      simp [entry_eq_zero hR hnj]
    · simp [riordanCoeffMatrix, mul_comm]
  | succ k =>
    rw [hR.2.2.2]
    have shifted (j : ℕ) : a j * R n (k + j) =
        R n (k + j) * riordanCoeffMatrix z a (k + j) (k + 1) := by
      simp [riordanCoeffMatrix, mul_comm]
    apply Finset.sum_bij_ne_zero (fun j _ _ => k + j)
    · intro j _ hj
      apply Finset.mem_range.mpr
      by_contra! h
      simp [entry_eq_zero hR (hn.trans_le h)] at hj
    · intros
      omega
    · intro i _ hi
      have hki : k ≤ i := by
        by_contra! h
        simp [riordanCoeffMatrix, Nat.not_le.mpr h] at hi
      have hin : i ≤ n := by
        by_contra! h
        simp [entry_eq_zero hR h] at hi
      have heq : k + (i - k) = i := by omega
      refine ⟨i - k, Finset.mem_range.mpr (by omega), ?_, heq⟩
      rwa [shifted, heq]
    · exact fun j _ _ => shifted j

/-- Factor each leading truncation into the unit-bordered previous truncation and the
coefficient matrix with a leading unit row. -/
private theorem truncation_totallyNonneg {a z : ℕ → ℝ} {R : ℕ → ℕ → ℝ}
    (hR : IsRiordanArrayAZ a z R) (hJ : Matrix.HasNonnegativeMinors (riordanCoeffMatrix z a))
    (N : ℕ) : ((Matrix.of R).submatrix (Fin.val (n := N)) Fin.val).IsTotallyNonneg := by
  induction N with
  | zero =>
    convert (Matrix.IsTotallyNonneg.one : (1 : Matrix (Fin 0) (Fin 0) ℝ).IsTotallyNonneg) using 1
    exact Subsingleton.elim _ _
  | succ N ih =>
    let D : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.of fun i j =>
      Fin.cases (if j = 0 then 1 else 0) (fun n => Fin.cases 0 (fun k => R n k) j) i
    let P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.of fun i j =>
      Fin.cases (if j = 0 then 1 else 0) (fun n => riordanCoeffMatrix z a n j) i
    have factor : (Matrix.of R).submatrix (Fin.val (n := N + 1)) Fin.val = D * P := by
      ext i j
      refine Fin.cases ?_ (fun n => ?_) i
      · rw [Matrix.mul_apply, Fin.sum_univ_succ]
        refine Fin.cases ?_ (fun k => ?_) j <;> simp [D, P, hR.1, hR.2.1]
      · rw [Matrix.mul_apply, Fin.sum_univ_succ]
        simpa [D, P] using row_succ hR n.isLt j.val
    rw [factor]
    apply BellRiordan.totallyNonneg_mul
    · apply BellRiordan.totallyNonneg_border
      · simp [D]
      · intro j hj
        simp [D, hj]
      · intro i hi
        obtain ⟨n, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        simp [D]
      · simpa [Matrix.submatrix, D] using ih
    · apply BellRiordan.totallyNonneg_of_firstRow P (by simp [P]) (by simp [P])
      intro k r c hr hc hr0
      have h := hJ k _ _ (Fin.val_strictMono.comp (Fin.strictMono_pred_comp hr0 hr))
        (Fin.val_strictMono.comp hc)
      convert h using 2
      ext i j
      obtain ⟨n, hn⟩ := Fin.exists_succ_eq_of_ne_zero (hr0 i)
      simp [P, Matrix.submatrix_apply, Function.comp_def, ← hn]

end Riordan

/-- **Total positivity of a Riordan array from its coefficient matrix.** Let $(a_n)$ and $(z_n)$
be real sequences with generating functions $A(x)$ and $Z(x)$, and let $R$ be the Riordan array
with $A$-sequence $(a_n)$ and $Z$-sequence $(z_n)$. If the coefficient matrix $J(Z(x), A(x))$ is
totally positive, that is, every minor of it is nonnegative, then every minor of $R$ is
nonnegative.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Proposition 1
(`jis-2025-25.7.5-prop-1`). -/
public theorem riordanArray_hasNonnegativeMinors_of_coeffMatrix {a z : ℕ → ℝ}
    {R : ℕ → ℕ → ℝ} (hR : IsRiordanArrayAZ a z R)
    (hJ : Matrix.HasNonnegativeMinors (riordanCoeffMatrix z a)) :
    Matrix.HasNonnegativeMinors (Matrix.of R) := by
  apply BellRiordan.nonnegativeMinors_of_truncations
  exact Riordan.truncation_totallyNonneg hR hJ

end MetaMathlibExt
