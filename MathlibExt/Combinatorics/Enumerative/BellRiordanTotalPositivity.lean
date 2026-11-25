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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
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

For the Bell-type criterion of Mu, Xing and Zheng, the array factors as a product of two
Bell arrays with Pólya frequency A-sequences.
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

/-- The truncation of the Riordan matrix with columns `d * h ^ k`. -/
private noncomputable def truncation (N : ℕ) (d h : PowerSeries ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun n k => coeff n.val (d * h ^ k.val)

/-- Substitution is matrix multiplication on each leading truncation. -/
private theorem truncation_mul (N : ℕ) (d h e f : PowerSeries ℝ) (h0 : constantCoeff h = 0) :
    truncation N (d * e.subst h) (f.subst h) = truncation N d h * truncation N e f := by
  have hs := HasSubst.of_constantCoeff_zero' h0
  ext n k
  simp only [truncation, Matrix.of_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => coeff n.val (d * h ^ j) * coeff j (e * f ^ k.val))]
  rw [mul_assoc, ← subst_pow hs, ← subst_mul hs, ← riordan_array_sum_eq_coeff_subst _ _ _ h0]
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono n.isLt) _ (by simp)
  intro j hj
  have hnj : n.val < j := by simpa using (Finset.mem_sdiff.mp hj).2
  have hjd : X ^ j ∣ h ^ j := pow_dvd_pow_of_dvd (X_dvd_iff.mpr h0) _
  have hz := X_pow_dvd_iff.mp (dvd_mul_of_dvd_right hjd d) n.val hnj
  simp [hz]

private theorem truncation_X (N : ℕ) (F : PowerSeries ℝ) :
    truncation N F X =
      (Matrix.lowerToeplitz fun n => coeff n F).submatrix Fin.val Fin.val := by
  ext i j
  simp [truncation, coeff_mul_X_pow', Matrix.lowerToeplitz]

/-- Successive square truncations of the array are obtained by adjoining a unit
in the top left corner and multiplying by a Toeplitz truncation. -/
private theorem factor_truncation (g : PowerSeries ℝ) (a : ℕ → ℝ)
    (hsubst : (mk a).subst (X * g) = g) (N : ℕ) :
    (Matrix.of fun n k : Fin N => coeff n.val (g * (X * g) ^ k.val)) =
      (Matrix.of fun n j : Fin N => coeff n.val ((X * g) ^ j.val)) *
        (_root_.Matrix.lowerToeplitz a).submatrix Fin.val Fin.val := by
  have h0 : constantCoeff (X * g) = 0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' h0
  have factor := truncation_mul N 1 (X * g) (mk a) X h0
  rw [hsubst, subst_X hs, one_mul, truncation_X] at factor
  simpa only [truncation, one_mul, coeff_mk] using factor

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

namespace BellRiordan

/-- In a bidiagonal minor only the order-preserving permutation can contribute. -/
private theorem linearFactor_totallyNonneg (u : ℝ) (hu : 0 ≤ u) (N : ℕ) :
    (truncation N (1 + C u * X) X).IsTotallyNonneg := by
  let M := truncation N (1 + C u * X) X
  have entry (i j : Fin N) : M i j =
      (if i.val = j.val then 1 else 0) + (if i.val = j.val + 1 then u else 0) := by
    simp only [M, truncation, Matrix.of_apply, add_mul, one_mul, mul_assoc,
      ← pow_succ', map_add, coeff_X_pow, coeff_C_mul]
    split_ifs <;> simp_all
  intro k rows cols hr hc
  change 0 ≤ (M.submatrix rows cols).det
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin k))]
  · simp only [map_one, one_smul, Equiv.Perm.one_apply, Matrix.submatrix_apply, entry]
    apply Finset.prod_nonneg
    exact fun _ _ => add_nonneg (by split <;> positivity) (by split <;> positivity)
  · intro σ _ hσ
    suffices ∃ i, M (rows (σ i)) (cols i) = 0 by
      obtain ⟨i, hi⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, smul_zero]
    by_contra! h
    have band (i : Fin k) : (rows (σ i)).val = (cols i).val ∨
        (rows (σ i)).val = (cols i).val + 1 := by
      by_contra! hh
      exact h i (by simp [entry, hh.1, hh.2])
    have mono : StrictMono σ := by
      intro i j hij
      have hcij := hc hij
      have le : rows (σ i) ≤ rows (σ j) := by
        change (rows (σ i)).val ≤ (rows (σ j)).val
        have := band i
        have := band j
        omega
      exact lt_of_le_of_ne (hr.le_iff_le.mp le) (σ.injective.ne hij.ne)
    have he := mono.eq_of_range_eq strictMono_id (by simp [σ.surjective.range_eq])
    exact hσ (Equiv.ext fun i => congrFun he i)
  · simp

/-- In a geometric Toeplitz minor, either the top row is supported in the first
column, or two columns are proportional. -/
private theorem geometric_totallyNonneg (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    (truncation N (mk fun n => r ^ n) X).IsTotallyNonneg := by
  rw [truncation_X]
  apply Matrix.IsTotallyNonneg.submatrix _ Fin.val_strictMono Fin.val_strictMono
  simp only [coeff_mk]
  let M := Matrix.lowerToeplitz fun n => r ^ n
  change M.IsTotallyNonneg
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro rows cols hrows hcols
    let D := M.submatrix rows cols
    by_cases h : ∃ j ≠ 0, cols j ≤ rows 0
    · obtain ⟨j, hj, hjr⟩ := h
      have hcol : D.col 0 = r ^ (cols j - cols 0) • D.col j := by
        funext i
        have hji := hjr.trans (hrows.monotone (Fin.zero_le i))
        have h0j := hcols.monotone (Fin.zero_le j)
        change M (rows i) (cols 0) = r ^ _ * M (rows i) (cols j)
        dsimp only [M]
        rw [Matrix.lowerToeplitz_apply_of_le _ (h0j.trans hji),
          Matrix.lowerToeplitz_apply_of_le _ hji, ← pow_add]
        congr 1
        omega
      change 0 ≤ D.det
      rw [← Matrix.updateCol_eq_self D 0]
      change 0 ≤ (D.updateCol 0 (D.col 0)).det
      rw [hcol, Matrix.det_updateCol_smul,
        show (D.updateCol 0 (D.col j)).det = 0 from Matrix.det_updateCol_eq_zero hj, mul_zero]
    · rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
      · simp only [Fin.val_zero, pow_zero, one_mul, Matrix.submatrix_apply,
          Matrix.submatrix_submatrix, Fin.succAbove_zero]
        apply mul_nonneg _ (ih (hrows.comp Fin.strictMono_succ) (hcols.comp Fin.strictMono_succ))
        simp only [M, Matrix.lowerToeplitz]
        split <;> positivity
      · intro j _ hj
        have hz : rows 0 < cols j := lt_of_not_ge fun hle => h ⟨j, hj, hle⟩
        simp [M, hz]
      · simp

/-- The discriminant condition factors the quadratic numerator into two nonnegative
linear factors. The third Toeplitz factor is the geometric series. -/
private theorem exists_parameter_series {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hst : 4 * t ≤ s ^ 2) :
    ∃ B : PowerSeries ℝ, constantCoeff B = 1 ∧
      B * (1 - C r * X) = 1 + C s * X + C t * X ^ 2 ∧
      (Matrix.lowerToeplitz fun n => coeff n B).IsTotallyNonneg := by
  let u := (s + Real.sqrt (s ^ 2 - 4 * t)) / 2
  let v := (s - Real.sqrt (s ^ 2 - 4 * t)) / 2
  have hsq := Real.sq_sqrt (sub_nonneg.mpr hst)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by
    dsimp [v]
    have := Real.sqrt_nonneg (s ^ 2 - 4 * t)
    nlinarith [sq_nonneg (s - Real.sqrt (s ^ 2 - 4 * t))]
  have huv : u * v = t := by dsimp [u, v]; nlinarith
  have hsum : u + v = s := by dsimp [u, v]; ring
  let G : PowerSeries ℝ := mk fun n => r ^ n
  have hG : G * (1 - C r * X) = 1 := by
    rw [mul_sub, mul_one, ← mul_assoc]
    ext n
    cases n with
    | zero => simp [G]
    | succ n => simp [G, coeff_succ_mul_X, coeff_mul_C, pow_succ]
  refine ⟨(1 + C u * X) * (1 + C v * X) * G, ?_, ?_, ?_⟩
  · simp [G]
  · rw [mul_assoc, hG, mul_one, ← hsum, ← huv, map_add, map_mul]
    ring
  · apply (Matrix.hasNonnegativeMinors_iff_isTotallyNonneg _).mp
    apply nonnegativeMinors_of_truncations
    intro N
    rw [← truncation_X]
    have prod (F H : PowerSeries ℝ) : truncation N (F * H) X =
        truncation N F X * truncation N H X := by
      simpa using truncation_mul N F X H X (by simp)
    rw [prod, prod]
    exact totallyNonneg_mul
      (totallyNonneg_mul (linearFactor_totallyNonneg u hu N) (linearFactor_totallyNonneg v hv N))
      (geometric_totallyNonneg r hr N)

/-- Reverting `X / F` gives a solution of the Bell functional equation. -/
private theorem exists_bell_series (F : PowerSeries ℝ) (hF : constantCoeff F ≠ 0) :
    ∃ g : PowerSeries ℝ, F.subst (X * g) = g := by
  let q := X * F⁻¹
  have hq0 : constantCoeff q = 0 := by simp [q]
  have hq1 : IsUnit (coeff 1 q) := by
    simpa [q, coeff_succ_X_mul, coeff_zero_eq_constantCoeff, constantCoeff_inv] using hF
  let f := q.substInvOfIsUnit hq1
  have hf : HasSubst f := HasSubst.substInvOfIsUnit q hq1
  have hinv : q.subst f = X := subst_substInvOfIsUnit_right q hq0 hq1
  have hqF : q * F = X := by simp [q, mul_assoc, hF]
  have h := congrArg (subst f) hqF
  rw [subst_mul hf, hinv, subst_X hf] at h
  exact ⟨F.subst f, by rw [h]⟩

private theorem subst_constant (F g : PowerSeries ℝ) :
    constantCoeff (F.subst (X * g)) = constantCoeff F :=
  constantCoeff_subst_of_constantCoeff_zero (show constantCoeff (X * g) = 0 by simp) F

/-- The AZ recurrence identifies the normalized coefficient array of a Bell series,
including the first column obtained from the shifted coefficients of `A`. -/
private theorem bell_entries (A g : PowerSeries ℝ) (hg : A.subst (X * g) = g)
    {R : ℕ → ℕ → ℝ}
    (hR : IsRiordanArrayAZ (fun n => coeff n A) (fun n => coeff (n + 1) A) R)
    (n k : ℕ) : constantCoeff A * R n k = coeff n (g * (X * g) ^ k) := by
  let f := X * g
  have h0 : constantCoeff f = 0 := by simp [f]
  have hf := HasSubst.of_constantCoeff_zero' h0
  have hg0 : constantCoeff g = constantCoeff A := hg ▸ subst_constant A g
  change constantCoeff A * R n k = coeff n (g * f ^ k)
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [hR.1, coeff_zero_eq_constantCoeff, hg0]
    | succ k => simp [hR.2.1, coeff_zero_eq_constantCoeff, h0]
  | succ n ih =>
    cases k with
    | zero =>
      let Z := mk fun j => coeff (j + 1) A
      have hZ : g = X * (g * Z.subst f) + C (constantCoeff A) := by
        have h := congrArg (subst f) (eq_X_mul_shift_add_const A)
        simpa only [subst_add hf, subst_mul hf, subst_X hf, subst_C, ← C_apply,
          f, hg, mul_assoc, Z] using h
      rw [hR.2.2.1, Finset.mul_sum]
      simp_rw [mul_left_comm (constantCoeff A), ih, mul_comm (coeff (_ + 1) A)]
      simp only [pow_zero, mul_one]
      have hsum := riordan_array_sum_eq_coeff_subst g f Z h0 n
      simp only [Z, coeff_mk] at hsum
      rw [hsum]
      simpa [coeff_succ_X_mul] using (congrArg (coeff (n + 1)) hZ).symm
    | succ k =>
      rw [hR.2.2.2, Finset.mul_sum]
      simp_rw [mul_left_comm (constantCoeff A), ih, pow_add]
      simp_rw [← mul_assoc g (f ^ k), mul_comm (coeff _ A)]
      rw [riordan_array_sum_eq_coeff_subst _ _ _ h0, hg]
      have heq : g * f ^ k * f = X * (g * f ^ k * g) := by
        dsimp [f]
        ring
      rw [pow_one, heq, coeff_succ_X_mul]

/-- Composing the Bell arrays for `B` and `P` gives the Bell series for `A`. -/
private theorem compose_bell_series (P A B p b : PowerSeries ℝ) (hP : constantCoeff P ≠ 0)
    {r s t : ℝ}
    (hA : A * (P - C r * X) = P ^ 2 + C s * X * P + C t * X ^ 2)
    (hB : B * (1 - C r * X) = 1 + C s * X + C t * X ^ 2)
    (hp : P.subst (X * p) = p) (hb : B.subst (X * b) = b) :
    let g := b * p.subst (X * b)
    A.subst (X * g) = g := by
  let y := X * b
  let D := p.subst y
  let f := X * (b * D)
  have hy0 : constantCoeff y = 0 := by simp [y]
  have hy := HasSubst.of_constantCoeff_zero' hy0
  have hf0 : constantCoeff f = 0 := by simp [f]
  have hf := HasSubst.of_constantCoeff_zero' hf0
  have hp0 := HasSubst.of_constantCoeff_zero' (show constantCoeff (X * p) = 0 by simp)
  have hpy : (X * p).subst y = f := by rw [subst_mul hy, subst_X hy]; exact mul_assoc _ _ _
  have hPf : P.subst f = D := by
    rw [← hpy, ← subst_comp_subst_apply hp0 hy P, hp]
  have hD0 : constantCoeff D ≠ 0 := by
    rwa [subst_constant, ← hp, subst_constant]
  have hD : D ≠ 0 := fun he => hD0 (by simp [he])
  have hden : 1 - C r * y ≠ 0 := by
    intro he
    simpa [hy0] using congrArg constantCoeff he
  have hBy := congrArg (substAlgHom hy) hB
  simp only [map_mul, map_sub, map_one, map_add, map_pow, coe_substAlgHom,
    subst_C, ← C_apply, subst_X hy, hb, y] at hBy
  have hAf := congrArg (substAlgHom hf) hA
  simp only [map_mul, map_sub, map_add, map_pow, coe_substAlgHom, subst_C,
    ← C_apply, subst_X hf, hPf] at hAf
  change A.subst f = b * D
  apply mul_right_cancel₀ (mul_ne_zero hD hden)
  have he : f = y * D := (mul_assoc _ _ _).symm
  rw [he] at hAf ⊢
  change b * (1 - C r * y) = 1 + C s * y + C t * y ^ 2 at hBy
  linear_combination hAf - D ^ 2 * hBy

end BellRiordan

open BellRiordan

/-- **Total positivity of Bell-type Riordan arrays from a Pólya frequency series.** Let $P$ and
$A$ be formal power series over $\mathbb{R}$ with $P(0) \ne 0$, write $[x^n]F$ for the
coefficient of $x^n$ in a power series $F$, and let $r, s, t \ge 0$ be real numbers with
$s^2 \ge 4t$. Suppose that $P$ is a Pólya frequency series, that is, every minor of the lower
Toeplitz matrix of its coefficients (whose entry in row $n$ and column $k$ is $[x^{n-k}]P$ for
$k \le n$ and $0$ otherwise) is nonnegative, and that
$$A(x)\,(P(x) - rx) = P(x)^2 + sxP(x) + tx^2.$$
Let $R$ be the Riordan array with $A$-sequence $(a_n)_{n \ge 0}$ and $Z$-sequence
$(z_n)_{n \ge 0}$, where $a_n = [x^n]A$ and $z_n = a_{n+1}$ (a Bell-type Riordan array). Then
$R$ is totally positive: every minor of $R$ is nonnegative.

Since $P(0) \ne 0$, the series $P(x) - rx$ is invertible, so the hypothesis on $A$ says
$A = (P^2 + sxP + tx^2)/(P - rx)$.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Corollary 6
(`jis-2025-25.7.5-cor-6`). -/
public theorem bellRiordanArray_hasNonnegativeMinors_of_pf (P A : PowerSeries ℝ)
    (hP : PowerSeries.constantCoeff P ≠ 0) {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hpf : Matrix.HasNonnegativeMinors (Matrix.lowerToeplitz fun n => PowerSeries.coeff n P))
    (hA : A * (P - PowerSeries.C r * PowerSeries.X) =
      P ^ 2 + PowerSeries.C s * PowerSeries.X * P + PowerSeries.C t * PowerSeries.X ^ 2)
    {R : ℕ → ℕ → ℝ}
    (hR : IsRiordanArrayAZ (fun n => PowerSeries.coeff n A)
      (fun n => PowerSeries.coeff (n + 1) A) R)
    (hst : 4 * t ≤ s ^ 2) :
    Matrix.HasNonnegativeMinors (Matrix.of R) := by
  obtain ⟨B, hB0, hB, hBpf⟩ := exists_parameter_series hr hs ht hst
  obtain ⟨b, hb⟩ := exists_bell_series B (by simp [hB0])
  obtain ⟨p, hp⟩ := exists_bell_series P hP
  let g := b * p.subst (X * b)
  have hg : A.subst (X * g) = g := compose_bell_series P A B p b hP hA hB hp hb
  have hT := (Matrix.hasNonnegativeMinors_iff_isTotallyNonneg _).mp hpf
  have hPpos : 0 < constantCoeff P := by
    exact hP.symm.lt_of_le (by simpa using hT.nonneg 0 0)
  have hA0 : constantCoeff A = constantCoeff P := by
    have h := congrArg constantCoeff hA
    simp at h
    exact mul_right_cancel₀ hP (h.trans (pow_two _))
  apply nonnegativeMinors_of_truncations
  intro N
  have bell (F d : PowerSeries ℝ) (hd : F.subst (X * d) = d)
      (hF : (Matrix.lowerToeplitz fun n => coeff n F).IsTotallyNonneg) :
      (truncation N d (X * d)).IsTotallyNonneg := by
    apply truncation_totallyNonneg d (fun n => coeff n F) _ hF
    rwa [show (mk fun n => coeff n F) = F from PowerSeries.ext fun n => coeff_mk ..]
  have hf : HasSubst (X * b) :=
    HasSubst.of_constantCoeff_zero' (show constantCoeff (X * b) = 0 by simp)
  have factor := truncation_mul N b (X * b) p (X * p) (by simp)
  rw [subst_mul hf, subst_X hf, mul_assoc] at factor
  have hprod : (truncation N g (X * g)).IsTotallyNonneg :=
    factor ▸ totallyNonneg_mul (bell B b hb hBpf) (bell P p hp hT)
  have entries : truncation N g (X * g) =
      constantCoeff A • (Matrix.of R).submatrix Fin.val Fin.val := by
    ext n k
    exact (bell_entries A g hg hR n.val k.val).symm
  rw [entries, Matrix.isTotallyNonneg_smul_iff (hA0 ▸ hPpos : 0 < constantCoeff A)] at hprod
  exact hprod

end MetaMathlibExt
