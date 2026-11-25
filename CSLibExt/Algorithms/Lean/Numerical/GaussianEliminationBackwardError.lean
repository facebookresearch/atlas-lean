/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.LUBackwardError
public import Mathlib.Data.Fin.Rev

/-!
# Backward stability of Gaussian elimination for `A x = b`

Solving `A x = b` by Gaussian elimination factors `A ≈ L̂ Û` (`IsFlLU`), then solves `L̂ y = b`
by forward substitution and `Û x = y` by back substitution, all in floating point. Each
triangular solve is backward stable componentwise: the computed solution solves exactly a
triangular system whose entries are perturbed by at most `γₙ` relative to themselves. Putting the
three steps together, the computed `x̂` solves `(A + F) x̂ = b` with
`|F| ≤ (3 γₙ + γₙ²) |L̂| |Û|` entrywise (J. W. Demmel, Math 221, UC Berkeley, Lecture 5 notes
of 19 September 2024: the corollary "`(A-F)*xhat = b` where `|F| <= 3*n*macheps*P*|L|*|U|`" and
homework 1.11 for the triangular solves, there to first order in `macheps`, with `P = I`).
The exact forms follow N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
SIAM, 2002: the triangular-solve bound `γₙ |T|`, and the GE-solve bound in its usual form
`γ₃ₙ |L̂| |Û|` (`exists_add_mulVec_eq_of_isFlLU_gamma`). The bound `(3 γₙ + γₙ²) |L̂| |Û|` proved
first is slightly stronger, since `3γₙ + γₙ² ≤ γ₃ₙ`, and needs only `n u < 1`.

## Main results

* `IsFlLowerSolve`, `IsFlUpperSolve`: the results of forward and back substitution in floating
  point; back substitution is forward substitution on the index-reversed system.
* `exists_perturbation_of_abs_le`: a residual bounded by `g |M| |x|` is a componentwise
  perturbation `δM` of `M` with `|δM| ≤ g |M|`.
* `exists_add_mulVec_eq_of_isFlLowerSolve`, `exists_add_mulVec_eq_of_isFlUpperSolve`:
  `(L + δL) ŷ = b` with `|δL| ≤ γₙ |L|`, and likewise for `U`.
* `exists_add_mulVec_eq_of_isFlLU`: **backward stability of Gaussian elimination**:
  `(A + F) x̂ = b` with `|F| ≤ (3 γₙ + γₙ²) |L̂| |Û|`.
* `three_mul_gamma_add_sq_le_gamma`, `exists_add_mulVec_eq_of_isFlLU_gamma`: the `γ₃ₙ` form, when
  `3 n u < 1`.

## Cost model

None: these are statements about the values computed, not about the cost of computing them.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint.GaussianEliminationBackwardError

open Finset Cslib.Algorithms.Lean.FloatingPoint Cslib.Algorithms.Lean.FloatingPoint.DotProductError
  Cslib.Algorithms.Lean.FloatingPoint.LUBackwardError

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- **Vector as a sequence.** A vector, padded with zeros. -/
def vecSeq {n : ℕ} (v : Fin n → K) (k : ℕ) : K := if h : k < n then v ⟨k, h⟩ else 0

/-- **Forward substitution in floating point.** `IsFlLowerSolve p L b y` says that `y` is computed
from the lower triangular `L` and `b` by `yᵢ = fl(fl(bᵢ - ∑_{k<i} Lᵢₖ yₖ) / Lᵢᵢ)`, the sum being
evaluated by `subDotFl` (products rounded and subtracted one at a time). -/
def IsFlLowerSolve (p : ℕ) {n : ℕ} (L : Matrix (Fin n) (Fin n) K) (b y : Fin n → K) : Prop :=
  ∀ i, y i = fl p (subDotFl p (b i) (rowSeq L i) (vecSeq y) i / L i i)

/-- **Back substitution in floating point.** `IsFlUpperSolve p U y x` says that `x` is computed
from the upper triangular `U` and `y` by `xᵢ = fl(fl(yᵢ - ∑_{k>i} Uᵢₖ xₖ) / Uᵢᵢ)`, for
`i = n - 1, …, 0`, the sum over `k = n - 1, …, i + 1` being evaluated by `subDotFl`. In other
words, it is forward substitution on the system with rows and columns in reverse order. -/
def IsFlUpperSolve (p : ℕ) {n : ℕ} (U : Matrix (Fin n) (Fin n) K) (y x : Fin n → K) : Prop :=
  IsFlLowerSolve p (fun i k => U i.rev k.rev) (fun i => y i.rev) (fun i => x i.rev)

variable {p : ℕ}

/-- **Residual bound for one division step.** If `ŝ = subDotFl p c a b m` and `ẑ = fl(ŝ / d)`
with `d ≠ 0` and `(m + 1) u < 1`, then
`|c - ∑_{k<m} aₖ bₖ - d ẑ| ≤ γₘ₊₁ (∑_{k<m} |aₖ bₖ| + |d ẑ|)`. -/
theorem abs_sub_sum_sub_mul_le (c d : K) (a b : ℕ → K) (m : ℕ) (hd : d ≠ 0)
    (hm : ((m + 1 : ℕ) : K) * 2 ^ (-(p : ℤ)) < 1) :
    |c - ∑ k ∈ range m, a k * b k - d * fl p (subDotFl p c a b m / d)| ≤
      gamma p (m + 1) *
        (∑ k ∈ range m, |a k * b k| + |d * fl p (subDotFl p c a b m / d)|) := by
  have hu : (0 : K) < 2 ^ (-(p : ℤ)) := two_zpow_pos _
  have hm0 : (m : K) * 2 ^ (-(p : ℤ)) < 1 := by
    have : (m : K) ≤ ((m + 1 : ℕ) : K) := by exact_mod_cast Nat.le_succ m
    nlinarith
  have hu1 : (2 : K) ^ (-(p : ℤ)) < 1 := by
    have : (1 : K) ≤ ((m + 1 : ℕ) : K) := by exact_mod_cast Nat.succ_pos m
    nlinarith
  set s := subDotFl p c a b m
  set z := fl p (s / d)
  set P := ∑ k ∈ range m, |a k * b k|
  set S := ∑ k ∈ range m, a k * b k
  have hP : 0 ≤ P := sum_nonneg fun _ _ => abs_nonneg _
  have hdiv : |d * z - s| ≤ gamma p 1 * |d * z| := by
    have h1 := abs_fl_sub_le_gamma_one_mul hu1 (s / d)
    have : d * z - s = d * (z - s / d) := by field_simp
    rw [this, abs_mul, abs_mul]
    calc |d| * |z - s / d| ≤ |d| * (gamma p 1 * |z|) := by gcongr
      _ = gamma p 1 * (|d| * |z|) := by ring
  have hs : |s| ≤ (1 + gamma p 1) * |d * z| := by
    have := abs_sub_abs_le_abs_sub s (d * z)
    rw [abs_sub_comm] at this
    linarith
  have key := abs_subDotFl_add_sum_sub_le (p := p) c a b m hm0
  have hγm : 0 ≤ (gamma p m : K) := gamma_nonneg hm0
  have hγ1 : 0 ≤ (gamma p 1 : K) := gamma_nonneg (by rw [Nat.cast_one, one_mul]; exact hu1)
  have hprod := one_add_gamma_mul_le (K := K) (p := p) (a := m) (b := 1) hm
  have hdz : 0 ≤ |d * z| := abs_nonneg _
  calc |c - S - d * z| = |(s + S - c) + (d * z - s)| := by
        rw [← abs_neg]; ring_nf
    _ ≤ |s + S - c| + |d * z - s| := abs_add_le _ _
    _ ≤ gamma p m * (P + |s|) + gamma p 1 * |d * z| := by gcongr
    _ ≤ gamma p m * (P + (1 + gamma p 1) * |d * z|) + gamma p 1 * |d * z| := by gcongr
    _ = gamma p m * P + ((1 + gamma p m) * (1 + gamma p 1) - 1) * |d * z| := by ring
    _ ≤ gamma p (m + 1) * P + gamma p (m + 1) * |d * z| := by
        gcongr
        · exact gamma_mono (Nat.le_succ m) hm
        · linarith
    _ = _ := by ring

omit [FloorRing K] in
/-- **Residuals as componentwise perturbations.** If `|rᵢ| ≤ g ∑ₖ |Mᵢₖ| |xₖ|` for every `i`,
then there is `δM` with `|δMᵢₖ| ≤ g |Mᵢₖ|` and `δM x = r`. -/
theorem exists_perturbation_of_abs_le {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (x r : Fin n → K)
    {g : K} (hg : 0 ≤ g) (h : ∀ i, |r i| ≤ g * ∑ k, |M i k| * |x k|) :
    ∃ δM : Matrix (Fin n) (Fin n) K, (∀ i k, |δM i k| ≤ g * |M i k|) ∧ δM.mulVec x = r := by
  classical
  set S : Fin n → K := fun i => ∑ k, |M i k| * |x k|
  have hS : ∀ i, 0 ≤ S i := fun i => sum_nonneg fun _ _ => by positivity
  refine ⟨fun i k => if S i = 0 ∨ x k = 0 then 0 else r i * |M i k| * |x k| / (S i * x k),
    fun i k => ?_, ?_⟩
  · by_cases hik : S i = 0 ∨ x k = 0
    · simp only [hik, ite_true, abs_zero]; positivity
    · simp only [hik, ite_false]
      push Not at hik
      have hSpos : 0 < S i := lt_of_le_of_ne (hS i) (Ne.symm hik.1)
      rw [abs_div, abs_mul, abs_mul, abs_mul, abs_abs, abs_abs, abs_of_pos hSpos]
      rw [div_le_iff₀ (mul_pos hSpos (abs_pos.2 hik.2))]
      have := h i
      calc |r i| * |M i k| * |x k| ≤ (g * S i) * |M i k| * |x k| := by gcongr
        _ = g * |M i k| * (S i * |x k|) := by ring
  · funext i
    simp only [Matrix.mulVec, dotProduct]
    by_cases hSi : S i = 0
    · have hr : r i = 0 := by
        have := h i
        rw [show ∑ k, |M i k| * |x k| = S i from rfl, hSi, mul_zero] at this
        exact abs_nonpos_iff.1 this
      simp [hSi, hr]
    · have hterm : ∀ k, (if S i = 0 ∨ x k = 0 then 0 else
          r i * |M i k| * |x k| / (S i * x k)) * x k = r i / S i * (|M i k| * |x k|) := by
        intro k
        by_cases hxk : x k = 0
        · simp [hxk]
        · simp only [hSi, hxk, or_self, ite_false]
          field_simp
      simp only [hterm, ← mul_sum]
      rw [show ∑ k, |M i k| * |x k| = S i from rfl]
      field_simp

/-- **Backward error of floating-point forward substitution.** If `L` is lower triangular with
nonzero diagonal, `ŷ` is computed by forward substitution in floating point (`IsFlLowerSolve`) and
`n u < 1`, then `(L + δL) ŷ = b` for some `δL` with `|δLᵢₖ| ≤ γₙ |Lᵢₖ|` (Demmel, Math 221
Lecture 5 notes, 2024, recalling homework 1.11, there to first order; exact form as in
N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter on
triangular systems). -/
theorem exists_add_mulVec_eq_of_isFlLowerSolve {n : ℕ} (hn : (n : K) * 2 ^ (-(p : ℤ)) < 1)
    {L : Matrix (Fin n) (Fin n) K} (hL : ∀ i k, i < k → L i k = 0) (hdiag : ∀ i, L i i ≠ 0)
    {b y : Fin n → K} (hy : IsFlLowerSolve p L b y) :
    ∃ δL : Matrix (Fin n) (Fin n) K, (∀ i k, |δL i k| ≤ gamma p n * |L i k|) ∧
      (L + δL).mulVec y = b := by
  have hu : (0 : K) < 2 ^ (-(p : ℤ)) := two_zpow_pos _
  have hγn : 0 ≤ (gamma p n : K) := gamma_nonneg hn
  have hres : ∀ i, |b i - L.mulVec y i| ≤ gamma p n * ∑ k, |L i k| * |y k| := by
    intro i
    set m : ℕ := (i : ℕ)
    have hm : m < n := i.isLt
    have hm1 : ((m + 1 : ℕ) : K) * 2 ^ (-(p : ℤ)) < 1 := by
      have : ((m + 1 : ℕ) : K) ≤ n := by exact_mod_cast hm
      nlinarith
    have hsum := sum_fin_eq_sum_range_add hm (fun k => L i k * y k) fun k hk => by
      simp [hL i k (by exact_mod_cast hk)]
    have habs := sum_fin_eq_sum_range_add hm (fun k => |L i k| * |y k|) fun k hk => by
      simp [hL i k (by exact_mod_cast hk)]
    have hi : (⟨m, hm⟩ : Fin n) = i := rfl
    simp only [hi] at hsum habs
    have hr : ∀ k ∈ range m, (if h : k < n then L i ⟨k, h⟩ * y ⟨k, h⟩ else 0) =
        rowSeq L i k * vecSeq y k := fun k hk => by
      have : k < n := (mem_range.1 hk).trans hm
      simp [rowSeq, vecSeq, this]
    have hra : ∀ k ∈ range m, (if h : k < n then |L i ⟨k, h⟩| * |y ⟨k, h⟩| else 0) =
        |rowSeq L i k * vecSeq y k| := fun k hk => by
      have : k < n := (mem_range.1 hk).trans hm
      simp [rowSeq, vecSeq, this, abs_mul]
    simp only [Matrix.mulVec, dotProduct]
    rw [hsum, habs, sum_congr rfl hr, sum_congr rfl hra, hy i]
    have key := abs_sub_sum_sub_mul_le (p := p) (b i) (L i i) (rowSeq L i) (vecSeq y) m
      (hdiag i) hm1
    have hmono := gamma_mono (K := K) (p := p) (a := m + 1) (b := n) hm hn
    calc |b i - (∑ k ∈ range m, rowSeq L i k * vecSeq y k +
          L i i * fl p (subDotFl p (b i) (rowSeq L i) (vecSeq y) m / L i i))|
        = |b i - ∑ k ∈ range m, rowSeq L i k * vecSeq y k -
            L i i * fl p (subDotFl p (b i) (rowSeq L i) (vecSeq y) m / L i i)| := by ring_nf
      _ ≤ _ := key
      _ ≤ _ := by
          rw [abs_mul]
          gcongr
          exact add_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
  obtain ⟨δL, hδ, hδy⟩ := exists_perturbation_of_abs_le L y (fun i => b i - L.mulVec y i) hγn hres
  refine ⟨δL, hδ, ?_⟩
  rw [Matrix.add_mulVec, hδy]
  funext i
  simp

/-- **Backward error of floating-point back substitution.** If `U` is upper triangular with
nonzero diagonal, `x̂` is computed by back substitution in floating point (`IsFlUpperSolve`) and
`n u < 1`, then `(U + δU) x̂ = y` for some `δU` with `|δUᵢₖ| ≤ γₙ |Uᵢₖ|` (Demmel, Math 221
Lecture 5 notes, 2024, recalling homework 1.11, there to first order; exact form as in
N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter on
triangular systems). -/
theorem exists_add_mulVec_eq_of_isFlUpperSolve {n : ℕ} (hn : (n : K) * 2 ^ (-(p : ℤ)) < 1)
    {U : Matrix (Fin n) (Fin n) K} (hU : ∀ i k, k < i → U i k = 0) (hdiag : ∀ i, U i i ≠ 0)
    {y x : Fin n → K} (hx : IsFlUpperSolve p U y x) :
    ∃ δU : Matrix (Fin n) (Fin n) K, (∀ i k, |δU i k| ≤ gamma p n * |U i k|) ∧
      (U + δU).mulVec x = y := by
  obtain ⟨δ, hδ, hδx⟩ := exists_add_mulVec_eq_of_isFlLowerSolve hn
    (L := fun i k => U i.rev k.rev) (fun i k hik => hU _ _ (Fin.rev_lt_rev.2 hik))
    (fun i => hdiag i.rev) hx
  refine ⟨fun i k => δ i.rev k.rev, fun i k => by simpa using hδ i.rev k.rev, ?_⟩
  funext i
  have := congrFun hδx i.rev
  simp only [Matrix.mulVec, dotProduct, Fin.rev_rev] at this ⊢
  rw [← this]
  refine (Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)).symm
  change (U i.rev.rev k.rev + δ i.rev k) * x k.rev = (U i k.rev + δ i.rev k.rev.rev) * x k.rev
  rw [Fin.rev_rev, Fin.rev_rev]

/-- **Backward stability of Gaussian elimination.** Solve `A x = b` in `p`-bit floating point by
computing `L̂, Û` by Gaussian elimination without pivoting (`IsFlLU`, nonzero pivots), then `ŷ`
by forward substitution with `L̂` and `x̂` by back substitution with `Û`. If `n u < 1`, then
`(A + F) x̂ = b` with `|Fᵢⱼ| ≤ (3 γₙ + γₙ²) ∑ₖ |L̂ᵢₖ| |Ûₖⱼ|` (Demmel, Math 221 Lecture 5 notes,
2024: "`(A-F)*xhat = b` where `|F| <= 3*n*macheps*P*|L|*|U|`", to first order and with
`P = I`). The usual statement has `γ₃ₙ |L̂| |Û|` (N. J. Higham, *Accuracy and Stability of
Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter on LU factorization); since
`3γₙ + γₙ² ≤ γ₃ₙ` the bound here is slightly stronger, and it needs only `n u < 1`. -/
theorem exists_add_mulVec_eq_of_isFlLU {n : ℕ} (hn : (n : K) * 2 ^ (-(p : ℤ)) < 1)
    {A L U : Matrix (Fin n) (Fin n) K} (hLU : IsFlLU p A L U) (hpiv : ∀ j, U j j ≠ 0)
    {b y x : Fin n → K} (hy : IsFlLowerSolve p L b y) (hx : IsFlUpperSolve p U y x) :
    ∃ F : Matrix (Fin n) (Fin n) K, (A + F).mulVec x = b ∧
      ∀ i j, |F i j| ≤ (3 * gamma p n + gamma p n ^ 2) * ∑ k, |L i k| * |U k j| := by
  obtain ⟨E, hE, hEb⟩ := exists_mul_eq_add_abs_le_gamma hn hLU fun j _ => hpiv j
  obtain ⟨δL, hδL, hLy⟩ := exists_add_mulVec_eq_of_isFlLowerSolve hn hLU.L_upper_zero
    (fun i => by rw [hLU.diag_L i]; exact one_ne_zero) hy
  obtain ⟨δU, hδU, hUx⟩ := exists_add_mulVec_eq_of_isFlUpperSolve hn hLU.U_lower_zero hpiv hx
  have hγ : 0 ≤ (gamma p n : K) := gamma_nonneg hn
  refine ⟨E + δL * U + L * δU + δL * δU, ?_, fun i j => ?_⟩
  · have h1 : A + (E + δL * U + L * δU + δL * δU) = (L + δL) * (U + δU) := by
      rw [add_mul, mul_add, mul_add, hE]
      abel
    rw [h1, ← Matrix.mulVec_mulVec, hUx, hLy]
  · simp only [Matrix.add_apply, Matrix.mul_apply]
    set T := ∑ k, |L i k| * |U k j|
    have hT : 0 ≤ T := sum_nonneg fun _ _ => by positivity
    have h2 : |∑ k, δL i k * U k j| ≤ gamma p n * T := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun k _ => ?_
      rw [abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hδL i k) (abs_nonneg _)
    have h3 : |∑ k, L i k * δU k j| ≤ gamma p n * T := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun k _ => ?_
      rw [abs_mul]
      calc |L i k| * |δU k j| ≤ |L i k| * (gamma p n * |U k j|) := by gcongr; exact hδU k j
        _ = _ := by ring
    have h4 : |∑ k, δL i k * δU k j| ≤ gamma p n ^ 2 * T := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun k _ => ?_
      rw [abs_mul]
      calc |δL i k| * |δU k j| ≤ (gamma p n * |L i k|) * (gamma p n * |U k j|) := by
            gcongr
            · exact hδL i k
            · exact hδU k j
        _ = _ := by ring
    have h1 := hEb i j
    calc |E i j + ∑ k, δL i k * U k j + ∑ k, L i k * δU k j + ∑ k, δL i k * δU k j|
        ≤ |E i j| + |∑ k, δL i k * U k j| + |∑ k, L i k * δU k j| +
            |∑ k, δL i k * δU k j| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ gamma p n * T + gamma p n * T + gamma p n * T + gamma p n ^ 2 * T := by gcongr
      _ = (3 * gamma p n + gamma p n ^ 2) * T := by ring

/-- **`3γₙ + γₙ² ≤ γ₃ₙ`** when `3 n u < 1`. -/
theorem three_mul_gamma_add_sq_le_gamma {n : ℕ} (hn : ((3 * n : ℕ) : K) * 2 ^ (-(p : ℤ)) < 1) :
    3 * gamma p n + gamma p n ^ 2 ≤ (gamma p (3 * n) : K) := by
  have hu : (0 : K) < 2 ^ (-(p : ℤ)) := two_zpow_pos _
  have h3 : ((3 * n : ℕ) : K) = 3 * n := by push_cast; ring
  have hn0 : (0 : K) ≤ n := Nat.cast_nonneg n
  have h1 : (n : K) * 2 ^ (-(p : ℤ)) < 1 := by rw [h3] at hn; nlinarith
  have h2 : ((n + n : ℕ) : K) * 2 ^ (-(p : ℤ)) < 1 := by push_cast; rw [h3] at hn; nlinarith
  have h3' : ((n + n + n : ℕ) : K) * 2 ^ (-(p : ℤ)) < 1 := by
    have : (n + n + n : ℕ) = 3 * n := by ring
    rw [this]; exact hn
  have hγ : 0 ≤ (gamma p n : K) := gamma_nonneg h1
  have hA := one_add_gamma_mul_le (K := K) (p := p) (a := n) (b := n) h2
  have hB := one_add_gamma_mul_le (K := K) (p := p) (a := n + n) (b := n) h3'
  have hγ2 : 0 ≤ (gamma p (n + n) : K) := gamma_nonneg (by push_cast at h2 ⊢; linarith)
  have : (n + n + n : ℕ) = 3 * n := by ring
  rw [this] at hB
  nlinarith [mul_le_mul_of_nonneg_right hA (by linarith : (0 : K) ≤ 1 + gamma p n),
    mul_nonneg hγ hγ, mul_nonneg (mul_nonneg hγ hγ) hγ]

/-- **Backward stability of Gaussian elimination, `γ₃ₙ` form.** Under the hypotheses of
`exists_add_mulVec_eq_of_isFlLU` and `3 n u < 1`, `(A + F) x̂ = b` with
`|Fᵢⱼ| ≤ γ₃ₙ ∑ₖ |L̂ᵢₖ| |Ûₖⱼ|`, the form in which the bound is usually stated (N. J. Higham,
*Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter on LU
factorization). -/
theorem exists_add_mulVec_eq_of_isFlLU_gamma {n : ℕ}
    (hn : ((3 * n : ℕ) : K) * 2 ^ (-(p : ℤ)) < 1)
    {A L U : Matrix (Fin n) (Fin n) K} (hLU : IsFlLU p A L U) (hpiv : ∀ j, U j j ≠ 0)
    {b y x : Fin n → K} (hy : IsFlLowerSolve p L b y) (hx : IsFlUpperSolve p U y x) :
    ∃ F : Matrix (Fin n) (Fin n) K, (A + F).mulVec x = b ∧
      ∀ i j, |F i j| ≤ gamma p (3 * n) * ∑ k, |L i k| * |U k j| := by
  have hu : (0 : K) < 2 ^ (-(p : ℤ)) := two_zpow_pos _
  have hn1 : (n : K) * 2 ^ (-(p : ℤ)) < 1 := by
    have : ((3 * n : ℕ) : K) = 3 * n := by push_cast; ring
    have hn0 : (0 : K) ≤ n := Nat.cast_nonneg n
    rw [this] at hn; nlinarith
  obtain ⟨F, hF, hFb⟩ := exists_add_mulVec_eq_of_isFlLU hn1 hLU hpiv hy hx
  refine ⟨F, hF, fun i j => (hFb i j).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (three_mul_gamma_add_sq_le_gamma hn)
    (Finset.sum_nonneg fun _ _ => by positivity)

end Cslib.Algorithms.Lean.FloatingPoint.GaussianEliminationBackwardError
