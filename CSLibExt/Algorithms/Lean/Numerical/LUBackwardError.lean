/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.DotProductError
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Floating-point LU factorization (Doolittle, no pivoting)

The factors that Gaussian elimination without pivoting computes in floating point, as a
predicate. In exact arithmetic `A = L U` with `L` unit lower triangular and `U` upper triangular
gives, entry by entry (Doolittle's formulas),

* `U(i, j) = A(i, j) - ∑_{k<i} L(i, k) U(k, j)` for `i ≤ j`,
* `L(i, j) = (A(i, j) - ∑_{k<j} L(i, k) U(k, j)) / U(j, j)` for `i > j`,

and the algorithm evaluates these sums by subtracting the rounded products one at a time,
rounding every operation (J. W. Demmel, Math 221, UC Berkeley, Lecture 5 notes of 19 September
2024, proof of the backward error analysis of LU decomposition, with `P = I`). `IsFlLU p A L U`
says that `L` and `U` are the factors so computed with `p`-bit round to nearest
(`Cslib.Algorithms.Lean.FloatingPoint.fl`). The recurrences determine `L` and `U` from `A`;
the predicate avoids writing the well-founded recursion.

## Main results

* `IsFlLU`: the computed factors, with `subDotFl` for the floating-point `c - ∑ aₖ bₖ`.
* `abs_subDotFl_add_sum_sub_le`: `|ŝ + ∑_{k<m} aₖ bₖ - c| ≤ γₘ (∑ |aₖ bₖ| + |ŝ|)` for the
  computed `ŝ`, the error being measured against the computed result.
* `exists_mul_eq_add_abs_le_gamma`: **the backward error theorem** `L̂ Û = A + E` with
  `|E| ≤ γₙ |L̂| |Û|` entrywise.

The proof follows the classical argument: each Doolittle formula is an instance of
`abs_subDotFl_add_sum_sub_le`, with one more rounding, for the division by the pivot, in the
entries of `L̂`; the composition `(1 + γₘ)(1 + γ₁) ≤ 1 + γₘ₊₁` absorbs it.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint.LUBackwardError

open Finset Cslib.Algorithms.Lean.FloatingPoint Cslib.Algorithms.Lean.FloatingPoint.DotProductError

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- **Floating-point evaluation of `c - ∑_{k<m} aₖ bₖ`.** Starting from `s₀ = c`, subtract the
rounded products from left to right, rounding each subtraction:
`sₖ₊₁ = fl(sₖ - fl(aₖ bₖ))`. -/
def subDotFl (p : ℕ) (c : K) (a b : ℕ → K) : ℕ → K
  | 0 => c
  | k + 1 => fl p (subDotFl p c a b k - fl p (a k * b k))

/-- **Row of a matrix as a sequence.** Row `i` of a square matrix, padded with zeros. -/
def rowSeq {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (i : Fin n) (k : ℕ) : K :=
  if h : k < n then M i ⟨k, h⟩ else 0

/-- **Column of a matrix as a sequence.** Column `j` of a square matrix, padded with zeros. -/
def colSeq {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (j : Fin n) (k : ℕ) : K :=
  if h : k < n then M ⟨k, h⟩ j else 0

/-- **Factors computed by floating-point Gaussian elimination without pivoting.**
`IsFlLU p A L U` holds when `L` is unit lower triangular, `U` is upper triangular, and their
entries satisfy Doolittle's formulas evaluated in `p`-bit floating point:
`U(i, j) = fl(A(i, j) - ∑_{k<i} L(i, k) U(k, j))` for `i ≤ j` and
`L(i, j) = fl(fl(A(i, j) - ∑_{k<j} L(i, k) U(k, j)) / U(j, j))` for `i > j`, each sum
evaluated by `subDotFl` (Demmel, Math 221 Lecture 5 notes, 2024). -/
structure IsFlLU (p : ℕ) {n : ℕ} (A L U : Matrix (Fin n) (Fin n) K) : Prop where
  diag_L : ∀ i, L i i = 1
  L_upper_zero : ∀ i j, i < j → L i j = 0
  U_lower_zero : ∀ i j, j < i → U i j = 0
  U_eq : ∀ i j, i ≤ j → U i j = subDotFl p (A i j) (rowSeq L i) (colSeq U j) i
  L_eq : ∀ i j, j < i →
    L i j = fl p (subDotFl p (A i j) (rowSeq L i) (colSeq U j) j / U j j)

omit [IsStrictOrderedRing K] in
/-- **Floating-point LU of a `1 × 1` matrix.** A `1 × 1` matrix `(a)` is factored as
`(1) (a)`, exactly. -/
theorem isFlLU_one_by_one (p : ℕ) (a : K) :
    IsFlLU p (fun _ _ : Fin 1 => a) (fun _ _ => 1) (fun _ _ => a) where
  diag_L _ := rfl
  L_upper_zero i j h := absurd h (by omega)
  U_lower_zero i j h := absurd h (by omega)
  U_eq i j _ := by simp [subDotFl]
  L_eq i j h := absurd h (by omega)

/-! ## The backward error theorem -/

section Gamma

variable {p : ℕ}

omit [FloorRing K] in
/-- `1 + γₖ = 1 / (1 - k u)`. -/
private theorem one_add_gamma {k : ℕ} (hk : (k : K) * 2 ^ (-(p : ℤ)) < 1) :
    1 + (gamma p k : K) = 1 / (1 - k * 2 ^ (-(p : ℤ))) := by
  unfold gamma
  have hd : (1 : K) - k * 2 ^ (-(p : ℤ)) ≠ 0 := by linarith
  field_simp
  ring

/-- **Composition of relative errors.** `(1 + γₐ)(1 + γ_b) ≤ 1 + γ_{a+b}` when `(a + b) u < 1`. -/
theorem one_add_gamma_mul_le {a b : ℕ} (h : ((a + b : ℕ) : K) * 2 ^ (-(p : ℤ)) < 1) :
    (1 + (gamma p a : K)) * (1 + gamma p b) ≤ 1 + gamma p (a + b) := by
  have hu : (0 : K) < 2 ^ (-(p : ℤ)) := two_zpow_pos _
  have ha0 : (0 : K) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : K) ≤ b := Nat.cast_nonneg b
  push_cast at h
  have ha : (a : K) * 2 ^ (-(p : ℤ)) < 1 := by nlinarith
  have hb : (b : K) * 2 ^ (-(p : ℤ)) < 1 := by nlinarith
  rw [one_add_gamma ha, one_add_gamma hb, one_add_gamma (by push_cast; exact h)]
  push_cast
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg ha0 hb0) (mul_pos hu hu).le]

/-- **Monotonicity of `γ`.** `γₐ ≤ γ_b` for `a ≤ b` when `b u < 1`. -/
theorem gamma_mono {a b : ℕ} (hab : a ≤ b) (hb : (b : K) * 2 ^ (-(p : ℤ)) < 1) :
    (gamma p a : K) ≤ gamma p b := by
  have hu : (0 : K) < 2 ^ (-(p : ℤ)) := two_zpow_pos _
  have hab' : (a : K) ≤ b := by exact_mod_cast hab
  have ha : (a : K) * 2 ^ (-(p : ℤ)) < 1 := by nlinarith
  have h1 := one_add_gamma ha
  have h2 := one_add_gamma hb
  have : 1 / (1 - (a : K) * 2 ^ (-(p : ℤ))) ≤ 1 / (1 - b * 2 ^ (-(p : ℤ))) :=
    one_div_le_one_div_of_le (by linarith) (by nlinarith)
  linarith

/-- **Rounding error relative to the rounded value.** `|fl x - x| ≤ γ₁ |fl x|` when `u < 1`. -/
theorem abs_fl_sub_le_gamma_one_mul (h : (2 : K) ^ (-(p : ℤ)) < 1) (x : K) :
    |fl p x - x| ≤ gamma p 1 * |fl p x| := by
  have hu : (0 : K) < 2 ^ (-(p : ℤ)) := two_zpow_pos _
  have h0 := abs_fl_sub_le (p := p) x
  have hx : |x| ≤ |fl p x| + |fl p x - x| := by
    have := abs_sub_abs_le_abs_sub x (fl p x)
    rw [abs_sub_comm] at this
    linarith
  have key : (1 - 2 ^ (-(p : ℤ))) * |fl p x - x| ≤ 2 ^ (-(p : ℤ)) * |fl p x| := by nlinarith
  unfold gamma
  push_cast
  rw [one_mul, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

end Gamma

variable {p : ℕ}

/-- **Error of a floating-point `c - ∑ aₖ bₖ`, measured by the result.** If `m u < 1`, the value
`ŝ = subDotFl p c a b m` satisfies `|ŝ + ∑_{k<m} aₖ bₖ - c| ≤ γₘ (∑_{k<m} |aₖ bₖ| + |ŝ|)`. -/
theorem abs_subDotFl_add_sum_sub_le (c : K) (a b : ℕ → K) (m : ℕ)
    (hm : (m : K) * 2 ^ (-(p : ℤ)) < 1) :
    |subDotFl p c a b m + ∑ k ∈ range m, a k * b k - c| ≤
      gamma p m * (∑ k ∈ range m, |a k * b k| + |subDotFl p c a b m|) := by
  induction m with
  | zero => simp [subDotFl, gamma]
  | succ k ih =>
    set u : K := 2 ^ (-(p : ℤ)) with hu_def
    have hu : 0 < u := two_zpow_pos _
    have hk : (k : K) * u < 1 := by
      have : (k : K) ≤ ((k + 1 : ℕ) : K) := by exact_mod_cast Nat.le_succ k
      nlinarith
    have hu1 : u < 1 := by
      have : (1 : K) ≤ ((k + 1 : ℕ) : K) := by exact_mod_cast Nat.succ_pos k
      nlinarith
    have ih := ih hk
    set s := subDotFl p c a b k
    set q := a k * b k
    set P := ∑ i ∈ range k, |a i * b i|
    set D := s + ∑ i ∈ range k, a i * b i - c
    set α := fl p q - q with hα_def
    set s' := fl p (s - fl p q) with hs'_def
    set β := s' - (s - fl p q) with hβ_def
    have hα : |α| ≤ u * |q| := abs_fl_sub_le q
    have hβ : |β| ≤ gamma p 1 * |s'| := abs_fl_sub_le_gamma_one_mul hu1 _
    have hγk : 0 ≤ (gamma p k : K) := gamma_nonneg hk
    have hγ1 : 0 ≤ (gamma p 1 : K) := gamma_nonneg (by rw [Nat.cast_one, one_mul]; exact hu1)
    have hP : 0 ≤ P := sum_nonneg fun _ _ => abs_nonneg _
    have hsucc : subDotFl p c a b (k + 1) = s' := rfl
    have hD : s' + ∑ i ∈ range (k + 1), a i * b i - c = D - α + β := by
      rw [sum_range_succ, hβ_def, hα_def]
      ring
    have hs : |s| ≤ (1 + gamma p 1) * |s'| + (1 + u) * |q| := by
      have : s = s' + q + α - β := by rw [hβ_def, hα_def]; ring
      rw [this]
      calc |s' + q + α - β| ≤ |s'| + |q| + |α| + |β| := by
            refine (abs_sub _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ |s'| + |q| + u * |q| + gamma p 1 * |s'| := by gcongr
        _ = _ := by ring
    have hstep := gamma_step (K := K) (p := p) (k := k) (by push_cast at hm; linarith)
    have hprod := one_add_gamma_mul_le (K := K) (p := p) (a := k) (b := 1) hm
    rw [hsucc, hD, sum_range_succ]
    calc |D - α + β| ≤ |D| + |α| + |β| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ gamma p k * (P + |s|) + u * |q| + gamma p 1 * |s'| := by gcongr
      _ ≤ gamma p k * (P + ((1 + gamma p 1) * |s'| + (1 + u) * |q|)) + u * |q| +
            gamma p 1 * |s'| := by gcongr
      _ = gamma p k * P + (u + (1 + u) * gamma p k) * |q| +
            ((1 + gamma p k) * (1 + gamma p 1) - 1) * |s'| := by ring
      _ ≤ gamma p (k + 1) * P + gamma p (k + 1) * |q| + gamma p (k + 1) * |s'| := by
          gcongr
          · exact gamma_mono (Nat.le_succ k) hm
          · linarith
      _ = gamma p (k + 1) * (P + |a k * b k| + |s'|) := by ring

omit [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] in
/-- **Splitting a sum at its last nonzero term.** A sum over `Fin n` whose terms vanish beyond
index `m < n` is the sum of the zero-padded terms below `m` plus the term at `m`. -/
theorem sum_fin_eq_sum_range_add {n m : ℕ} (hm : m < n) (f : Fin n → K)
    (hf : ∀ k : Fin n, m < (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k ∈ range m, (if h : k < n then f ⟨k, h⟩ else 0) + f ⟨m, hm⟩ := by
  set g : ℕ → K := fun k => if h : k < n then f ⟨k, h⟩ else 0
  have h1 : ∑ k, f k = ∑ k ∈ range n, g k := by
    rw [← Fin.sum_univ_eq_sum_range g n]
    refine sum_congr rfl fun k _ => ?_
    simp [g, k.isLt]
  have h2 : ∑ k ∈ range n, g k = ∑ k ∈ range (m + 1), g k := by
    refine (sum_subset (range_subset_range.2 (by omega)) fun k hk hk' => ?_).symm
    simp only [mem_range, not_lt] at hk hk'
    simp only [g, hk, dite_true]
    exact hf ⟨k, hk⟩ (by simp; omega)
  rw [h1, h2, sum_range_succ]
  simp [g, hm]

/-- **Backward error of floating-point LU factorization.** Let `L̂` and `Û` be the factors of an
`n × n` matrix `A` computed by Gaussian elimination without pivoting in `p`-bit floating point
(`IsFlLU`), with nonzero pivots `Û(j, j)` for `j < n - 1` (the last pivot is never divided by),
and let `n u < 1` for `u = 2^(-p)`. Then
`L̂ Û = A + E` with `|E(i, j)| ≤ γₙ ∑ₖ |L̂(i, k)| |Û(k, j)|` for all `i, j` (J. W. Demmel,
Math 221, UC Berkeley, Lecture 5 notes, 2024: "If P, L and U are computed by the above algorithm,
then `A - E = P*L*U` where `|E| <= n*macheps*P*|L|*|U|`", stated there to first order in
`macheps`, for `P = I`; the exact `γₙ` form is the one of N. J. Higham, *Accuracy and Stability of
Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter on LU
factorization). -/
theorem exists_mul_eq_add_abs_le_gamma {n : ℕ} (hn : (n : K) * 2 ^ (-(p : ℤ)) < 1)
    {A L U : Matrix (Fin n) (Fin n) K} (hLU : IsFlLU p A L U)
    (hpiv : ∀ j : Fin n, (j : ℕ) + 1 < n → U j j ≠ 0) :
    ∃ E : Matrix (Fin n) (Fin n) K, L * U = A + E ∧
      ∀ i j, |E i j| ≤ gamma p n * ∑ k, |L i k| * |U k j| := by
  have hu : (0 : K) < 2 ^ (-(p : ℤ)) := two_zpow_pos _
  refine ⟨L * U - A, by abel, fun i j => ?_⟩
  have hcast : ∀ m : ℕ, m < n → (m : K) * 2 ^ (-(p : ℤ)) < 1 := fun m hm => by
    have : (m : K) ≤ n := by exact_mod_cast hm.le
    nlinarith
  have hcast1 : ∀ m : ℕ, m < n → ((m + 1 : ℕ) : K) * 2 ^ (-(p : ℤ)) < 1 := fun m hm => by
    have : ((m + 1 : ℕ) : K) ≤ n := by exact_mod_cast hm
    nlinarith
  have hγn : 0 ≤ (gamma p n : K) := gamma_nonneg hn
  rw [Matrix.sub_apply, Matrix.mul_apply]
  rcases le_or_gt i j with hij | hji
  · -- an entry of `U`: `m = i`
    set m : ℕ := (i : ℕ)
    have hm : m < n := i.isLt
    have hsum := sum_fin_eq_sum_range_add hm (fun k => L i k * U k j) fun k hk => by
      simp [hLU.L_upper_zero i k (by exact_mod_cast hk)]
    have habs := sum_fin_eq_sum_range_add hm (fun k => |L i k| * |U k j|) fun k hk => by
      simp [hLU.L_upper_zero i k (by exact_mod_cast hk)]
    have hi : (⟨m, hm⟩ : Fin n) = i := rfl
    simp only [hi, hLU.diag_L i, one_mul, abs_one] at hsum habs
    rw [hsum, habs, hLU.U_eq i j hij]
    have hr : ∀ k ∈ range m, (if h : k < n then L i ⟨k, h⟩ * U ⟨k, h⟩ j else 0) =
        rowSeq L i k * colSeq U j k := fun k hk => by
      have : k < n := (mem_range.1 hk).trans hm
      simp [rowSeq, colSeq, this]
    have hra : ∀ k ∈ range m, (if h : k < n then |L i ⟨k, h⟩| * |U ⟨k, h⟩ j| else 0) =
        |rowSeq L i k * colSeq U j k| := fun k hk => by
      have : k < n := (mem_range.1 hk).trans hm
      simp [rowSeq, colSeq, this, abs_mul]
    rw [sum_congr rfl hr, sum_congr rfl hra]
    have key := abs_subDotFl_add_sum_sub_le (p := p) (A i j) (rowSeq L i) (colSeq U j) m
      (hcast m hm)
    have hmono := gamma_mono (K := K) (p := p) hm.le hn
    calc |∑ k ∈ range m, rowSeq L i k * colSeq U j k +
          subDotFl p (A i j) (rowSeq L i) (colSeq U j) m - A i j|
        = |subDotFl p (A i j) (rowSeq L i) (colSeq U j) m +
            ∑ k ∈ range m, rowSeq L i k * colSeq U j k - A i j| := by ring_nf
      _ ≤ _ := key
      _ ≤ _ := by
          gcongr
          exact add_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)
  · -- an entry of `L`: `m = j`
    set m : ℕ := (j : ℕ)
    have hm : m < n := j.isLt
    have hsum := sum_fin_eq_sum_range_add hm (fun k => L i k * U k j) fun k hk => by
      simp [hLU.U_lower_zero k j (by exact_mod_cast hk)]
    have habs := sum_fin_eq_sum_range_add hm (fun k => |L i k| * |U k j|) fun k hk => by
      simp [hLU.U_lower_zero k j (by exact_mod_cast hk)]
    have hj : (⟨m, hm⟩ : Fin n) = j := rfl
    simp only [hj] at hsum habs
    rw [hsum, habs]
    have hr : ∀ k ∈ range m, (if h : k < n then L i ⟨k, h⟩ * U ⟨k, h⟩ j else 0) =
        rowSeq L i k * colSeq U j k := fun k hk => by
      have : k < n := (mem_range.1 hk).trans hm
      simp [rowSeq, colSeq, this]
    have hra : ∀ k ∈ range m, (if h : k < n then |L i ⟨k, h⟩| * |U ⟨k, h⟩ j| else 0) =
        |rowSeq L i k * colSeq U j k| := fun k hk => by
      have : k < n := (mem_range.1 hk).trans hm
      simp [rowSeq, colSeq, this, abs_mul]
    rw [sum_congr rfl hr, sum_congr rfl hra]
    set sj := subDotFl p (A i j) (rowSeq L i) (colSeq U j) m
    set P := ∑ k ∈ range m, |rowSeq L i k * colSeq U j k|
    set S := ∑ k ∈ range m, rowSeq L i k * colSeq U j k
    have hP : 0 ≤ P := sum_nonneg fun _ _ => abs_nonneg _
    have hLij : L i j = fl p (sj / U j j) := hLU.L_eq i j hji
    have hm1 : m + 1 < n := by
      have : (j : ℕ) < i := hji
      omega
    have hu1 : (2 : K) ^ (-(p : ℤ)) < 1 := by
      have := hcast 1 (by omega)
      simpa using this
    -- the division rounding, measured by the result
    have hdiv : |L i j * U j j - sj| ≤ gamma p 1 * (|L i j| * |U j j|) := by
      have h1 := abs_fl_sub_le_gamma_one_mul hu1 (sj / U j j)
      rw [← hLij] at h1
      have : L i j * U j j - sj = (L i j - sj / U j j) * U j j := by
        field_simp [hpiv j (by omega)]
      rw [this, abs_mul]
      calc |L i j - sj / U j j| * |U j j| ≤ gamma p 1 * |L i j| * |U j j| := by gcongr
        _ = _ := by ring
    have hsj : |sj| ≤ (1 + gamma p 1) * (|L i j| * |U j j|) := by
      have : |sj| ≤ |L i j * U j j| + |L i j * U j j - sj| := by
        have := abs_sub_abs_le_abs_sub sj (L i j * U j j)
        rw [abs_sub_comm (L i j * U j j) sj] at hdiv
        linarith [abs_sub_comm sj (L i j * U j j)]
      rw [abs_mul] at this
      linarith
    have key := abs_subDotFl_add_sum_sub_le (p := p) (A i j) (rowSeq L i) (colSeq U j) m
      (hcast m hm)
    have hγm : 0 ≤ (gamma p m : K) := gamma_nonneg (hcast m hm)
    have hγ1 : 0 ≤ (gamma p 1 : K) := gamma_nonneg (by simpa using hu1)
    have hprod := one_add_gamma_mul_le (K := K) (p := p) (a := m) (b := 1) (hcast1 m (by omega))
    have hmono := gamma_mono (K := K) (p := p) (a := m + 1) (b := n) hm1.le hn
    have hLU0 : 0 ≤ |L i j| * |U j j| := by positivity
    calc |S + L i j * U j j - A i j| = |(sj + S - A i j) + (L i j * U j j - sj)| := by ring_nf
      _ ≤ |sj + S - A i j| + |L i j * U j j - sj| := abs_add_le _ _
      _ ≤ gamma p m * (P + |sj|) + gamma p 1 * (|L i j| * |U j j|) := by gcongr
      _ ≤ gamma p m * (P + (1 + gamma p 1) * (|L i j| * |U j j|)) +
            gamma p 1 * (|L i j| * |U j j|) := by gcongr
      _ = gamma p m * P + ((1 + gamma p m) * (1 + gamma p 1) - 1) * (|L i j| * |U j j|) := by
          ring
      _ ≤ gamma p n * P + gamma p n * (|L i j| * |U j j|) := by
          gcongr
          · exact gamma_mono (by omega) hn
          · linarith
      _ = gamma p n * (P + |L i j| * |U j j|) := by ring

end Cslib.Algorithms.Lean.FloatingPoint.LUBackwardError
