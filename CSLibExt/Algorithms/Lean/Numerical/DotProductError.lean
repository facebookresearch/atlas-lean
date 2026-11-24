/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Rounding error analysis of dot products and matrix multiplication

In the floating-point model of `Cslib.Algorithms.Lean.FloatingPoint` (round to nearest, ties to
even, `p`-bit significands, unbounded exponent), every operation satisfies
`fl(a op b) = (a op b)(1 + δ)` with `|δ| ≤ u = 2^(-p)`. Error analysis builds every result of
numerical linear algebra from this model, starting with the dot product. Summing the rounded
products `fl(xᵢ yᵢ)` from left to right in floating point,

`|fl(∑ xᵢ yᵢ) - ∑ xᵢ yᵢ| ≤ γₙ ∑ |xᵢ yᵢ|`,  `γₙ = n u / (1 - n u)`,  whenever `n u < 1`.

Applied entrywise, the classical floating-point product `Ĉ = fl(A B)` of an `m × n` and an
`n × r` matrix satisfies `|Ĉ - A B| ≤ γₙ |A| |B|` entrywise. J. W. Demmel's Math 221 course
(UC Berkeley, Lecture 5 notes of 19 September 2024, recalling homework 1.10) uses this bound,
in its first-order form `n ε |A| |B|`, as the model for the backward error analysis of LU
factorization. The exact `γₙ` forms proved here are the standard ones of
N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.

## Main results

* `gamma`: `γₙ = n u / (1 - n u)`, with `gamma_step` (`u + (1 + u) γₖ ≤ γₖ₊₁`).
* `dotFl`: the floating-point dot product, accumulated from left to right.
* `abs_dotFl_sub_le`: the forward error bound above.
* `matMulFl`, `abs_matMulFl_sub_le`: the floating-point matrix product and its entrywise bound.

## Cost model

None: these are statements about the values computed, not about the cost of computing them.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint.DotProductError

open Finset Cslib.Algorithms.Lean.FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable (p : ℕ)

/-- **The constant `γₙ` of rounding error analysis.** With the unit roundoff `u = 2^(-p)`,
`γₙ = n u / (1 - n u)`; it bounds the accumulated relative error of `n` roundings when
`n u < 1`. -/
def gamma (n : ℕ) : K := n * 2 ^ (-(p : ℤ)) / (1 - n * 2 ^ (-(p : ℤ)))

/-- **Floating-point dot product.** `dotFl p x y n` sums the rounded products `fl(xᵢ yᵢ)`,
`i = 0, …, n - 1`, from left to right, rounding after each addition: `s₀ = 0` and
`sₖ₊₁ = fl(sₖ + fl(xₖ yₖ))`. -/
def dotFl (x y : ℕ → K) : ℕ → K
  | 0 => 0
  | k + 1 => fl p (dotFl x y k + fl p (x k * y k))

variable {p}

/-- **Growth of `γ` by one rounding.** `u + (1 + u) γₖ ≤ γₖ₊₁` when `(k + 1) u < 1`. -/
theorem gamma_step {k : ℕ} (hk : ((k : K) + 1) * 2 ^ (-(p : ℤ)) < 1) :
    2 ^ (-(p : ℤ)) + (1 + 2 ^ (-(p : ℤ))) * gamma p k ≤ (gamma p (k + 1) : K) := by
  unfold gamma
  generalize hu : (2 : K) ^ (-(p : ℤ)) = u at hk ⊢
  have hu0 : 0 < u := hu ▸ two_zpow_pos _
  have hk0 : (0 : K) ≤ k := Nat.cast_nonneg k
  have hd1 : 0 < 1 - (k + 1) * u := by linarith
  have hd0 : 0 < 1 - k * u := by nlinarith
  push_cast
  have hl : u + (1 + u) * (k * u / (1 - k * u)) = (k + 1) * u / (1 - k * u) := by
    rw [eq_div_iff hd0.ne', add_mul, mul_assoc (1 + u), div_mul_cancel₀ _ hd0.ne']
    ring
  rw [hl]
  exact div_le_div_of_nonneg_left (by positivity) hd1 (by nlinarith)

/-- **Two roundings stay within `γₖ₊₁`.** `2u + u² ≤ γ₂ ≤ γₖ₊₁` for `k ≥ 1` when
`(k + 1) u < 1`. -/
theorem two_mul_add_sq_le_gamma {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ((k : K) + 1) * 2 ^ (-(p : ℤ)) < 1) :
    2 * 2 ^ (-(p : ℤ)) + (2 ^ (-(p : ℤ))) ^ 2 ≤ (gamma p (k + 1) : K) := by
  unfold gamma
  generalize hu : (2 : K) ^ (-(p : ℤ)) = u at hk ⊢
  have hu0 : 0 < u := hu ▸ two_zpow_pos _
  have hk1' : (1 : K) ≤ k := by exact_mod_cast hk1
  have hd1 : 0 < 1 - (k + 1) * u := by linarith
  push_cast
  rw [le_div_iff₀ hd1]
  nlinarith [mul_pos hu0 hu0, mul_pos (mul_pos hu0 hu0) hu0]

/-- **One rounding stays within `γ₁`.** `u ≤ γ₁` when `u < 1`. -/
theorem le_gamma_one (h : (2 : K) ^ (-(p : ℤ)) < 1) :
    2 ^ (-(p : ℤ)) ≤ (gamma p 1 : K) := by
  unfold gamma
  generalize hu : (2 : K) ^ (-(p : ℤ)) = u at h ⊢
  have hu0 : 0 < u := hu ▸ two_zpow_pos _
  push_cast
  rw [one_mul, le_div_iff₀ (by linarith)]
  nlinarith

/-- **`γₖ` is nonnegative** when `k u < 1`. -/
theorem gamma_nonneg {k : ℕ} (hk : (k : K) * 2 ^ (-(p : ℤ)) < 1) : 0 ≤ (gamma p k : K) := by
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) (two_zpow_pos _).le) (by linarith)

/-- **Forward error of the floating-point dot product.** If `n u < 1` with `u = 2^(-p)`, then
`|fl(∑_{i<n} xᵢ yᵢ) - ∑_{i<n} xᵢ yᵢ| ≤ γₙ ∑_{i<n} |xᵢ yᵢ|`, where the floating-point sum is
`dotFl`: rounded products added from left to right, each addition rounded (Demmel, Math 221
Lecture 5 notes, 2024, recalling homework 1.10, in the first-order form `n u`; the exact `γₙ`
form is the standard one of N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., SIAM, 2002). -/
theorem abs_dotFl_sub_le (hp : 1 ≤ p) (x y : ℕ → K) (n : ℕ)
    (hn : (n : K) * 2 ^ (-(p : ℤ)) < 1) :
    |dotFl p x y n - ∑ i ∈ range n, x i * y i| ≤ gamma p n * ∑ i ∈ range n, |x i * y i| := by
  set u : K := 2 ^ (-(p : ℤ)) with hu_def
  have hu : 0 < u := two_zpow_pos _
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [dotFl]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero =>
    have h1 : dotFl p x y 1 = fl p (x 0 * y 0) := by
      simp only [dotFl, zero_add]
      exact fl_eq_self hp (isFloat_fl hp _)
    simp only [zero_add, range_one, sum_singleton, h1]
    have hu1 : u < 1 := by
      have := hn
      push_cast at this
      linarith
    exact (abs_fl_sub_le (x 0 * y 0)).trans
      (mul_le_mul_of_nonneg_right (le_gamma_one hu1) (abs_nonneg _))
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : K) * u < 1 := by
      have : ((k + 1 : ℕ) : K) ≤ ((k + 1 + 1 : ℕ) : K) := by exact_mod_cast Nat.le_succ _
      nlinarith
    have ih := ih hk (Nat.succ_pos _)
    set S := ∑ i ∈ range (k + 1), x i * y i
    set T := ∑ i ∈ range (k + 1), |x i * y i|
    set s := dotFl p x y (k + 1)
    set q := x (k + 1) * y (k + 1)
    have hST : |S| ≤ T := abs_sum_le_sum_abs _ _
    have hT : 0 ≤ T := sum_nonneg fun _ _ => abs_nonneg _
    have hg : 0 ≤ (gamma p (k + 1) : K) := gamma_nonneg hk
    -- the two roundings of the step
    set a := fl p q - q with ha_def
    have ha : |a| ≤ u * |q| := abs_fl_sub_le q
    set b := fl p (s + fl p q) - (s + fl p q) with hb_def
    have hb : |b| ≤ u * |s + fl p q| := abs_fl_sub_le _
    have hstep : dotFl p x y (k + 1 + 1) - ∑ i ∈ range (k + 1 + 1), x i * y i =
        (s - S) + a + b := by
      rw [show dotFl p x y (k + 1 + 1) = fl p (s + fl p q) from rfl, sum_range_succ, ha_def,
        hb_def]
      ring
    have hsq : |s + fl p q| ≤ T + gamma p (k + 1) * T + |q| + u * |q| := by
      have : s + fl p q = S + (s - S) + q + a := by ring
      rw [this]
      calc |S + (s - S) + q + a| ≤ |S| + |s - S| + |q| + |a| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ _ := by gcongr
    rw [hstep, sum_range_succ]
    have hn' : ((((k + 1 : ℕ) : K)) + 1) * u < 1 := by
      have := hn
      push_cast at this ⊢
      linarith
    have hγ := gamma_step (K := K) (p := p) hn'
    have hγ2 := two_mul_add_sq_le_gamma (K := K) (p := p) (Nat.succ_pos k) hn'
    have hq : 0 ≤ |q| := abs_nonneg _
    calc |s - S + a + b| ≤ |s - S| + |a| + |b| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ gamma p (k + 1) * T + u * |q| + u * (T + gamma p (k + 1) * T + |q| + u * |q|) := by
          gcongr
          exact hb.trans (by gcongr)
      _ = (u + (1 + u) * gamma p (k + 1)) * T + (2 * u + u ^ 2) * |q| := by ring
      _ ≤ gamma p (k + 1 + 1) * T + gamma p (k + 1 + 1) * |q| := by gcongr
      _ = gamma p (k + 1 + 1) * (T + |x (k + 1) * y (k + 1)|) := by ring

/-- **Floating-point matrix product.** Entry `(i, j)` of `matMulFl p A B` is the floating-point
dot product `dotFl` of row `i` of `A` and column `j` of `B`. -/
def matMulFl (p : ℕ) {m n r : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin r) K) :
    Matrix (Fin m) (Fin r) K :=
  fun i j => dotFl p (fun k => if h : k < n then A i ⟨k, h⟩ else 0)
    (fun k => if h : k < n then B ⟨k, h⟩ j else 0) n

/-- **Forward error of floating-point matrix multiplication.** If `n u < 1`, the floating-point
product of an `m × n` matrix `A` and an `n × r` matrix `B` satisfies, entrywise,
`|fl(A B) - A B| ≤ γₙ |A| |B|` (Demmel, Math 221 Lecture 5 notes, 2024: "`C = fl(A*B) = A*B + E`
where `|E| <= n*macheps*|A|*|B|`", in first-order form; the exact `γₙ` form is the standard
one of N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002). -/
theorem abs_matMulFl_sub_le (hp : 1 ≤ p) {m n r : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin r) K) (hn : (n : K) * 2 ^ (-(p : ℤ)) < 1) (i : Fin m) (j : Fin r) :
    |matMulFl p A B i j - (A * B) i j| ≤ gamma p n * ∑ k, |A i k| * |B k j| := by
  have h := abs_dotFl_sub_le hp (fun k => if h : k < n then A i ⟨k, h⟩ else 0)
    (fun k => if h : k < n then B ⟨k, h⟩ j else 0) n hn
  have hsum : ∑ k ∈ range n, (if h : k < n then A i ⟨k, h⟩ else 0) *
      (if h : k < n then B ⟨k, h⟩ j else 0) = (A * B) i j := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < n then A i ⟨k, h⟩ else 0) * (if h : k < n then B ⟨k, h⟩ j else 0))]
    simp
  have hsumabs : ∑ k ∈ range n, |(if h : k < n then A i ⟨k, h⟩ else 0) *
      (if h : k < n then B ⟨k, h⟩ j else 0)| = ∑ k, |A i k| * |B k j| := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => |(if h : k < n then A i ⟨k, h⟩ else 0) * (if h : k < n then B ⟨k, h⟩ j else 0)|)]
    simp [abs_mul]
  rw [hsum, hsumabs] at h
  exact h

end Cslib.Algorithms.Lean.FloatingPoint.DotProductError
