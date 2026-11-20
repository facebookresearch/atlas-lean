/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Ecology.Leslie

import MathlibExt.Probability.FiniteMarkovChainConvergence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid

/-!
# Stable-age convergence for primitive Leslie matrices

This module proves the Strong Ergodic Theorem (Fundamental Theorem of
Demography) for age-structured population projection: the age distribution of
a population projected by a primitive Leslie matrix converges to the stable
age distribution, independently of the (nonzero, nonnegative) initial vector.

## Main results

* `leslie_projection`: finite-step projection `x t = (L ^ t) *ᵥ x 0`.
* `tendsto_leslieMatrix_pow_mulVec_div_pow`: scaled projections converge.
* `tendsto_leslie_age_distribution`: age shares converge to `v i / ∑ j, v j`.
* `exists_stable_age_distribution`: eigen-data from Perron-Frobenius.

## Implementation note

Reuses Atlas `leslieMatrix`, the Perron-Frobenius theorem for irreducible
nonnegative matrices, and the convergence theorem for primitive stochastic
matrices, through the similarity `P i j = L i j * v j / (r * v i)`.

## Not covered

* Asymptotics of periodic (imprimitive) matrices.
* Sensitivity and elasticity analysis.
* Reproductive value beyond its role as the left eigenvector.
* Density dependence and migration terms.
* Any convergence claim for non-primitive matrices.

## References

* P. H. Leslie, _On the use of matrices in certain population mathematics_,
  Biometrika 33 (1945), 183–212: the primary source of the matrix projection
  `x (t + 1) = L *ᵥ x t`, with fertilities in the first row and survival
  probabilities on the subdiagonal (`leslieMatrix f s` here), and of its stable
  age distribution.
* G. Frobenius, _Über Matrizen aus nicht negativen Elementen_, S.-Ber. Preuss.
  Akad. Wiss. Berlin (1912), 456–477: the primary source for primitive
  nonnegative matrices, whose Perron root strictly dominates every other
  eigenvalue in modulus.
* J. M. Cushing, _Matrix Models and Population Dynamics_, IAS/Park City
  Mathematics Series lecture notes (AMS, 2008/2009), Lecture 1, Exercise 2
  ("Strong Ergodic Theorem").
* H. Caswell, _Matrix Population Models: Construction, Analysis, and
  Interpretation_, 2nd edition, Sinauer Associates, Sunderland, MA, 2001,
  Chapter 4 (Strong Ergodic Theorem for primitive projection matrices).

Correspondence with the hypotheses here: `(leslieMatrix f s).IsPrimitive` is
primitivity in Frobenius's sense, the condition under which normalized iterates
converge (the imprimitive swap matrix in the tests has no limiting age shares).
The initial population is nonnegative and nonzero, so its pairing with the
positive left eigenvector `w` is positive and the age shares are defined.
-/
@[expose] public section

namespace MathlibExt.Biology.Demography.Leslie

open Matrix Filter Topology MathlibExt.Biology.Ecology.Leslie

/-- Stochastic similarity transform of a Leslie matrix. -/
private noncomputable def leslieStochasticP {n : ℕ} (f s : Fin n → ℝ)
    (v : Fin n → ℝ) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => leslieMatrix f s i j * v j / (r * v i)

private theorem leslieStochasticP_row_sum {n : ℕ} (f s v : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hv : ∀ i, 0 < v i)
    (hLv : leslieMatrix f s *ᵥ v = r • v) (i : Fin n) :
    ∑ j, leslieStochasticP f s v r i j = 1 := by
  have hvi : v i ≠ 0 := ne_of_gt (hv i)
  have hr' : r ≠ 0 := ne_of_gt hr
  have hsum : ∑ j, leslieMatrix f s i j * v j = r * v i := by
    have h := congrFun hLv i
    simp only [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul] at h
    exact h
  simp only [leslieStochasticP, ← Finset.sum_div, hsum]
  exact div_self (mul_ne_zero hr' hvi)

private theorem leslieStochasticP_nonneg {n : ℕ} (f s v : Fin n → ℝ) {r : ℝ}
    (hL : ∀ i j, 0 ≤ leslieMatrix f s i j)
    (hr : 0 < r) (hv : ∀ i, 0 < v i) (i j : Fin n) :
    0 ≤ leslieStochasticP f s v r i j := by
  simp only [leslieStochasticP]
  exact div_nonneg (mul_nonneg (hL i j) (le_of_lt (hv j)))
    (le_of_lt (mul_pos hr (hv i)))

private theorem leslieStochasticP_mem {n : ℕ} (f s v : Fin n → ℝ) {r : ℝ}
    (hL : ∀ i j, 0 ≤ leslieMatrix f s i j)
    (hr : 0 < r) (hv : ∀ i, 0 < v i)
    (hLv : leslieMatrix f s *ᵥ v = r • v) :
    leslieStochasticP f s v r ∈ rowStochastic ℝ (Fin n) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  exact ⟨leslieStochasticP_nonneg f s v hL hr hv,
    leslieStochasticP_row_sum f s v hr hv hLv⟩

private theorem leslieStochasticP_pow_apply {n : ℕ} (f s v : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hv : ∀ i, 0 < v i) (t : ℕ) (i : Fin n) :
    ∀ j : Fin n, (leslieStochasticP f s v r ^ t) i j
      = (leslieMatrix f s ^ t) i j * v j / (r ^ t * v i) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hvi : v i ≠ 0 := ne_of_gt (hv i)
  induction t with
  | zero =>
      intro j
      simp only [pow_zero]
      by_cases h : i = j
      · subst h
        rw [Matrix.one_apply_eq, one_mul, div_self hvi]
      · rw [Matrix.one_apply_ne h]
        simp
  | succ t ih =>
      intro j
      have eP : leslieStochasticP f s v r ^ (t + 1)
          = leslieStochasticP f s v r ^ t * leslieStochasticP f s v r :=
        pow_succ _ _
      have eL : leslieMatrix f s ^ (t + 1)
          = leslieMatrix f s ^ t * leslieMatrix f s := pow_succ _ _
      rw [eP, eL]
      simp only [Matrix.mul_apply, ih]
      simp only [leslieStochasticP]
      have hterm : ∀ k : Fin n,
          ((leslieMatrix f s ^ t) i k * v k / (r ^ t * v i)) *
            (leslieMatrix f s k j * v j / (r * v k))
          = ((leslieMatrix f s ^ t) i k * leslieMatrix f s k j) * v j /
            (r ^ (t + 1) * v i) := by
        intro k
        have hvk : v k ≠ 0 := ne_of_gt (hv k)
        rw [pow_succ r t]
        have hrt : r ^ t ≠ 0 := ne_of_gt (pow_pos hr t)
        have h1 : r ^ t * v i ≠ 0 := mul_ne_zero hrt hvi
        have h2 : r * v k ≠ 0 := mul_ne_zero hr' hvk
        have h3 : (r ^ t * r) * v i ≠ 0 :=
          mul_ne_zero (mul_ne_zero hrt hr') hvi
        field_simp
      simp only [hterm, ← Finset.sum_div, ← Finset.sum_mul]

private theorem leslieStochasticP_isPrimitive {n : ℕ} (f s v : Fin n → ℝ)
    {r : ℝ} (hprim : (leslieMatrix f s).IsPrimitive)
    (hr : 0 < r) (hv : ∀ i, 0 < v i) :
    (leslieStochasticP f s v r).IsPrimitive := by
  refine ⟨leslieStochasticP_nonneg f s v hprim.nonneg hr hv, ?_⟩
  obtain ⟨k, hkpos, hk⟩ := hprim.exists_pos_pow
  refine ⟨k, hkpos, fun i j => ?_⟩
  rw [leslieStochasticP_pow_apply f s v hr hv k i j]
  exact div_pos (mul_pos (hk i j) (hv j)) (mul_pos (pow_pos hr k) (hv i))

/-- Stationary distribution of the similarity transform. -/
private noncomputable def leslieStationary {n : ℕ} (w v : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j => w j * v j / (w ⬝ᵥ v)

private theorem leslie_dot_pos {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : Fin n) :
    0 < w ⬝ᵥ v := by
  simp only [dotProduct]
  refine Finset.sum_pos' (fun a _ => mul_nonneg (le_of_lt (hw a))
    (le_of_lt (hv a))) ?_
  exact ⟨k, Finset.mem_univ k, mul_pos (hw k) (hv k)⟩

private theorem leslieStationary_nonneg {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : Fin n) (y : Fin n) :
    0 ≤ leslieStationary w v y := by
  simp only [leslieStationary]
  exact div_nonneg (mul_nonneg (le_of_lt (hw y)) (le_of_lt (hv y)))
    (le_of_lt (leslie_dot_pos w v hw hv k))

private theorem leslieStationary_sum {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : Fin n) :
    ∑ y, leslieStationary w v y = 1 := by
  have hS : w ⬝ᵥ v ≠ 0 := ne_of_gt (leslie_dot_pos w v hw hv k)
  simp only [leslieStationary, ← Finset.sum_div]
  change (w ⬝ᵥ v) / (w ⬝ᵥ v) = 1
  exact div_self hS

private theorem leslieStationary_vecMul {n : ℕ} (f s : Fin n → ℝ)
    (w v : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, 0 < v i) (hwL : w ᵥ* leslieMatrix f s = r • w) (k : Fin n) :
    (leslieStationary w v) ᵥ* (leslieStochasticP f s v r)
      = leslieStationary w v := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hS : w ⬝ᵥ v ≠ 0 := ne_of_gt (leslie_dot_pos w v hw hv k)
  funext j
  simp only [Matrix.vecMul_apply_eq_sum, leslieStationary, leslieStochasticP]
  have hterm : ∀ a : Fin n,
      (w a * v a / (w ⬝ᵥ v)) * (leslieMatrix f s a j * v j / (r * v a))
      = (w a * leslieMatrix f s a j) * v j / ((w ⬝ᵥ v) * r) := by
    intro a
    have hva : v a ≠ 0 := ne_of_gt (hv a)
    have h2 : r * v a ≠ 0 := mul_ne_zero hr' hva
    have h3 : (w ⬝ᵥ v) * r ≠ 0 := mul_ne_zero hS hr'
    field_simp
  simp only [hterm, ← Finset.sum_div, ← Finset.sum_mul]
  have hwj : ∑ a, w a * leslieMatrix f s a j = r * w j := by
    have h := congrFun hwL j
    simp only [Matrix.vecMul_apply_eq_sum, Pi.smul_apply, smul_eq_mul] at h
    exact h
  rw [hwj]
  have hSr : (w ⬝ᵥ v) * r ≠ 0 := mul_ne_zero hS hr'
  field_simp

private theorem leslie_pow_entry_div_pow {n : ℕ} (f s : Fin n → ℝ) {r : ℝ}
    (hprim : (leslieMatrix f s).IsPrimitive)
    (hr : 0 < r) {v w : Fin n → ℝ}
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hLv : leslieMatrix f s *ᵥ v = r • v) (hwL : w ᵥ* leslieMatrix f s = r • w)
    (k : Fin n) (i j : Fin n) :
    Tendsto (fun t : ℕ => (leslieMatrix f s ^ t) i j / r ^ t) atTop
      (𝓝 (w j * v i / (w ⬝ᵥ v))) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hP := leslieStochasticP_mem f s v hprim.nonneg hr hv hLv
  have hPprim := leslieStochasticP_isPrimitive f s v hprim hr hv
  have hπ0 := leslieStationary_nonneg w v hw hv k
  have hπ1 := leslieStationary_sum w v hw hv k
  have hstat := leslieStationary_vecMul f s w v hr hw hv hwL k
  have hlim :=
    MathlibExt.Probability.FiniteMarkovChainConvergence.tendsto_pow_apply
      hP hPprim hπ0 hπ1 hstat i j
  have hS : w ⬝ᵥ v ≠ 0 := ne_of_gt (leslie_dot_pos w v hw hv k)
  have hvi : v i ≠ 0 := ne_of_gt (hv i)
  have hvj : v j ≠ 0 := ne_of_gt (hv j)
  have heq : ∀ t : ℕ, (leslieMatrix f s ^ t) i j / r ^ t
      = (leslieStochasticP f s v r ^ t) i j * (v i / v j) := by
    intro t
    rw [leslieStochasticP_pow_apply f s v hr hv t i j]
    have hrt : r ^ t ≠ 0 := ne_of_gt (pow_pos hr t)
    have h1 : r ^ t * v i ≠ 0 := mul_ne_zero hrt hvi
    field_simp
  have hlimval : leslieStationary w v j * (v i / v j)
      = w j * v i / (w ⬝ᵥ v) := by
    simp only [leslieStationary]
    field_simp
  have h2 := hlim.mul_const (v i / v j)
  rw [hlimval] at h2
  simp only [heq]
  exact h2

/-- Finite-step projection `x t = L ^ t *ᵥ x 0`, with no convergence claim. -/
theorem leslie_projection {n : ℕ} (f s : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (hstep : ∀ t, x (t + 1) = leslieMatrix f s *ᵥ x t) (t : ℕ) :
    x t = (leslieMatrix f s ^ t) *ᵥ x 0 := by
  induction t with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ t ih => rw [hstep t, ih, pow_succ', Matrix.mulVec_mulVec]

/-- Strong Ergodic Theorem, growth-rate form, with supplied positive
right and left eigenvectors. Primitivity is essential; no diagonalizability
is assumed. -/
theorem tendsto_leslieMatrix_pow_mulVec_div_pow {n : ℕ} {f s : Fin n → ℝ}
    (hprim : (leslieMatrix f s).IsPrimitive) {r : ℝ} (hr : 0 < r)
    {v w : Fin n → ℝ}
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hLv : leslieMatrix f s *ᵥ v = r • v) (hwL : w ᵥ* leslieMatrix f s = r • w)
    (x₀ : Fin n → ℝ) (i : Fin n) :
    Tendsto (fun t : ℕ => (leslieMatrix f s ^ t *ᵥ x₀) i / r ^ t) atTop
      (𝓝 (w ⬝ᵥ x₀ / (w ⬝ᵥ v) * v i)) := by
  have hdecomp : ∀ t : ℕ, (leslieMatrix f s ^ t *ᵥ x₀) i / r ^ t
      = ∑ j, ((leslieMatrix f s ^ t) i j / r ^ t * x₀ j) := by
    intro t
    rw [Matrix.mulVec_apply_eq_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    exact (div_mul_eq_mul_div _ _ _).symm
  have hterm : ∀ j : Fin n, Tendsto
      (fun t : ℕ => (leslieMatrix f s ^ t) i j / r ^ t * x₀ j) atTop
      (𝓝 (w j * v i / (w ⬝ᵥ v) * x₀ j)) := by
    intro j
    exact (leslie_pow_entry_div_pow f s hprim hr hv hw hLv hwL i i j).mul_const
      (x₀ j)
  have hlimval : (∑ j, (w j * v i / (w ⬝ᵥ v) * x₀ j))
      = w ⬝ᵥ x₀ / (w ⬝ᵥ v) * v i := by
    have hS : w ⬝ᵥ v ≠ 0 := ne_of_gt (leslie_dot_pos w v hw hv i)
    have hterm2 : ∀ j : Fin n, w j * v i / (w ⬝ᵥ v) * x₀ j
        = (w j * x₀ j) * (v i / (w ⬝ᵥ v)) := by
      intro j
      ring
    simp only [hterm2, ← Finset.sum_mul]
    change (w ⬝ᵥ x₀) * (v i / (w ⬝ᵥ v)) = _
    field_simp
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  simp only [hdecomp]
  rw [hlimval] at hsum
  exact hsum

/-- Strong Ergodic Theorem, age-distribution form, with supplied positive
right and left eigenvectors. Primitivity is essential; no diagonalizability
is assumed. -/
theorem tendsto_leslie_age_distribution {n : ℕ} {f s : Fin n → ℝ}
    (hprim : (leslieMatrix f s).IsPrimitive) {r : ℝ} (hr : 0 < r)
    {v w : Fin n → ℝ}
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hLv : leslieMatrix f s *ᵥ v = r • v) (hwL : w ᵥ* leslieMatrix f s = r • w)
    {x₀ : Fin n → ℝ} (hx₀ : ∀ i, 0 ≤ x₀ i) (hx₀' : x₀ ≠ 0) (i : Fin n) :
    Tendsto (fun t : ℕ => (leslieMatrix f s ^ t *ᵥ x₀) i /
        ∑ j, (leslieMatrix f s ^ t *ᵥ x₀) j) atTop (𝓝 (v i / ∑ j, v j)) := by
  have hnum :=
    tendsto_leslieMatrix_pow_mulVec_div_pow hprim hr hv hw hLv hwL x₀ i
  have hden_term : ∀ j : Fin n, Tendsto
      (fun t : ℕ => (leslieMatrix f s ^ t *ᵥ x₀) j / r ^ t) atTop
      (𝓝 (w ⬝ᵥ x₀ / (w ⬝ᵥ v) * v j)) := fun j =>
    tendsto_leslieMatrix_pow_mulVec_div_pow hprim hr hv hw hLv hwL x₀ j
  have hden := tendsto_finsetSum Finset.univ (fun j _ => hden_term j)
  have hdenfun : ∀ t : ℕ, (∑ j, (leslieMatrix f s ^ t *ᵥ x₀) j / r ^ t)
      = (∑ j, (leslieMatrix f s ^ t *ᵥ x₀) j) / r ^ t := by
    intro t
    rw [Finset.sum_div]
  simp only [hdenfun] at hden
  have hdenval : (∑ j, w ⬝ᵥ x₀ / (w ⬝ᵥ v) * v j)
      = w ⬝ᵥ x₀ / (w ⬝ᵥ v) * ∑ j, v j :=
    (Finset.mul_sum _ _ _).symm
  rw [hdenval] at hden
  have hquot : ∀ t : ℕ, (leslieMatrix f s ^ t *ᵥ x₀) i /
        ∑ j, (leslieMatrix f s ^ t *ᵥ x₀) j
      = ((leslieMatrix f s ^ t *ᵥ x₀) i / r ^ t) /
        ((∑ j, (leslieMatrix f s ^ t *ᵥ x₀) j) / r ^ t) := by
    intro t
    have hrt : r ^ t ≠ 0 := ne_of_gt (pow_pos hr t)
    field_simp
  have hwx₀ : 0 < w ⬝ᵥ x₀ := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hx₀'
    simp only [Pi.zero_apply] at hk
    have hpos : 0 < x₀ k := lt_of_le_of_ne (hx₀ k) (Ne.symm hk)
    simp only [dotProduct]
    refine Finset.sum_pos' (fun a _ => mul_nonneg (le_of_lt (hw a))
      (hx₀ a)) ?_
    exact ⟨k, Finset.mem_univ k, mul_pos (hw k) hpos⟩
  have hS : 0 < w ⬝ᵥ v := leslie_dot_pos w v hw hv i
  have hV : 0 < ∑ j, v j :=
    Finset.sum_pos' (fun a _ => le_of_lt (hv a)) ⟨i, Finset.mem_univ i, hv i⟩
  have hden_ne : w ⬝ᵥ x₀ / (w ⬝ᵥ v) * ∑ j, v j ≠ 0 :=
    ne_of_gt (mul_pos (div_pos hwx₀ hS) hV)
  have hlimval : (w ⬝ᵥ x₀ / (w ⬝ᵥ v) * v i) / (w ⬝ᵥ x₀ / (w ⬝ᵥ v) * ∑ j, v j)
      = v i / ∑ j, v j := by
    have h1 : w ⬝ᵥ x₀ / (w ⬝ᵥ v) ≠ 0 := ne_of_gt (div_pos hwx₀ hS)
    have h2 : ∑ j, v j ≠ 0 := ne_of_gt hV
    field_simp
  have h := hnum.div hden hden_ne
  simp only [hquot]
  rw [hlimval] at h
  exact h

/-- Strong Ergodic Theorem with eigen-data obtained from Perron-Frobenius:
the stable age distribution exists, sums to one, and attracts every nonzero
nonnegative initial population. -/
theorem exists_stable_age_distribution {n : ℕ} [NeZero n] {f s : Fin n → ℝ}
    (hprim : (leslieMatrix f s).IsPrimitive) :
    ∃ (r : ℝ) (v : Fin n → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ ∑ i, v i = 1 ∧
      leslieMatrix f s *ᵥ v = r • v ∧
      ∀ x₀ : Fin n → ℝ, (∀ i, 0 ≤ x₀ i) → x₀ ≠ 0 → ∀ i,
        Tendsto (fun t : ℕ => (leslieMatrix f s ^ t *ᵥ x₀) i /
          ∑ j, (leslieMatrix f s ^ t *ᵥ x₀) j) atTop (𝓝 (v i)) := by
  have hnpos : 0 < n := NeZero.pos n
  have k : Fin n := ⟨0, hnpos⟩
  obtain ⟨r, v, hr, hv, hLv, -⟩ := hprim.isIrreducible.perron_frobenius
  obtain ⟨r', w, hr', hw, hLtw, -⟩ :=
    hprim.isIrreducible.transpose.perron_frobenius
  have hSpos := leslie_dot_pos w v hw hv k
  have hS : w ⬝ᵥ v ≠ 0 := ne_of_gt hSpos
  have hrr' : r' = r := by
    have h1 : w ⬝ᵥ (leslieMatrix f s *ᵥ v) = r * (w ⬝ᵥ v) := by
      rw [hLv]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have h2 : w ⬝ᵥ (leslieMatrix f s *ᵥ v) = r' * (w ⬝ᵥ v) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hLtw]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    exact (mul_right_cancel₀ hS (h1.symm.trans h2)).symm
  have hwL : w ᵥ* leslieMatrix f s = r • w := by
    have hwL' : w ᵥ* leslieMatrix f s = r' • w := by
      rw [← Matrix.mulVec_transpose]
      exact hLtw
    rw [hrr'] at hwL'
    exact hwL'
  have hVpos : 0 < ∑ i, v i :=
    Finset.sum_pos' (fun a _ => le_of_lt (hv a)) ⟨k, Finset.mem_univ k, hv k⟩
  have hnpos' : ∀ a : Fin n, 0 < ((∑ i, v i)⁻¹ • v) a := by
    intro a
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hVpos) (hv a)
  have hnsum : ∑ i, ((∑ i, v i)⁻¹ • v) i = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hVpos)
  have hnLv : leslieMatrix f s *ᵥ ((∑ i, v i)⁻¹ • v)
      = r • ((∑ i, v i)⁻¹ • v) := by
    rw [Matrix.mulVec_smul, hLv]
    ext a
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨r, (∑ i, v i)⁻¹ • v, hr, hnpos', hnsum, hnLv,
    fun x₀ hx₀ hx₀' a => ?_⟩
  have hden : ∑ _x, (∑ i, v i)⁻¹ * v _x = 1 := by
    rw [← Finset.mul_sum, inv_mul_cancel₀ (ne_of_gt hVpos)]
  have h :=
    tendsto_leslie_age_distribution hprim hr hnpos' hw hnLv hwL hx₀ hx₀' a
  simpa [Pi.smul_apply, smul_eq_mul, hden] using h

end MathlibExt.Biology.Demography.Leslie
