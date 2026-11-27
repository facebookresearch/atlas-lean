/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.RingTheory.MvPolynomial.Bernstein
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bernstein coefficient bounds on boxes

Tensor-product Bernstein weights are nonnegative on the unit cube and sum to
one. Hence bounds on all coefficients enclose every polynomial value there.
Affine pullback transfers this statement to closed coordinate boxes, including
boxes with zero-width coordinates. Pullback does not increase coordinate
degrees, so the degree bound is imposed on the original polynomial.

Reference: A. P. Smith, *Enclosure Methods for Systems of Polynomial Equations
and Inequalities* (2012), §3.1.4 (affine pullback) and §3.2.4, equation (3.17)
(range enclosure), https://d-nb.info/1028327854/34. Allowing zero-width boxes
uses the same pullback argument without requiring an invertible affine map.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {ι : Type*} [Fintype ι]

/-- A tensor-product Bernstein polynomial has nonnegative value whenever
every coordinate of its real argument lies in the closed unit interval.
The variable type is finite. -/
theorem eval_bernstein_nonneg (n k : ι → ℕ) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc 0 1) : 0 ≤ eval x (bernstein n k) := by
  rw [eval_bernstein]
  apply prod_nonneg
  intro i _
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hx i).1 _))
    (pow_nonneg (sub_nonneg.mpr (hx i).2) _)

/-- Summing the tensor-product Bernstein values over every index in the
coordinate degree box gives one, at every real argument over a finite variable type. -/
theorem sum_eval_bernstein [DecidableEq ι] (n : ι → ℕ) (x : ι → ℝ) :
    ∑ k : (i : ι) → Fin (n i + 1), eval x (bernstein n (fun i => k i)) = 1 := by
  simp_rw [eval_bernstein]
  rw [← Fintype.prod_sum (fun i (j : Fin (n i + 1)) =>
    (bernsteinPolynomial ℝ (n i) j).eval (x i))]
  apply prod_eq_one
  intro i _
  have h := congrArg (Polynomial.eval (x i)) (bernsteinPolynomial.sum ℝ (n i))
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_one, Finset.sum_range] using h

/-- If `p.degreeOf i ≤ n i` for each coordinate and every degree-`n` Bernstein
coefficient lies in `[L,U]`, then `p(x)` lies in `[L,U]` at every point of the
closed unit cube in finitely many variables. Both endpoint inequalities are non-strict. -/
theorem eval_mem_Icc_of_bernsteinCoeff {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    (hp : ∀ i, p.degreeOf i ≤ n i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc 0 1) {L U : ℝ}
    (hL : ∀ k : (i : ι) → Fin (n i + 1), L ≤ bernsteinCoeff n p (fun i => k i))
    (hU : ∀ k : (i : ι) → Fin (n i + 1), bernsteinCoeff n p (fun i => k i) ≤ U) :
    eval x p ∈ Set.Icc L U := by
  classical
  rw [eval_eq_sum_bernstein hp]
  constructor
  · calc
      L = ∑ k : (i : ι) → Fin (n i + 1), L * eval x (bernstein n (fun i => k i)) := by
        rw [← mul_sum, sum_eval_bernstein, mul_one]
      _ ≤ _ := sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hL k)
        (eval_bernstein_nonneg _ _ hx)
  · calc
      _ ≤ ∑ k : (i : ι) → Fin (n i + 1), U * eval x (bernstein n (fun i => k i)) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hU k)
          (eval_bernstein_nonneg _ _ hx)
      _ = U := by rw [← mul_sum, sum_eval_bernstein, mul_one]

/-- For a real polynomial with coordinate degrees at most `n`, its value on
the closed unit cube lies between the minimum and maximum of its finitely
many degree-`n` Bernstein coefficients. The index set is nonempty even when
the variable type is empty or some coordinate degree is zero. -/
theorem eval_mem_Icc_bernsteinCoeff [DecidableEq ι] {n : ι → ℕ}
    {p : MvPolynomial ι ℝ} (hp : ∀ i, p.degreeOf i ≤ n i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc 0 1) :
    eval x p ∈ Set.Icc
      ((univ : Finset ((i : ι) → Fin (n i + 1))).inf' univ_nonempty
        (fun k => bernsteinCoeff n p (fun i => k i)))
      ((univ : Finset ((i : ι) → Fin (n i + 1))).sup' univ_nonempty
        (fun k => bernsteinCoeff n p (fun i => k i))) := by
  apply eval_mem_Icc_of_bernsteinCoeff hp hx
  · intro k
    exact inf'_le (fun k : (i : ι) → Fin (n i + 1) =>
      bernsteinCoeff n p (fun i => k i)) (mem_univ k)
  · intro k
    exact le_sup' (fun k : (i : ι) → Fin (n i + 1) =>
      bernsteinCoeff n p (fun i => k i)) (mem_univ k)

/-- Strict positivity of every degree-`n` Bernstein coefficient of `p`
implies strict positivity of `p` throughout the closed unit cube, provided
each coordinate degree of `p` is at most `n` and the variable type is finite.
This is a sufficient condition. -/
theorem eval_pos_of_bernsteinCoeff {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    (hp : ∀ i, p.degreeOf i ≤ n i) {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Icc 0 1)
    (hc : ∀ k : (i : ι) → Fin (n i + 1), 0 < bernsteinCoeff n p (fun i => k i)) :
    0 < eval x p := by
  classical
  exact lt_of_lt_of_le ((lt_inf'_iff ..).mpr (fun k _ => hc k))
    (eval_mem_Icc_bernsteinCoeff hp hx).1

/-- Pull a real multivariate polynomial back along the coordinate affine map
`t i ↦ a i + (b i - a i) * t i`. This is defined for all endpoints, even when
some widths vanish or are negative. Ordered endpoints are needed only for
the box enclosure theorem. -/
noncomputable def boxPullback (a b : ι → ℝ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  eval₂Hom C (fun i => C (a i) + C (b i - a i) * X i) p

omit [Fintype ι] in
/-- Evaluating the affine box pullback at `t` equals evaluating the original
polynomial at `a + (b-a)*t`, with the operations taken coordinatewise. -/
theorem eval_boxPullback (a b t : ι → ℝ) (p : MvPolynomial ι ℝ) :
    eval t (boxPullback a b p) = eval (fun i => a i + (b i - a i) * t i) p := by
  simp only [boxPullback, map_eval₂Hom, map_add, map_mul, eval_C, eval_X]
  congr 2
  ext c
  simp

omit [Fintype ι] in
private theorem degreeOf_affine [DecidableEq ι] (a b : ι → ℝ) (i j : ι) :
    (C (a j) + C (b j - a j) * X j : MvPolynomial ι ℝ).degreeOf i ≤
      (Pi.single j 1 : ι → ℕ) i := by
  classical
  apply (degreeOf_add_le _ _ _).trans
  apply max_le
  · simp
  · apply (degreeOf_C_mul_le _ _ _).trans
    simp [degreeOf_X, Pi.single_apply]

omit [Fintype ι] in
/-- Coordinatewise affine box pullback does not increase any coordinate
degree, for arbitrary real endpoints, including zero widths. -/
theorem degreeOf_boxPullback_le (a b : ι → ℝ) (p : MvPolynomial ι ℝ) (i : ι) :
    (boxPullback a b p).degreeOf i ≤ p.degreeOf i := by
  classical
  unfold boxPullback
  rw [coe_eval₂Hom, eval₂_eq]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro d hd
  apply (degreeOf_C_mul_le _ _ _).trans
  apply (degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ j ∈ d.support, d j * (Pi.single j 1 : ι → ℕ) i := by
      apply sum_le_sum
      intro j _
      exact (degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (degreeOf_affine a b i j))
    _ = d i := by simp [Pi.single_apply, eq_comm]
    _ ≤ p.degreeOf i := le_degreeOf_of_mem_support i hd

theorem exists_unit_parameter {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, a + (b - a) * t = x := by
  by_cases h : a = b
  · refine ⟨0, by norm_num, ?_⟩
    have : x = a := le_antisymm (h ▸ hx.2) hx.1
    simp [this]
  · have hpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab h)
    refine ⟨(x - a) / (b - a), ⟨div_nonneg (sub_nonneg.mpr hx.1) hpos.le, ?_⟩, ?_⟩
    · exact (div_le_one hpos).mpr (sub_le_sub_right hx.2 a)
    · rw [mul_div_cancel₀ _ hpos.ne']
      ring

/-- Let `a i ≤ b i` and `p.degreeOf i ≤ n i` in every coordinate. If all
degree-`n` Bernstein coefficients of the affine pullback of `p` from `[a,b]`
lie in `[L,U]`, then `p(x)` lies in `[L,U]` for every `x` in that closed box.
The variable type is finite.
Coordinates with `a i = b i` are allowed; no positive-width hypothesis is needed. -/
theorem eval_mem_Icc_of_bernsteinCoeff_box {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    (hp : ∀ i, p.degreeOf i ≤ n i) {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Icc (a i) (b i)) {L U : ℝ}
    (hL : ∀ k : (i : ι) → Fin (n i + 1),
      L ≤ bernsteinCoeff n (boxPullback a b p) (fun i => k i))
    (hU : ∀ k : (i : ι) → Fin (n i + 1),
      bernsteinCoeff n (boxPullback a b p) (fun i => k i) ≤ U) :
    eval x p ∈ Set.Icc L U := by
  classical
  choose t ht heq using fun i => exists_unit_parameter (hab i) (hx i)
  have h := eval_mem_Icc_of_bernsteinCoeff
    (fun i => (degreeOf_boxPullback_le a b p i).trans (hp i)) ht hL hU
  rw [eval_boxPullback] at h
  simpa only [heq] using h

/-- For ordered real endpoints `a ≤ b` and coordinate degrees of `p` bounded
by `n`, every value of `p` on the closed box `[a,b]` lies between the minimum
and maximum degree-`n` Bernstein coefficients of its affine pullback.
The variable type is finite; empty variable types and zero-width coordinates are allowed. -/
theorem eval_mem_Icc_bernsteinCoeff_box [DecidableEq ι] {n : ι → ℕ}
    {p : MvPolynomial ι ℝ} (hp : ∀ i, p.degreeOf i ≤ n i)
    {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (a i) (b i)) :
    eval x p ∈ Set.Icc
      ((univ : Finset ((i : ι) → Fin (n i + 1))).inf' univ_nonempty
        (fun k => bernsteinCoeff n (boxPullback a b p) (fun i => k i)))
      ((univ : Finset ((i : ι) → Fin (n i + 1))).sup' univ_nonempty
        (fun k => bernsteinCoeff n (boxPullback a b p) (fun i => k i))) := by
  apply eval_mem_Icc_of_bernsteinCoeff_box hp hab hx
  · intro k
    exact inf'_le (fun k : (i : ι) → Fin (n i + 1) =>
      bernsteinCoeff n (boxPullback a b p) (fun i => k i)) (mem_univ k)
  · intro k
    exact le_sup' (fun k : (i : ι) → Fin (n i + 1) =>
      bernsteinCoeff n (boxPullback a b p) (fun i => k i)) (mem_univ k)

/-- For ordered real endpoints `a ≤ b` and coordinate degrees of `p` bounded
by `n`, strict positivity of all degree-`n` Bernstein coefficients of the
affine box pullback implies `p(x) > 0` on the entire closed box `[a,b]`.
The variable type is finite, and zero-width coordinates are allowed. -/
theorem eval_pos_of_bernsteinCoeff_box {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    (hp : ∀ i, p.degreeOf i ≤ n i) {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Icc (a i) (b i))
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      0 < bernsteinCoeff n (boxPullback a b p) (fun i => k i)) : 0 < eval x p := by
  classical
  choose t ht heq using fun i => exists_unit_parameter (hab i) (hx i)
  have h := eval_pos_of_bernsteinCoeff
    (fun i => (degreeOf_boxPullback_le a b p i).trans (hp i)) ht hc
  rw [eval_boxPullback] at h
  simpa only [heq] using h

end MvPolynomial
