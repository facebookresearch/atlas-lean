/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.BernsteinBounds
public import MathlibExt.RingTheory.Polynomial.BernsteinConvergence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Uniform convergence of tensor Bernstein coefficients

The coefficients approach polynomial values at the associated grid points
uniformly as every coordinate degree grows. An explicit error constant gives
positive coefficient margins for strictly positive polynomials.

Reference: Garloff and Hamadneh (2016), *Convergence and Inclusion Isotonicity
of the Tensorial Rational Bernstein Form*, Theorem 1 and Remark 1,
https://d-nb.info/1163536172/34. We prove a weaker elementary estimate using
squared power exponents and twice the coordinate-degree threshold.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {ι : Type*} [Fintype ι]

/-- A nonnegative error constant for a real polynomial in finitely many
variables: sum the absolute power coefficients weighted by the sum of the
squared coordinate exponents. For box estimates use the affine pullback
polynomial, since its power coefficients depend on the box endpoints. -/
noncomputable def bernsteinErrorConstant (p : MvPolynomial ι ℝ) : ℝ :=
  p.coeff.sum fun d c => |c| * ∑ i, (d i : ℝ)^2

/-- The Bernstein error constant of a monomial is its absolute coefficient
multiplied by the sum of squared coordinate exponents. -/
@[simp] theorem bernsteinErrorConstant_monomial (d : ι →₀ ℕ) (c : ℝ) :
    bernsteinErrorConstant (monomial d c) = |c| * ∑ i, (d i : ℝ)^2 := by
  exact sum_monomial_eq (by simp)

/-- A constant polynomial has zero Bernstein coefficient error constant. -/
@[simp] theorem bernsteinErrorConstant_C (c : ℝ) :
    bernsteinErrorConstant (C c : MvPolynomial ι ℝ) = 0 := by
  change bernsteinErrorConstant (monomial 0 c : MvPolynomial ι ℝ) = 0
  rw [bernsteinErrorConstant_monomial]
  simp

/-- The Bernstein coefficient error constant is nonnegative. -/
theorem bernsteinErrorConstant_nonneg (p : MvPolynomial ι ℝ) :
    0 ≤ bernsteinErrorConstant p := by
  unfold bernsteinErrorConstant Finsupp.sum
  exact sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)

/-- For a real polynomial `p` in finitely many variables, let `N > 0` be at
least twice every coordinate degree of `p`. If every expansion degree `n i`
is at least `N`, then every valid Bernstein coefficient differs from `p` at
its grid point `k i / n i` by at most `bernsteinErrorConstant p / N`.
The degrees may be heterogeneous and the variable type may be empty. -/
theorem abs_bernsteinCoeff_sub_eval_le {p : MvPolynomial ι ℝ} {N : ℕ}
    (hN : 0 < N) (hp : ∀ i, 2 * p.degreeOf i ≤ N) {n : ι → ℕ}
    (hn : ∀ i, N ≤ n i) {k : ι → ℕ} (hk : ∀ i, k i ≤ n i) :
    |bernsteinCoeff n p k - eval (fun i => (k i : ℝ) / n i) p| ≤
      bernsteinErrorConstant p / N := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR (i : ι) : (0 : ℝ) < n i := by exact_mod_cast hN.trans_le (hn i)
  have hterm (d : ι →₀ ℕ) (hd : d ∈ p.support) :
      |(∏ i, ((k i).choose (d i) : ℝ) / (n i).choose (d i)) -
        ∏ i, ((k i : ℝ) / n i) ^ d i| ≤ ∑ i, (d i : ℝ)^2 / N := by
    have hdi (i : ι) : 2 * d i ≤ n i :=
      (Nat.mul_le_mul_left 2 (le_degreeOf_of_mem_support i hd)).trans ((hp i).trans (hn i))
    have hc (i : ι) : (0 : ℝ) < (n i).choose (d i) := by
      exact_mod_cast Nat.choose_pos (show d i ≤ n i by have := hdi i; omega)
    apply (Finset.abs_prod_sub_prod_le_sum_of_mem_Icc univ
      (f := fun i => ((k i).choose (d i) : ℝ) / (n i).choose (d i))
      (g := fun i => ((k i : ℝ) / n i) ^ d i)
      (fun i _ => ⟨div_nonneg (Nat.cast_nonneg _) (hc i).le,
        (div_le_one (hc i)).mpr (by exact_mod_cast Nat.choose_le_choose (d i) (hk i))⟩)
      (fun i _ => ⟨pow_nonneg (div_nonneg (Nat.cast_nonneg _) (hnR i).le) _,
        pow_le_one₀ (div_nonneg (Nat.cast_nonneg _) (hnR i).le)
          ((div_le_one (hnR i)).mpr (by exact_mod_cast hk i))⟩)).trans
    apply sum_le_sum
    intro i _
    exact (bernsteinPolynomial.abs_choose_ratio_sub_pow_le (hN.trans_le (hn i))
      (hk i) (hdi i)).trans (div_le_div_of_nonneg_left (sq_nonneg _) hNR
        (by exact_mod_cast hn i))
  rw [bernsteinCoeff, sum_def, eval_eq', ← sum_sub_distrib]
  calc
    _ = |∑ d ∈ p.support, p.coeff d *
        ((∏ i, ((k i).choose (d i) : ℝ) / (n i).choose (d i)) -
          ∏ i, ((k i : ℝ) / n i) ^ d i)| := by
      congr 1
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ p.support, |p.coeff d| *
        |(∏ i, ((k i).choose (d i) : ℝ) / (n i).choose (d i)) -
          ∏ i, ((k i : ℝ) / n i) ^ d i| := by
      simpa only [abs_mul] using abs_sum_le_sum_abs
        (fun d => p.coeff d * ((∏ i, ((k i).choose (d i) : ℝ) / (n i).choose (d i)) -
          ∏ i, ((k i : ℝ) / n i) ^ d i)) p.support
    _ ≤ ∑ d ∈ p.support, |p.coeff d| * (∑ i, (d i : ℝ)^2 / N) :=
      sum_le_sum fun d hd => mul_le_mul_of_nonneg_left (hterm d hd) (abs_nonneg _)
    _ = _ := by
      simp only [← sum_div, ← mul_div_assoc, bernsteinErrorConstant, sum_def]

/-- Let `N > 0` be at least twice every coordinate degree of a real polynomial
in finitely many variables, and let every expansion degree `n i` be at least
`N`. A lower bound `μ` on the closed unit cube gives the coefficient lower
bound `μ - bernsteinErrorConstant p / N` at every valid index `k i ≤ n i`.
No sign assumption on `μ` is needed. -/
theorem le_bernsteinCoeff_of_cube_lower_bound {p : MvPolynomial ι ℝ} {N : ℕ}
    (hN : 0 < N) (hp : ∀ i, 2 * p.degreeOf i ≤ N) {n : ι → ℕ}
    (hn : ∀ i, N ≤ n i) {μ : ℝ}
    (hμ : ∀ x : ι → ℝ, (∀ i, x i ∈ Set.Icc 0 1) → μ ≤ eval x p)
    {k : ι → ℕ} (hk : ∀ i, k i ≤ n i) :
    μ - bernsteinErrorConstant p / N ≤ bernsteinCoeff n p k := by
  have hgrid : ∀ i, (k i : ℝ) / n i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have hni : (0 : ℝ) < n i := by exact_mod_cast hN.trans_le (hn i)
    exact ⟨div_nonneg (Nat.cast_nonneg _) hni.le,
      (div_le_one hni).mpr (by exact_mod_cast hk i)⟩
  have hlower := hμ _ hgrid
  have herr := (abs_le.mp (abs_bernsteinCoeff_sub_eval_le hN hp hn hk)).1
  linarith

/-- A real polynomial in finitely many variables with lower bound `μ` on
the closed unit cube has strictly positive Bernstein coefficients whenever
`N > 0`, `N` is at least twice every coordinate degree, all expansion degrees
are at least `N`, and its error bound `bernsteinErrorConstant p / N` is below `μ`. -/
theorem bernsteinCoeff_pos_of_error_lt {p : MvPolynomial ι ℝ} {N : ℕ}
    (hN : 0 < N) (hp : ∀ i, 2 * p.degreeOf i ≤ N) {n : ι → ℕ}
    (hn : ∀ i, N ≤ n i) {μ : ℝ}
    (hμ : ∀ x : ι → ℝ, (∀ i, x i ∈ Set.Icc 0 1) → μ ≤ eval x p)
    (herror : bernsteinErrorConstant p / N < μ) {k : ι → ℕ}
    (hk : ∀ i, k i ≤ n i) : 0 < bernsteinCoeff n p k :=
  (sub_pos.mpr herror).trans_le (le_bernsteinCoeff_of_cube_lower_bound hN hp hn hμ hk)

/-- If a real polynomial in finitely many variables is strictly positive
throughout the closed unit cube, all its valid Bernstein coefficients are
strictly positive for every coordinate degree vector above one threshold.
The threshold is positive; heterogeneous degrees and empty variable types
are included. Strict positivity is essential to this completeness statement. -/
theorem exists_pos_bernsteinCoeff_of_pos {p : MvPolynomial ι ℝ}
    (hpos : ∀ x : ι → ℝ, (∀ i, x i ∈ Set.Icc 0 1) → 0 < eval x p) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ι → ℕ, (∀ i, N ≤ n i) →
      ∀ k : ι → ℕ, (∀ i, k i ≤ n i) → 0 < bernsteinCoeff n p k := by
  classical
  have hcompact : IsCompact (Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1)) := isCompact_Icc
  obtain ⟨μ, hμpos, hμ⟩ := hcompact.exists_forall_le' p.continuous_eval.continuousOn
    (fun x hx => hpos x (fun i => ⟨hx.1 i, hx.2 i⟩))
  obtain ⟨M, hM⟩ := exists_nat_gt (bernsteinErrorConstant p / μ)
  let N := max (M + 1) (univ.sup fun i => 2 * p.degreeOf i)
  have hN : 0 < N := (Nat.succ_pos M).trans_le (le_max_left _ _)
  have hdegree (i : ι) : 2 * p.degreeOf i ≤ N :=
    (le_sup (f := fun i => 2 * p.degreeOf i) (mem_univ i)).trans (le_max_right _ _)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN : (M : ℝ) < N := by exact_mod_cast Nat.lt_of_succ_le (le_max_left (M+1) _)
  have herror : bernsteinErrorConstant p / N < μ :=
    (div_lt_iff₀ hNR).mpr (by
      have := (div_lt_iff₀ hμpos).mp (hM.trans hMN)
      linarith)
  refine ⟨N, hN, fun n hn k hk => ?_⟩
  exact bernsteinCoeff_pos_of_error_lt hN hdegree hn
    (fun x hx => hμ x ⟨fun i => (hx i).1, fun i => (hx i).2⟩) herror hk

/-- If a real polynomial in finitely many variables is strictly positive
on an ordered closed box, its affine pullback has strictly positive valid
Bernstein coefficients at every sufficiently large coordinate degree vector.
Zero-width coordinates, fully collapsed boxes and empty variable types are
allowed; positivity is required on the entire closed box. -/
theorem exists_pos_bernsteinCoeff_box_of_pos {p : MvPolynomial ι ℝ} {a b : ι → ℝ}
    (hab : ∀ i, a i ≤ b i)
    (hpos : ∀ x : ι → ℝ, (∀ i, x i ∈ Set.Icc (a i) (b i)) → 0 < eval x p) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ι → ℕ, (∀ i, N ≤ n i) →
      ∀ k : ι → ℕ, (∀ i, k i ≤ n i) → 0 < bernsteinCoeff n (boxPullback a b p) k := by
  apply exists_pos_bernsteinCoeff_of_pos
  intro x hx
  rw [eval_boxPullback]
  apply hpos
  intro i
  have hw := sub_nonneg.mpr (hab i)
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hw (hx i).1)
  · have := mul_le_mul_of_nonneg_left (hx i).2 hw
    linarith

end MvPolynomial
