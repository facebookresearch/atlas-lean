/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.SchurSiegelSmyth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.MahlerMeasure
import Mathlib.RingTheory.Discriminant

/-!
# Schur's lower bound for the Schur–Siegel–Smyth trace constant

We prove Schur's lower bound `√e` using the discriminant and monic polynomials
obtained by differentiating a holomorphic generating function. Cauchy's estimate bounds the
determinant of their evaluations, which rules out sufficiently large degrees below any fixed
threshold less than `√e`. Northcott's theorem gives finiteness for the remaining degrees.
-/

public section

open scoped BigOperators NNReal Topology
open Filter Finset Polynomial Set

namespace MathlibExt.NumberTheory.SchurSiegelSmyth
namespace schur1918LowerBound_wanted

-- These polynomials encode the derivatives of the generating function.
private noncomputable def derivativePolynomial : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => (X - C (n : ℂ)) * derivativePolynomial n -
      X * (derivativePolynomial n).derivative

private lemma derivativePolynomial_monic_degree (n : ℕ) :
    (derivativePolynomial n).Monic ∧ (derivativePolynomial n).natDegree = n := by
  induction n with
  | zero => simp [derivativePolynomial]
  | succ n ih =>
    obtain ⟨hm, hd⟩ := ih
    rw [derivativePolynomial]
    have hdeg : ((X - C (n : ℂ)) * derivativePolynomial n).natDegree = n + 1 := by
      rw [natDegree_mul (X_sub_C_ne_zero _) hm.ne_zero, natDegree_X_sub_C, hd, add_comm]
    have hlt : (X * (derivativePolynomial n).derivative).natDegree < n + 1 := by
      cases n with
      | zero => simp [derivative_of_natDegree_zero hd]
      | succ n =>
        have h := natDegree_mul_le
          (p := (X : ℂ[X])) (q := (derivativePolynomial (n + 1)).derivative)
        simp only [natDegree_X, natDegree_derivative, hd] at h
        omega
    rw [← hdeg] at hlt
    exact ⟨((monic_X_sub_C _).mul hm).sub_of_left (degree_lt_degree hlt),
      (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hdeg⟩

private noncomputable def reciprocal (z : ℂ) : ℂ := (1 + z)⁻¹

private noncomputable def generatingFunction (x z : ℂ) : ℂ :=
  Complex.exp (x * (1 - reciprocal z))

private lemma hasDerivAt_reciprocal {z : ℂ} (hz : 1 + z ≠ 0) :
    HasDerivAt reciprocal (-(reciprocal z) ^ 2) z := by
  convert ((hasDerivAt_const z (1 : ℂ)).add (hasDerivAt_id z)).inv hz using 1
  · rfl
  · simp [reciprocal, div_eq_mul_inv, inv_pow]

private lemma hasDerivAt_generatingFunction (x : ℂ) {z : ℂ} (hz : 1 + z ≠ 0) :
    HasDerivAt (generatingFunction x) (generatingFunction x z * (x * reciprocal z ^ 2)) z := by
  convert (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_reciprocal hz)).const_mul x).cexp using 1
  · rfl
  · simp [generatingFunction, Pi.sub_apply]

private lemma iteratedDeriv_generatingFunction (n : ℕ) (x : ℂ) {z : ℂ} (hz : 1 + z ≠ 0) :
    iteratedDeriv n (generatingFunction x) z =
      generatingFunction x z * reciprocal z ^ n *
        (derivativePolynomial n).eval (x * reciprocal z) := by
  induction n generalizing z with
  | zero => simp [derivativePolynomial]
  | succ n ih =>
    have hy := hasDerivAt_reciprocal hz
    have hf := hasDerivAt_generatingFunction x hz
    have hp := ((derivativePolynomial n).hasDerivAt (x * reciprocal z)).comp z (hy.const_mul x)
    have h := (hf.mul (hy.pow n)).mul hp
    have hn : ∀ᶠ w : ℂ in 𝓝 z, 1 + w ≠ 0 :=
      (continuous_const.add continuous_id).continuousAt.eventually_ne hz
    have he : iteratedDeriv n (generatingFunction x) =ᶠ[𝓝 z]
        fun w ↦ generatingFunction x w * reciprocal w ^ n *
          (derivativePolynomial n).eval (x * reciprocal w) := hn.mono fun _ hw ↦ ih hw
    change HasDerivAt (fun w ↦ generatingFunction x w * reciprocal w ^ n *
      (derivativePolynomial n).eval (x * reciprocal w)) _ z at h
    rw [iteratedDeriv_succ, he.deriv_eq, h.deriv]
    simp only [derivativePolynomial, eval_sub, eval_mul, eval_X, eval_C, pow_succ,
      Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
    cases n with
    | zero => simp [derivativePolynomial]; ring
    | succ n =>
      simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ]
      ring

private lemma norm_derivativePolynomial_eval_le {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r)
    (hr' : r < 1) (n : ℕ) :
    ‖(derivativePolynomial n).eval (x : ℂ)‖ ≤ n.factorial * Real.exp (x / 2) / r ^ n := by
  have hne (z : ℂ) (hz : ‖z‖ ≤ r) : 1 + z ≠ 0 := by
    intro he
    have hh : z = -1 := by linear_combination he
    rw [hh, norm_neg, norm_one] at hz
    exact (not_le_of_gt hr') hz
  have hd : DiffContOnCl ℂ (generatingFunction x) (Metric.ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hn := hne z (by
      simpa [Metric.mem_closedBall, dist_zero_right] using Metric.closure_ball_subset_closedBall hz)
    exact (hasDerivAt_generatingFunction x hn).differentiableAt.differentiableWithinAt
  have hc (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) r) :
      ‖generatingFunction x z‖ ≤ Real.exp (x / 2) := by
    have hnorm : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hn := hne z hnorm.le
    have hpos : 0 < Complex.normSq (1 + z) := Complex.normSq_pos.mpr hn
    have hzsq : Complex.normSq z ≤ 1 := by
      rw [← Complex.sq_norm, hnorm]
      nlinarith
    have hre : (1 - reciprocal z).re ≤ 1 / 2 := by
      simp only [Complex.sub_re, Complex.one_re, reciprocal, Complex.inv_re, Complex.add_re]
      suffices (1 / 2 : ℝ) ≤ (1 + z.re) / Complex.normSq (1 + z) by linarith
      apply (le_div_iff₀ hpos).mpr
      rw [Complex.normSq_apply] at hzsq ⊢
      simp
      nlinarith
    rw [generatingFunction, Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hre hx])
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hd hc
  have h0 : (1 : ℂ) + 0 ≠ 0 := by simp
  simpa [iteratedDeriv_generatingFunction n (x : ℂ) h0, generatingFunction, reciprocal] using h

-- The integral power basis gives a nonzero integer equal to the square of the determinant.
private lemma conjugates_vandermonde {α : ℂ} (hα : IsTotallyPositive α) :
    ∃ x : Fin (degree α) → ℝ, (∀ i, 0 < x i) ∧
      (∑ i, x i) = (trace α).re ∧ 1 ≤ ‖(Matrix.vandermonde fun i ↦ (x i : ℂ)).det‖ := by
  classical
  let hQ : IsIntegral ℚ α := hα.1.tower_top
  let pb := IntermediateField.adjoin.powerBasis hQ
  let := pb.finite
  let roots : Finset ℂ :=
    ⟨conjugates α, Polynomial.nodup_roots (minpoly.irreducible hQ).separable.map⟩
  have hcard : roots.card = degree α := IsAlgClosed.card_aroots_eq_natDegree
  let ix := (roots.equivFinOfCardEq hcard).symm
  let x : Fin (degree α) → ℝ := fun i ↦ (ix i : ℂ).re
  have hroot (i : Fin (degree α)) : (ix i : ℂ) ∈ conjugates α := (ix i).property
  refine ⟨x, fun i ↦ (hα.2 _ (hroot i)).2, ?_, ?_⟩
  · change (∑ i, x i) = roots.val.sum.re
    rw [Finset.sum_val roots, Complex.re_sum]
    exact (ix.sum_comp fun i ↦ (i : ℂ).re).trans (Finset.sum_coe_sort roots Complex.re)
  let e := ix.trans (IntermediateField.algHomAdjoinIntegralEquiv (K := ℂ) ℚ hQ).symm
  have he (i : Fin (degree α)) : e i pb.gen = (x i : ℂ) := by
    change (IntermediateField.algHomAdjoinIntegralEquiv (K := ℂ) ℚ hQ).symm
        ⟨(ix i : ℂ), hroot i⟩ pb.gen = _
    rw [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
    exact (Complex.re_add_im _).symm.trans (by simp [x, (hα.2 _ (hroot i)).1])
  have hg : IsIntegral ℤ pb.gen := by
    apply (isIntegral_algebraMap_iff (B := ℂ)).mp
    simpa [pb, IntermediateField.algebraMap_apply] using hα.1
  have hD := Algebra.discr_isIntegral ℚ (b := pb.basis) fun i ↦ by
    rw [pb.basis_eq_pow]
    exact hg.pow _
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hD
  have hm0 : m ≠ 0 := by
    intro h0
    apply Algebra.discr_not_zero_of_basis ℚ pb.basis
    simpa [h0] using hm.symm
  let e' : Fin pb.dim ≃ _ := e
  have hdisc := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ pb.basis e'
  rw [Algebra.embeddingsMatrixReindex_eq_vandermonde ℂ pb e', Matrix.det_transpose]
    at hdisc
  change (algebraMap ℚ ℂ) (Algebra.discr ℚ pb.basis) =
    (Matrix.vandermonde fun i ↦ e i pb.gen).det ^ 2 at hdisc
  rw [show (fun i ↦ e i pb.gen) = (fun i ↦ (x i : ℂ)) from funext he, ← hm,
    ← IsScalarTower.algebraMap_apply] at hdisc
  have hnorm := congrArg norm hdisc
  simp only [norm_pow, eq_intCast, Complex.norm_intCast] at hnorm
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
  nlinarith [norm_nonneg (Matrix.vandermonde fun i ↦ (x i : ℂ)).det]

private lemma norm_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n → ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ a i * b j) :
    ‖A.det‖ ≤ n.factorial * ((∏ i, a i) * ∏ j, b j) := by
  rw [Matrix.det_apply']
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (∏ i, a i) * ∏ j, b j := by
      apply Finset.sum_le_sum
      intro σ _
      have hs : ‖((Equiv.Perm.sign σ : ℤˣ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ]
      rw [norm_mul, hs, one_mul, norm_prod, ← Equiv.prod_comp σ a, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ h (σ i) i
    _ = _ := by simp [Fintype.card_perm, nsmul_eq_mul]

-- Scaling the conjugates makes the row factors contribute at most exp(n²/2).
private lemma vandermonde_bound {n : ℕ} (hn : 0 < n) {ρ r : ℝ} (hρ : 0 < ρ)
    (hr : 0 < r) (hr' : r < 1) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsum : ∑ i, x i ≤ n * ρ) :
    ‖(Matrix.vandermonde fun i ↦ (x i : ℂ)).det‖ ≤
      n.factorial * (Real.exp ((n : ℝ) ^ 2 / 2) *
        ∏ j : Fin n, (j.val.factorial : ℝ) / (r * n / ρ) ^ j.val) := by
  let c : ℝ := n / ρ
  have hc : 0 < c := div_pos (by exact_mod_cast hn) hρ
  let y (i : Fin n) : ℝ := c * x i
  let A := Matrix.of fun i j : Fin n ↦
    ((c : ℂ) ^ j.val)⁻¹ * (derivativePolynomial j).eval (y i : ℂ)
  have hdet : A.det = (Matrix.vandermonde fun i ↦ (x i : ℂ)).det := by
    have hscale : Matrix.vandermonde (fun i ↦ (y i : ℂ)) =
        Matrix.vandermonde (fun i ↦ (x i : ℂ)) *
          Matrix.diagonal (fun j : Fin n ↦ (c : ℂ) ^ j.val) := by
      ext i j
      simp [Matrix.vandermonde, y, mul_pow, mul_comm]
    let W := Matrix.of fun i j : Fin n ↦ (derivativePolynomial j).eval (y i : ℂ)
    change (Matrix.of fun i j : Fin n ↦ ((c : ℂ) ^ j.val)⁻¹ * W i j).det = _
    rw [Matrix.det_mul_row]
    change (∏ j : Fin n, ((c : ℂ) ^ j.val)⁻¹) *
      (Matrix.of fun i j : Fin n ↦ (derivativePolynomial j).eval (y i : ℂ)).det = _
    rw [← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun i ↦ (y i : ℂ)) (fun j ↦ derivativePolynomial j)
      (fun j ↦ (derivativePolynomial_monic_degree j).2)
      (fun j ↦ (derivativePolynomial_monic_degree j).1), hscale, Matrix.det_mul,
      Matrix.det_diagonal, Finset.prod_inv_distrib]
    have hprod : (∏ j : Fin n, (c : ℂ) ^ j.val) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun _ _ ↦ pow_ne_zero _ (by exact_mod_cast hc.ne')
    rw [mul_left_comm, inv_mul_cancel₀ hprod, mul_one]
  have hy (i : Fin n) : 0 ≤ y i := mul_nonneg hc.le (hx i)
  have hA := norm_det_le A (fun i ↦ Real.exp (y i / 2))
    (fun j ↦ (j.val.factorial : ℝ) / (r * c) ^ j.val) (fun i j ↦ ?_)
  · rw [← hdet]
    refine hA.trans ?_
    rw [← Real.exp_sum, ← Finset.sum_div, show r * c = r * n / ρ by unfold c; ring]
    gcongr
    have hs : ∑ i, y i ≤ (n : ℝ) ^ 2 := by
      simp only [y, ← Finset.mul_sum]
      calc
        c * ∑ i, x i ≤ c * (n * ρ) := mul_le_mul_of_nonneg_left hsum hc.le
        _ = _ := by dsimp [c]; field_simp
    linarith
  · change ‖((c : ℂ) ^ j.val)⁻¹ * (derivativePolynomial j).eval (y i : ℂ)‖ ≤ _
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le]
    calc
      _ ≤ (c ^ j.val)⁻¹ * (j.val.factorial * Real.exp (y i / 2) / r ^ j.val) :=
        mul_le_mul_of_nonneg_left (norm_derivativePolynomial_eval_le (hy i) hr hr' j)
          (by positivity)
      _ = _ := by rw [mul_pow]; ring

private lemma sum_triangular (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ range n, ∑ j ∈ Ico 1 (k + 1), f j) =
      ∑ j ∈ Ico 1 n, ((n : ℝ) - j) * f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with _ | n
    · simp
    · rw [sum_range_succ, ih, sum_Ico_succ_top (Nat.succ_pos n),
        sum_Ico_succ_top (Nat.succ_pos n)
          (fun j ↦ ((n + 1 + 1 : ℕ) - (j : ℝ)) * f j)]
      push_cast
      rw [← add_assoc, ← sum_add_distrib]
      simp only [add_sub_cancel_left, one_mul]
      congr 1
      apply sum_congr rfl
      intro j _
      ring

-- The normalized logarithms of the factorials are bounded by a single integral.
private lemma sum_log_factorial_sub (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range n, (Real.log (k.factorial : ℝ) - k * Real.log n)) ≤
      -(3 / 4 : ℝ) * n ^ 2 + n * (Real.log n + 1) := by
  have hn1 : (1 : ℕ) ≤ n := hn
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnr : (0 : ℝ) < n := by positivity
  let f (x : ℝ) := ((n : ℝ) - x) * Real.log (x / n)
  have heq (k : ℕ) :
      Real.log (k.factorial : ℝ) - k * Real.log n =
        ∑ j ∈ Ico 1 (k + 1), Real.log ((j : ℝ) / n) := by
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel, ← Real.sum_log_add_one_eq_log_factorial]
    simp only [Nat.cast_add, Nat.cast_one, add_comm 1]
    have hlog (j : ℕ) : Real.log (((j : ℝ) + 1) / n) =
        Real.log ((j : ℝ) + 1) - Real.log n := Real.log_div (by positivity) hnr.ne'
    simp_rw [hlog, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  simp_rw [heq]
  rw [sum_triangular]
  have hmono : MonotoneOn f (Set.Icc 1 (n : ℝ)) := by
    intro x hx y hy hxy
    dsimp [f]
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    have hypos := hxpos.trans_le hxy
    have hyle : Real.log (y / n) ≤ 0 :=
      Real.log_nonpos (div_nonneg hypos.le hnr.le) ((div_le_one hnr).mpr hy.2)
    calc
      _ ≤ ((n : ℝ) - x) * Real.log (y / n) :=
        mul_le_mul_of_nonneg_left
          (Real.strictMonoOn_log.monotoneOn (div_pos hxpos hnr)
            (div_pos (hxpos.trans_le hxy) hnr) (by gcongr))
          (sub_nonneg.mpr hx.2)
      _ ≤ _ := mul_le_mul_of_nonpos_right (by linarith) hyle
  calc
    _ ≤ ∫ x in (1 : ℝ)..(n : ℝ), f x := by
      have hmono' : MonotoneOn f (Set.Icc ((1 : ℕ) : ℝ) (n : ℝ)) := by simpa using hmono
      simpa [f] using hmono'.sum_le_integral_Ico hn1
    _ ≤ _ := by
      let F (x : ℝ) := ((n : ℝ) * x - x ^ 2 / 2) * Real.log (x / n) - n * x + x ^ 2 / 4
      have hpos {x : ℝ} (hx : x ∈ Set.uIcc 1 (n : ℝ)) : 0 < x :=
        zero_lt_one.trans_le ((Set.uIcc_of_le hn1r ▸ hx).1)
      have hd (x : ℝ) (hx : x ∈ Set.uIcc 1 (n : ℝ)) : HasDerivAt F (f x) x := by
        have hid := hasDerivAt_id x
        have hl := (hid.div_const (n : ℝ)).log (div_pos (hpos hx) hnr).ne'
        convert ((((hid.const_mul (n : ℝ)).sub ((hid.pow 2).div_const 2)).mul hl).sub
          (hid.const_mul (n : ℝ))).add ((hid.pow 2).div_const 4) using 1
        · rfl
        · dsimp [f, id]
          field_simp [(hpos hx).ne', hnr.ne']
          ring
      have hi : IntervalIntegrable f MeasureTheory.volume 1 (n : ℝ) := by
        apply ContinuousOn.intervalIntegrable
        apply (continuous_const.sub continuous_id).continuousOn.mul
        exact Real.continuousOn_log.comp ((continuous_id.div_const _).continuousOn)
          (fun x hx ↦ (div_pos (hpos hx) hnr).ne')
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
      simp only [F, div_self hnr.ne', Real.log_one, mul_zero, one_pow, mul_one,
        Real.log_div one_ne_zero hnr.ne', zero_sub]
      nlinarith [Real.log_nonneg hn1r]

private lemma sum_fin_val_le (n : ℕ) : (∑ j : Fin n, (j.val : ℝ)) ≤ (n : ℝ) ^ 2 / 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  have h : (∑ i ∈ range n, (i : ℝ)) * 2 = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    simpa using congrArg (fun j : ℕ ↦ (j : ℝ)) (sum_range_id_mul_two n)
  have hle : (((n - 1 : ℕ) : ℝ)) ≤ n := by exact_mod_cast Nat.sub_le n 1
  nlinarith [mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

private lemma eventually_vandermonde_bound_lt_one {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < Real.sqrt (Real.exp 1)) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) ≤ n * ρ →
      ‖(Matrix.vandermonde fun i ↦ (x i : ℂ)).det‖ < 1 := by
  let b := Real.sqrt (Real.exp 1)
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨r, hrl, hrr⟩ := exists_between ((div_lt_one hb).mpr hρ' : ρ / b < 1)
  have hr : 0 < r := (div_pos hρ hb).trans hrl
  have hl : Real.log (ρ / r) < 1 / 2 := by
    have hlt : ρ / r < b := (div_lt_iff₀ hr).mpr (by
      have := (div_lt_iff₀ hb).mp hrl
      simpa [mul_comm] using this)
    have := Real.strictMonoOn_log (div_pos hρ hr) hb hlt
    simpa [b, Real.log_sqrt (Real.exp_pos (1 : ℝ)).le] using this
  let a := max 0 (Real.log (ρ / r))
  have ha : 0 ≤ a := le_max_left _ _
  have ha' : a < 1 / 2 := max_lt (by norm_num) hl
  have hloglim : Tendsto (fun n : ℕ ↦ Real.log n / n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun n : ℕ ↦ (2 * Real.log n + 1) / n) atTop (𝓝 0) := by
    simpa [add_div, mul_div_assoc, one_div] using (hloglim.const_mul 2).add hinv
  have hsmall : ∀ᶠ n : ℕ in atTop, (2 * Real.log n + 1) / n < (1 / 2 - a) / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with n hn hn' x hx hs
  have hnr : (0 : ℝ) < n := by positivity
  let B := (n.factorial : ℝ) * (Real.exp ((n : ℝ) ^ 2 / 2) *
    ∏ j : Fin n, (j.val.factorial : ℝ) / (r * n / ρ) ^ j.val)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine (vandermonde_bound hn' hρ hr hrr x hx hs).trans_lt ?_
  change B < 1
  apply (Real.strictMonoOn_log.lt_iff_lt hB zero_lt_one).mp
  rw [Real.log_one]
  have hfac : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    exact Real.strictMonoOn_log.monotoneOn (by positivity : 0 < (n.factorial : ℝ))
      (pow_pos hnr n) (by exact_mod_cast Nat.factorial_le_pow n)
  have hsum := sum_log_factorial_sub n hn'
  have hcolumns : (∑ j : Fin n, (j.val : ℝ) * Real.log (ρ / r)) ≤ (n : ℝ) ^ 2 / 2 * a := by
    calc
      _ ≤ ∑ j : Fin n, (j.val : ℝ) * a :=
        sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ ≤ _ := by rw [← sum_mul]; gcongr; exact sum_fin_val_le n
  have hbase : 0 < r * (n : ℝ) / ρ := by positivity
  have hbase_log : Real.log (r * n / ρ) = Real.log n - Real.log (ρ / r) := by
    rw [Real.log_div (by positivity) hρ.ne', Real.log_mul hr.ne' hnr.ne',
      Real.log_div hρ.ne' hr.ne']
    ring
  have hlogB : Real.log B = Real.log (n.factorial : ℝ) + (n : ℝ) ^ 2 / 2 +
      (∑ k ∈ range n, (Real.log (k.factorial : ℝ) - k * Real.log n)) +
      ∑ j : Fin n, (j.val : ℝ) * Real.log (ρ / r) := by
    simp only [B, Real.log_mul (by positivity : (n.factorial : ℝ) ≠ 0)
      (by positivity : Real.exp ((n : ℝ) ^ 2 / 2) *
        ∏ j : Fin n, (j.val.factorial : ℝ) / (r * n / ρ) ^ j.val ≠ 0)]
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp, Real.log_prod (by
      intro j _
      positivity)]
    have hlog (j : Fin n) : Real.log ((j.val.factorial : ℝ) / (r * n / ρ) ^ j.val) =
        (Real.log (j.val.factorial : ℝ) - j.val * Real.log n) +
          j.val * Real.log (ρ / r) := by
      rw [Real.log_div (by positivity) (pow_ne_zero _ hbase.ne'), Real.log_pow, hbase_log]
      ring
    simp only [hlog, sum_add_distrib]
    rw [← Fin.sum_univ_eq_sum_range]
    ring
  rw [hlogB]
  have hnsmall := (div_lt_iff₀ hnr).mp hn
  have hnsmall' := mul_lt_mul_of_pos_right hnsmall hnr
  nlinarith

-- Northcott's theorem for integer polynomials handles the remaining bounded degrees.
private lemma finite_of_bounded_degree_trace (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    {α : ℂ | IsTotallyPositive α ∧ absoluteTrace α < ρ ∧ degree α ≤ N}.Finite := by
  let B : ℝ≥0 := ⟨Real.exp (N * ρ), (Real.exp_pos _).le⟩
  let P : Set ℤ[X] := {p | p.natDegree ≤ N ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} \ {0}
  have hP : P.Finite := (Polynomial.finite_mahlerMeasure_le N B).sdiff
  refine (hP.biUnion (t := fun p ↦ {z : ℂ | (p.map (Int.castRingHom ℂ)).IsRoot z})
    (fun p hp ↦ ?_)).subset ?_
  · exact Polynomial.finite_setOfPred_isRoot
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (by simpa using hp.2))
  · rintro α ⟨hα, htrace, hdeg⟩
    let p := minpoly ℤ α
    let q := p.map (Int.castRingHom ℂ)
    have hmap : q = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hα.1, Polynomial.map_map]
      rfl
    have hm : p.Monic := minpoly.monic hα.1
    have hqm : q.Monic := hm.map _
    have hqd : q.natDegree = degree α := by
      rw [hmap, (minpoly.monic hα.1.tower_top).natDegree_map]
      rfl
    have hroots : q.roots = conjugates α := by rw [hmap]; rfl
    have hsum : (q.roots.map Complex.re).sum = (trace α).re := by
      rw [hroots, trace]
      exact (map_multiset_sum Complex.reAddGroupHom _).symm
    have ht : (trace α).re ≤ N * ρ := by
      have hp : (0 : ℝ) < degree α := by exact_mod_cast degree_pos_of_isIntegral_int hα.1
      have ht := (div_lt_iff₀ hp).mp htrace
      have hb : (degree α : ℝ) ≤ N := by exact_mod_cast hdeg
      exact ht.le.trans (by rw [mul_comm ρ]; gcongr)
    have hM : q.mahlerMeasure ≤ B := calc
      _ = (q.roots.map (fun z ↦ max 1 ‖z‖)).prod := by
        simp [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hqm.leadingCoeff]
      _ ≤ (q.roots.map (fun z ↦ Real.exp z.re)).prod := by
        apply Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity)
        intro z hz
        rw [hroots] at hz
        obtain ⟨him, hp⟩ := hα.2 z hz
        have hreal : (z.re : ℂ) = z := by
          apply Complex.ext <;> simp [him]
        have hnorm : ‖z‖ = z.re := by
          simpa only [Complex.norm_real, Real.norm_of_nonneg hp.le] using congrArg norm hreal.symm
        rw [hnorm]
        exact max_le (by linarith [Real.add_one_le_exp z.re])
          (by linarith [Real.add_one_le_exp z.re])
      _ = Real.exp (trace α).re := by
        rw [← hsum, Real.exp_multiset_sum, Multiset.map_map]
        rfl
      _ ≤ B := Real.exp_le_exp.mpr ht
    have hpd : p.natDegree = degree α := (hm.natDegree_map _).symm.trans hqd
    have hroot : q.IsRoot α := by
      apply (mem_roots hqm.ne_zero).mp
      rw [hroots]
      exact self_mem_conjugates hα.1
    exact Set.mem_iUnion₂.mpr ⟨p, ⟨⟨hpd.le.trans hdeg, hM⟩, by simpa using hm.ne_zero⟩, hroot⟩

private lemma isAdmissible_of_lt {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < Real.sqrt (Real.exp 1)) : IsAdmissible ρ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_vandermonde_bound_lt_one hρ hρ')
  refine ⟨hρ.le, (finite_of_bounded_degree_trace N hρ).subset ?_⟩
  rintro α ⟨hα, ht⟩
  refine ⟨hα, ht, ?_⟩
  by_contra! hd
  obtain ⟨x, hx, hsum, hdet⟩ := conjugates_vandermonde hα
  have hn : (0 : ℝ) < degree α := by exact_mod_cast degree_pos_of_isIntegral_int hα.1
  have htrace : ∑ i, x i ≤ degree α * ρ := by
    rw [hsum, mul_comm]
    exact ((div_lt_iff₀ hn).mp ht).le
  exact (not_lt_of_ge hdet) (hN _ hd.le x (fun i ↦ (hx i).le) htrace)

end schur1918LowerBound_wanted

/-- **Schur's lower bound for the Schur–Siegel–Smyth constant.** The Schur–Siegel–Smyth trace
constant $C_{86}$, an extended real number, satisfies $\sqrt{e} \le C_{86}$.

Source: Schur (1918), lower bound `√e ≤ C₈₆`. -/
theorem schur1918LowerBound_wanted :
    ((Real.sqrt (Real.exp 1) : ℝ) : EReal) ≤ schurSiegelSmythConstant := by
  by_contra! h
  obtain ⟨ρ, hc, hρ⟩ := EReal.lt_iff_exists_real_btwn.mp h
  have hpos : 0 < ρ := EReal.coe_lt_coe_iff.mp (by
    simpa using zero_le_schurSiegelSmythConstant.trans_lt hc)
  exact hc.not_ge (coe_le_schurSiegelSmythConstant
    (schur1918LowerBound_wanted.isAdmissible_of_lt hpos (EReal.coe_lt_coe_iff.mp hρ)))

end MathlibExt.NumberTheory.SchurSiegelSmyth
