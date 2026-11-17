/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.HadamardFactorization

/-!
# Tests for Hadamard factorization of entire functions of order at most one

The factorization theorem is instantiated at the zero-free `exp`, and the auxiliary results at
small concrete functions.
-/

@[expose] public section

open Filter Asymptotics Bornology Complex

private lemma exp_hasGrowthOrderLE_one : HasGrowthOrderLE Complex.exp 1 := by
  refine hasGrowthOrderLE_one_of_isBigO_exp_mul_norm (A := 1)
    (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
  rw [Complex.norm_exp, one_mul, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (Complex.re_le_norm z)

private lemma analyticOrderAt_exp (w : ℂ) : analyticOrderAt Complex.exp w = 0 :=
  (Complex.differentiable_exp.analyticAt w).analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero w)

/-- **Hadamard at `exp`.** The hypotheses are met with the empty family of zeros. -/
example : ∃ A B : ℂ, ∀ s, Complex.exp s =
    Complex.exp (A + B * s) * ∏' n : Empty, (1 - s / Empty.elim n) * Complex.exp (s / Empty.elim n) :=
  exists_eq_exp_mul_tprod_of_hasGrowthOrderLE_one Complex.differentiable_exp
    exp_hasGrowthOrderLE_one (Complex.exp_ne_zero 0) fun w => by simp [analyticOrderAt_exp]

/-- The canonical indexing of the zeros of `exp` is empty. -/
example : IsEmpty (Σ w : ℂ, Fin (analyticOrderAt Complex.exp w).toNat) :=
  ⟨fun n => by simpa [analyticOrderAt_exp] using n.2.isLt⟩

example : ∃ A B : ℂ, ∀ s, Complex.exp s = Complex.exp (A + B * s) *
    ∏' n : (Σ w : ℂ, Fin (analyticOrderAt Complex.exp w).toNat),
      (1 - s / n.1) * Complex.exp (s / n.1) :=
  exists_eq_exp_mul_tprod_sigma_of_hasGrowthOrderLE_one Complex.differentiable_exp
    exp_hasGrowthOrderLE_one (Complex.exp_ne_zero 0)

/-- An entire logarithm of `exp` itself. -/
example : ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 = Complex.log (Complex.exp 0) ∧
    ∀ z, Complex.exp z = Complex.exp (h z) :=
  exists_differentiable_eq_cexp_of_ne_zero Complex.differentiable_exp Complex.exp_ne_zero

private lemma re_sq_le (z : ℂ) : ((fun z : ℂ => z ^ 2) z).re ≤ 0 + 1 * ‖z‖ ^ (2 : ℝ) := by
  rw [zero_add, one_mul, Real.rpow_two]
  exact (Complex.re_le_norm _).trans (by rw [norm_pow])

/-- `Re (z²) ≤ ‖z‖²` kills the Taylor coefficients of order `≥ 3` of `z ↦ z²`. -/
example : iteratedDeriv 3 (fun z : ℂ => z ^ 2) 0 = 0 :=
  iteratedDeriv_eq_zero_of_re_le_rpow (by fun_prop) two_pos zero_le_one re_sq_le (by norm_num)

/-- A degree-two polynomial is its degree-two Taylor polynomial. -/
example (z : ℂ) : z ^ 2 = ∑ n ∈ Finset.range (2 + 1),
    (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun z : ℂ => z ^ 2) 0 * z ^ n :=
  eq_sum_range_of_iteratedDeriv_eq_zero (h := fun z : ℂ => z ^ 2) (by fun_prop)
    (fun n hn => iteratedDeriv_eq_zero_of_re_le_rpow (by fun_prop) two_pos zero_le_one re_sq_le
      (by exact_mod_cast hn)) z

/-- The affine conclusion: `h z = 3 z` has real part `≤ 3 ‖z‖ ≤ 3 ‖z‖ ^ (1 + ε)`. -/
example : ∃ B : ℂ, ∀ z, 3 * z = B * z :=
  exists_eq_mul_of_re_le_rpow_one_add (h := fun z => 3 * z) (by fun_prop) (by simp)
    fun ε hε => ⟨3, by
      filter_upwards [(Metric.cobounded_eq_cocompact (α := ℂ)) ▸
        (tendsto_norm_cobounded_atTop (E := ℂ)).eventually (eventually_ge_atTop 1)] with z hz
      have h1 : ‖z‖ ≤ ‖z‖ ^ (1 + ε) := by
        conv_lhs => rw [← Real.rpow_one ‖z‖]
        exact Real.rpow_le_rpow_of_exponent_le hz (by linarith)
      calc (3 * z).re = 3 * z.re := by simp
        _ ≤ 3 * ‖z‖ := by linarith [Complex.re_le_norm z]
        _ ≤ 3 * ‖z‖ ^ (1 + ε) := by linarith⟩

/-- Every point of the canonical enumeration is a zero (here for `z ↦ z`). -/
example (n : Σ w : ℂ, Fin (analyticOrderAt (fun z : ℂ => z) w).toNat) : n.1 = 0 :=
  apply_fst_eq_zero_of_sigma_fin_analyticOrderAt (f := fun z : ℂ => z) n

example (w : ℂ) : analyticOrderAt (fun z : ℂ => z) w ≠ ⊤ :=
  analyticOrderAt_ne_top_of_differentiable (w₀ := 1) differentiable_id one_ne_zero w
