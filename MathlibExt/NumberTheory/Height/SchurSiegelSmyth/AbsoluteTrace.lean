/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.SchurSiegelSmyth
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The elementary lower bound for the absolute trace
-/

public section

namespace MathlibExt.NumberTheory.SchurSiegelSmyth

private theorem one_le_norm_prod_conjugates {α : ℂ} (hα : IsIntegral ℤ α) (h0 : α ≠ 0) :
    1 ≤ ‖(conjugates α).prod‖ := by
  have hQ : IsIntegral ℚ α := hα.tower_top
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hα
  have hc : (minpoly ℤ α).coeff 0 ≠ 0 := by
    intro hz
    apply minpoly.coeff_zero_ne_zero hQ h0
    simp [hmap, Polynomial.coeff_map, hz]
  have hprod := (IsAlgClosed.splits ((minpoly ℚ α).map (algebraMap ℚ ℂ)))
    |>.coeff_zero_eq_prod_roots_of_monic ((minpoly.monic hQ).map _)
  calc
    1 ≤ |((minpoly ℤ α).coeff 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hc
    _ = ‖((minpoly ℚ α).map (algebraMap ℚ ℂ)).coeff 0‖ := by
      simp [hmap, Polynomial.coeff_map, Complex.norm_intCast]
    _ = ‖(conjugates α).prod‖ := by rw [hprod]; simp [norm_pow, conjugates, Polynomial.aroots]

/-- **Absolute trace of a totally positive algebraic integer is at least one.** For every
complex number $\alpha$ that is a totally positive algebraic integer, the absolute trace of
$\alpha$ is at least $1$.

Source: catalogue trivial lower row, by AM--GM: the absolute trace
is at least the geometric mean of the conjugates, whose product is a
nonzero rational integer. -/
theorem absoluteTrace_one_le_wanted (α : ℂ)
    (hα : IsTotallyPositive α) :
    1 ≤ absoluteTrace α := by
  classical
  have hQ : IsIntegral ℚ α := hα.1.tower_top
  let s : Finset ℂ :=
    ⟨conjugates α, Polynomial.nodup_roots (minpoly.irreducible hQ).separable.map⟩
  have hcard : s.card = degree α := IsAlgClosed.card_aroots_eq_natDegree
  have hd : (0 : ℝ) < s.card := by
    rw [hcard]
    exact_mod_cast degree_pos_of_isIntegral_int hα.1
  have hnorm (z : ℂ) (hz : z ∈ s) : ‖z‖ = z.re := by
    obtain ⟨him, hre⟩ := hα.2 z hz
    simp [Complex.norm_eq_sqrt_sq_add_sq, him, Real.sqrt_sq hre.le]
  have h0 : α ≠ 0 := by
    have hpos := (hα.2 α (self_mem_conjugates hα.1)).2
    rintro rfl
    simp at hpos
  have hprod : 1 ≤ ∏ z ∈ s, z.re := by
    calc
      1 ≤ ‖(conjugates α).prod‖ := one_le_norm_prod_conjugates hα.1 h0
      _ = ∏ z ∈ s, ‖z‖ := by
        rw [← norm_prod]
        exact congrArg norm s.prod_val
      _ = ∏ z ∈ s, z.re := Finset.prod_congr rfl hnorm
  have hamgm := Real.geom_mean_le_arith_mean s (fun _ ↦ 1) Complex.re
    (by simp) (by simpa using hd) (fun z hz ↦ (hα.2 z hz).2.le)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hamgm
  have htrace : (trace α).re = ∑ z ∈ s, z.re := by
    rw [← Complex.re_sum]
    exact congrArg Complex.re s.sum_val
  rw [absoluteTrace, htrace, ← hcard]
  exact (Real.one_le_rpow hprod (by positivity)).trans hamgm

end MathlibExt.NumberTheory.SchurSiegelSmyth
