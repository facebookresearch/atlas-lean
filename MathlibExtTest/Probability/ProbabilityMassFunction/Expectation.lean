/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ProbabilityMassFunction.Expectation

/-!
# Tests for `PMF.expect` and `PMF.expectENN`

Concrete numeric checks of the expectation API on finite types.
-/

@[expose] public section

open scoped ENNReal

/-- The expected value of the identity function on `Fin 4` under the
uniform distribution is `(0 + 1 + 2 + 3) / 4 = 3 / 2`. -/
example : (PMF.uniformFintype (Fin 4)).expect (fun i => (i.val : ℝ)) = 3 / 2 := by
  rw [PMF.expect_uniformOfFintype]
  norm_num [Fin.sum_univ_four]

/-- A two-point check: half the mass on value `10` and half on `0`
gives expectation `5`. -/
example : (PMF.uniformFintype (Fin 2)).expect
    (fun i => if i = 0 then (10 : ℝ) else 0) = 5 := by
  rw [PMF.expect_uniformOfFintype]
  norm_num [Fin.sum_univ_two]

/-- Linearity over a two-term sum on `Fin 3`: the expectation of
`a ↦ (a + 0) + (a + 1)` is the sum of the two expectations, namely `3`. -/
example : (PMF.uniformFintype (Fin 3)).expect
    (fun a => ∑ i ∈ ({0, 1} : Finset ℕ), ((a.val : ℝ) + (i : ℝ))) = 3 := by
  rw [PMF.expect_sum]
  norm_num [PMF.expect_uniformOfFintype, Fin.sum_univ_three,
    Finset.sum_add_distrib]

/-- The indicator expectation of the even elements of `Fin 4` under the
uniform distribution is `2 / 4 = 1 / 2`. -/
example : (PMF.uniformFintype (Fin 4)).expect
    (fun i => if i.val % 2 = 0 then (1 : ℝ) else 0) = 1 / 2 := by
  rw [PMF.expect_indicator_decide]
  have hfilter : Finset.univ.filter (fun i : Fin 4 => i.val % 2 = 0) =
      {0, 2} := by decide
  rw [hfilter]
  norm_num [PMF.uniformFintype_apply, ENNReal.toReal_inv]

/-- The expectation of a constant under the Dirac (non-uniform)
distribution `PMF.pure 0` on `Fin 3` is that constant. -/
example : (PMF.pure (0 : Fin 3)).expect (fun _ => (4 : ℝ)) = 4 :=
  PMF.expect_const _ _

/-- The `ℝ≥0∞`-valued expected value of the identity function on `Fin 4`
under the uniform distribution is `(0 + 1 + 2 + 3) / 4 = 3 / 2`. -/
example : (PMF.uniformFintype (Fin 4)).expectENN
    (fun i => (i.val : ℝ≥0∞)) = 3 / 2 := by
  rw [PMF.expectENN_uniformOfFintype]
  norm_num [Fin.sum_univ_four]
  rw [show (4 : ℝ≥0∞) = ((4 : NNReal) : ℝ≥0∞) from
      (ENNReal.coe_ofNat 4).symm,
    show (6 : ℝ≥0∞) = ((6 : NNReal) : ℝ≥0∞) from
      (ENNReal.coe_ofNat 6).symm,
    show (3 : ℝ≥0∞) = ((3 : NNReal) : ℝ≥0∞) from
      (ENNReal.coe_ofNat 3).symm,
    show (2 : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞) from
      (ENNReal.coe_ofNat 2).symm,
    ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
    ← ENNReal.coe_mul,
    ← ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
    ENNReal.coe_inj]
  norm_num

/-- The `ℝ≥0∞`-valued expectation of a constant under `PMF.pure 0` on
`Fin 3` is that constant. -/
example : (PMF.pure (0 : Fin 3)).expectENN (fun _ => (4 : ℝ≥0∞)) = 4 :=
  PMF.expectENN_const _ _

/-- Bridge check on `Fin 3`: the `toReal` of the `ℝ≥0∞`-valued
expectation of `val` under the uniform distribution is `1`. -/
example : ((PMF.uniformFintype (Fin 3)).expectENN
    (fun i => (i.val : ℝ≥0∞))).toReal = 1 := by
  rw [PMF.expectENN_natCast_toReal, PMF.expect_uniformOfFintype]
  norm_num [Fin.sum_univ_three]

/-- Change of variables at an infinite source type: the uniform
distribution on `{0, 2} ⊆ ℕ` mapped by `· + 1` has expected value `2`.
The source type `ℕ` is not a `Fintype`; this exercises `expectENN_map`
beyond finite sample spaces. -/
example : ((PMF.uniformFinset ({0, 2} : Finset ℕ) (by simp)).map
    (· + 1)).expectENN (fun n : ℕ => (n : ℝ≥0∞)) = 2 := by
  rw [PMF.expectENN_map,
    PMF.expectENN_eq_sum_of_finite_support _ {0, 2}
      (fun a ha => by rw [PMF.uniformFinset_apply]; simp [ha])]
  norm_num [Finset.sum_insert, Finset.sum_singleton,
    PMF.uniformFinset_apply_of_mem, Function.comp_def]
  have hsum : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * 3 = (2 : ℝ≥0∞)⁻¹ * (1 + 3) := by
    rw [mul_add, mul_one]
  rw [hsum, show ((1 : ℝ≥0∞) + 3) = 4 by norm_num,
    show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

#print axioms PMF.expect_eq_sum
