/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CharFunLattice

/-!
# Tests for the lattice characteristic-function characterization

Concrete instantiations for the Dirac mass at `2`: its characteristic
function is `1` at frequency `π`, so it is supported on `2 ℤ`; conversely,
its support on `2 ℤ` forces the characteristic function to be `1` at `π`.
Also, the Dirac mass at `2` is a lattice random variable in the sense of
`IsLatticeRV`, and `#print axioms` checks that the main theorem depends
only on the standard axioms.
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Probability.CharFunLattice

namespace MathlibExtTest.Probability.CharFunLattice

/-- `(1 : ℂ) ≠ -1`, by taking real parts. -/
private lemma one_ne_neg_one_complex : (1 : ℂ) ≠ -1 := by
  intro hcon
  have h := congrArg Complex.re hcon
  simp only [Complex.one_re, Complex.neg_re] at h
  norm_num at h

/-- `2 * π / π = 2`. -/
private lemma two_mul_pi_div_pi : 2 * Real.pi / Real.pi = 2 :=
  mul_div_cancel_right₀ 2 Real.pi_ne_zero

/-- The characteristic function of the Dirac mass at `2` at frequency `π`
is `1`, computed directly: `exp (π * 2 * i) = exp (2π i) = 1`. -/
private lemma charFun_dirac_two_pi :
    charFun (Measure.dirac (2 : ℝ)) Real.pi = 1 := by
  rw [charFun_apply_real, integral_dirac]
  have h : (Real.pi : ℂ) * ((2 : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_two_pi_mul_I]

/-- The characteristic function of the Dirac mass at `2` at frequency `π / 2`
is `-1`, since `exp (π i / 2 * 2) = exp (π i) = -1`. -/
private lemma charFun_dirac_two_pi_div_two :
    charFun (Measure.dirac (2 : ℝ)) (Real.pi / 2) = -1 := by
  rw [charFun_apply_real, integral_dirac]
  have h : ((Real.pi / 2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) * Complex.I
      = Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_pi_mul_I]

/-- Forward direction, concretely: the Dirac mass at `2` is supported on
`2 ℤ`. -/
example : (Measure.dirac (2 : ℝ)) {x : ℝ | ∃ k : ℤ, x = 2 * k} = 1 := by
  have h := (charFun_eq_one_iff_measure_eq_one_of_lattice (μ := Measure.dirac (2 : ℝ))
    (l := Real.pi) (by norm_num)).mp charFun_dirac_two_pi
  rwa [two_mul_pi_div_pi] at h

/-- Converse direction, concretely: the Dirac mass at `2` is supported on
`2 ℤ` (it sits at `2 ∈ 2 ℤ`), so its characteristic function at `π` is `1`.
The support fact is proved directly from Dirac membership, not via the
forward direction. -/
example : charFun (Measure.dirac (2 : ℝ)) Real.pi = 1 := by
  have hsupp : (Measure.dirac (2 : ℝ))
      {x : ℝ | ∃ k : ℤ, x = (2 * Real.pi / Real.pi) * k} = 1 := by
    rw [two_mul_pi_div_pi]
    exact Measure.dirac_apply_of_mem ⟨1, by norm_num⟩
  exact (charFun_eq_one_iff_measure_eq_one_of_lattice (μ := Measure.dirac (2 : ℝ))
    (l := Real.pi) (by norm_num)).mpr hsupp

/-- The Dirac mass at `2` is a lattice random variable: its characteristic
function is `1` at `π` but not identically `1` (it is `-1` at `π / 2`). -/
example : IsLatticeRV (Measure.dirac (2 : ℝ)) := by
  refine ⟨⟨Real.pi, by norm_num, charFun_dirac_two_pi⟩, ?_⟩
  intro hall
  have h1 := hall (Real.pi / 2)
  rw [charFun_dirac_two_pi_div_two] at h1
  exact one_ne_neg_one_complex h1.symm

/-- A lattice random variable is supported on some lattice: for the Dirac
mass at `2`, the witness step is `2`. -/
example : ∃ hstep : ℝ, hstep ≠ 0 ∧
    (Measure.dirac (2 : ℝ)) {x : ℝ | ∃ k : ℤ, x = hstep * k} = 1 := by
  have hRV : IsLatticeRV (Measure.dirac (2 : ℝ)) := by
    refine ⟨⟨Real.pi, by norm_num, charFun_dirac_two_pi⟩, ?_⟩
    intro hall
    have h1 := hall (Real.pi / 2)
    rw [charFun_dirac_two_pi_div_two] at h1
    exact one_ne_neg_one_complex h1.symm
  exact hRV.exists_lattice_support

#print axioms charFun_eq_one_iff_measure_eq_one_of_lattice
#print axioms IsLatticeRV.exists_lattice_support

end MathlibExtTest.Probability.CharFunLattice
