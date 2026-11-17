/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.RectangularDFTAdapter

@[expose] public section

open MathlibExt.Analysis.Fourier.RectangularDFTAdapter

namespace MathlibExtTest.Analysis.Fourier.RectangularDFTAdapter

private lemma double_sum_impulse {m n : ℕ} [NeZero m] [NeZero n]
    (F : ZMod m → ZMod n → ℂ) (a : ZMod m) (b : ZMod n) :
    (∑ i : ZMod m, ∑ j : ZMod n, (if (i, j) = (a, b) then F i j else 0)) = F a b := by
  have houter : ∀ i : ZMod m, i ∈ Finset.univ → i ≠ a →
      (∑ j : ZMod n, (if (i, j) = (a, b) then F i j else 0)) = 0 := by
    intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    have hne : (i, j) ≠ (a, b) := by
      intro hcon
      simp only [Prod.mk.injEq] at hcon
      exact hi hcon.1
    simp [hne]
  have hinner : ∀ j : ZMod n, j ∈ Finset.univ → j ≠ b →
      (if (a, j) = (a, b) then F a j else 0) = 0 := by
    intro j _ hj
    have hne : (a, j) ≠ (a, b) := by
      intro hcon
      simp only [Prod.mk.injEq] at hcon
      exact hj hcon.2
    simp [hne]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a) houter,
    Finset.sum_eq_single_of_mem b (Finset.mem_univ b) hinner]
  simp

private lemma dft2Sum_impulse {m n : ℕ} [NeZero m] [NeZero n] (a : ZMod m) (b : ZMod n)
    (k : ZMod m) (l : ZMod n) :
    dft2Sum (fun p : ZMod m × ZMod n => if p = (a, b) then (1 : ℂ) else 0) (k, l) =
      Complex.exp (-2 * Real.pi * Complex.I *
        (((a.val * k.val : ℕ) : ℂ) / m + ((b.val * l.val : ℕ) : ℂ) / n)) := by
  simp only [dft2Sum, mul_ite, mul_one, mul_zero]
  exact double_sum_impulse _ _ _



/-- Validation: Validation (`2 × 3`): the impulse at the origin has the all-ones spectrum. -/
theorem rowColumnDFT_impulse_origin :
    rowColumnDFT (fun p : ZMod 2 × ZMod 3 => if p = (0, 0) then (1 : ℂ) else 0) =
      fun _ => 1 := by
  rw [rowColumnDFT_eq_dft2Sum]
  funext p
  obtain ⟨k, l⟩ := p
  rw [dft2Sum_impulse]
  simp


/-- Validation: Validation (`2 × 3`, shifted impulse): the impulse at `(1, 1)` has value
`exp (-πi) exp (-2πi/3) = -exp (-2πi/3)` at bin `(1, 1)`. -/
theorem rowColumnDFT_impulse_one_one :
    rowColumnDFT (fun p : ZMod 2 × ZMod 3 => if p = (1, 1) then (1 : ℂ) else 0) (1, 1) =
      -Complex.exp (-(2 * Real.pi * Complex.I / 3)) := by
  rw [rowColumnDFT_eq_dft2Sum, dft2Sum_impulse]
  have h1 : (1 : ZMod 2).val = 1 := by decide
  have h2 : (1 : ZMod 3).val = 1 := by decide
  rw [h1, h2]
  have harg : (-2 * Real.pi * Complex.I *
      ((((1 * 1 : ℕ)) : ℂ) / ((2 : ℕ) : ℂ) + ((((1 * 1 : ℕ)) : ℂ)) / ((3 : ℕ) : ℂ)) : ℂ) =
      (-(Real.pi * Complex.I)) + (-(2 * Real.pi * Complex.I / 3)) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_neg_pi_mul_I]
  ring


/-- Validation: Validation (`2 × 3`): the positive-exponent variant of the 2-D sum is not the
row-then-column canonical DFT. -/
theorem rowColumnDFT_ne_positiveExponentSum :
    ¬ ∀ x : ZMod 2 × ZMod 3 → ℂ, rowColumnDFT x = fun p => ∑ i : ZMod 2, ∑ j : ZMod 3,
      Complex.exp (2 * Real.pi * Complex.I *
        (((i.val * p.1.val : ℕ) : ℂ) / 2 + ((j.val * p.2.val : ℕ) : ℂ) / 3)) * x (i, j) := by
  intro hall
  have h1 : (1 : ZMod 3).val = 1 := by decide
  have h := congrFun (hall (fun p : ZMod 2 × ZMod 3 => if p = (0, 1) then (1 : ℂ) else 0)) (0, 1)
  rw [rowColumnDFT_eq_dft2Sum, dft2Sum_impulse] at h
  simp only [mul_ite, mul_one, mul_zero, double_sum_impulse, h1, ZMod.val_zero] at h
  have hBA : ((2 * Real.pi * Complex.I * ((((0 : ℕ)) : ℂ) / 2 + (((1 : ℕ)) : ℂ) / 3)) -
      (-2 * Real.pi * Complex.I * ((((0 : ℕ)) : ℂ) / (((2 : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ) / (((3 : ℕ)) : ℂ))) : ℂ) =
      2 * Real.pi * Complex.I * ((2 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) := by
    push_cast
    ring
  have hsub : Complex.exp ((2 * Real.pi * Complex.I * ((((0 : ℕ)) : ℂ) / 2 + (((1 : ℕ)) : ℂ) / 3)) -
      (-2 * Real.pi * Complex.I * ((((0 : ℕ)) : ℂ) / (((2 : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ) / (((3 : ℕ)) : ℂ)))) = 1 :=
    Complex.exp_eq_exp_iff_exp_sub_eq_one.mp h.symm
  rw [hBA] at hsub
  have hdiv := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 2) (N := 3) (by decide)).mp hsub
  norm_num at hdiv

private lemma invDft2Sum_impulse {m n : ℕ} [NeZero m] [NeZero n] (a : ZMod m) (b : ZMod n)
    (i : ZMod m) (j : ZMod n) :
    invDft2Sum (fun p : ZMod m × ZMod n => if p = (a, b) then (1 : ℂ) else 0) (i, j) =
      ((m : ℂ) * n)⁻¹ * Complex.exp (2 * Real.pi * Complex.I *
        (((a.val * i.val : ℕ) : ℂ) / m + ((b.val * j.val : ℕ) : ℂ) / n)) := by
  simp only [invDft2Sum, mul_ite, mul_one, mul_zero]
  congr 1
  exact double_sum_impulse _ _ _


/-- Validation: Validation (`2 × 3`): the inverse sum without the factor `1/(m*n)` is not the rectangular
inverse DFT. -/
theorem rectangularInvDFT_ne_unnormalizedSum :
    ¬ ∀ X : ZMod 2 × ZMod 3 → ℂ, rectangularInvDFT X = fun p => ∑ k : ZMod 2, ∑ l : ZMod 3,
      Complex.exp (2 * Real.pi * Complex.I *
        (((k.val * p.1.val : ℕ) : ℂ) / 2 + ((l.val * p.2.val : ℕ) : ℂ) / 3)) * X (k, l) := by
  intro hall
  have h := congrFun (hall (fun p : ZMod 2 × ZMod 3 => if p = (0, 0) then (1 : ℂ) else 0)) (0, 0)
  rw [rectangularInvDFT_eq_invDft2Sum, invDft2Sum_impulse] at h
  simp only [mul_ite, mul_one, mul_zero, double_sum_impulse] at h
  simp at h
  norm_num at h


end MathlibExtTest.Analysis.Fourier.RectangularDFTAdapter
