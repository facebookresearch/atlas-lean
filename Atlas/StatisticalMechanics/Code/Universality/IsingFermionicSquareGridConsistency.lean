/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Calculus.Taylor









namespace StatMech.Universality

open Set

noncomputable section

def cubicTaylorPolynomial (g : Real → Real) (s : Real) : Real :=
  g 0 + iteratedDeriv 1 g 0 * s +
    iteratedDeriv 2 g 0 * s ^ 2 / 2 +
      iteratedDeriv 3 g 0 * s ^ 3 / 6

theorem taylorWithinEval_three_eq_cubic
    (g : Real → Real) (s : Real) (hs : s ≠ 0)
    (hg : ContDiff Real 4 g) :
    taylorWithinEval g 3 (uIcc 0 s) 0 s = cubicTaylorPolynomial g s := by
  have hu : UniqueDiffOn Real (uIcc 0 s) :=
    uniqueDiffOn_Icc (by grind [uIcc])
  have hzero : (0 : Real) ∈ uIcc 0 s := left_mem_uIcc
  have hiter (j : Nat) (hj : j ≤ 4) :
      iteratedDerivWithin j g (uIcc 0 s) 0 = iteratedDeriv j g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hg.contDiffAt.of_le (by exact_mod_cast hj)) hzero
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hiter, cubicTaylorPolynomial]
  ring

theorem cubicTaylor_remainder_le_of_fourthDeriv_bound
    (g : Real → Real) (s M : Real) (hs : s ≠ 0)
    (hg : ContDiff Real 4 g)
    (hM : ∀ t ∈ uIcc 0 s, |iteratedDeriv 4 g t| ≤ M) :
    |g s - cubicTaylorPolynomial g s| ≤ M * |s| ^ 4 / 24 := by
  obtain ⟨t, ht, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (x := s) (x₀ := 0) hs.symm
      (hg.contDiffOn.mono (by rintro x -; exact mem_univ x))
      (n := 3)
  rw [← taylorWithinEval_three_eq_cubic g s hs hg, hrem]
  rw [abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (hM t (Ioo_subset_Icc_self ht)) (pow_nonneg (abs_nonneg s) 4))
    (by norm_num)



theorem centralSecondDifference_remainder_le
    (g : Real → Real) (h M : Real)
    (hg : ContDiff Real 4 g)
    (hfourth : ∀ t, |iteratedDeriv 4 g t| ≤ M) :
    |(g h + g (-h) - 2 * g 0) - iteratedDeriv 2 g 0 * h ^ 2| ≤
      M * |h| ^ 4 / 12 := by
  by_cases hh : h = 0
  · simp [hh]
    ring
  have hpos := cubicTaylor_remainder_le_of_fourthDeriv_bound
    g h M hh hg (fun t _ ↦ hfourth t)
  have hneg := cubicTaylor_remainder_le_of_fourthDeriv_bound
    g (-h) M (neg_ne_zero.mpr hh) hg (fun t _ ↦ hfourth t)
  have hid :
      (g h + g (-h) - 2 * g 0) - iteratedDeriv 2 g 0 * h ^ 2 =
        (g h - cubicTaylorPolynomial g h) +
          (g (-h) - cubicTaylorPolynomial g (-h)) := by
    unfold cubicTaylorPolynomial
    ring
  rw [hid]
  calc
    |(g h - cubicTaylorPolynomial g h) +
        (g (-h) - cubicTaylorPolynomial g (-h))| ≤
      |g h - cubicTaylorPolynomial g h| +
        |g (-h) - cubicTaylorPolynomial g (-h)| := abs_add_le _ _
    _ ≤ M * |h| ^ 4 / 24 + M * |-h| ^ 4 / 24 :=
      add_le_add hpos hneg
    _ = M * |h| ^ 4 / 12 := by rw [abs_neg]; ring

def directionalFourNeighborStencil
    (g₁ g₂ : Real → Real) (h : Real) : Real :=
  (g₁ h + g₁ (-h) - 2 * g₁ 0) +
    (g₂ h + g₂ (-h) - 2 * g₂ 0)



theorem harmonicDirectionalFourNeighborStencil_le
    (g₁ g₂ : Real → Real) (h M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4 g₁) (hg₂ : ContDiff Real 4 g₂)
    (hfourth₁ : ∀ t, |iteratedDeriv 4 g₁ t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4 g₂ t| ≤ M₂)
    (hharmonic : iteratedDeriv 2 g₁ 0 + iteratedDeriv 2 g₂ 0 = 0) :
    |directionalFourNeighborStencil g₁ g₂ h| ≤
      (M₁ + M₂) * |h| ^ 4 / 12 := by
  have h₁ := centralSecondDifference_remainder_le
    g₁ h M₁ hg₁ hfourth₁
  have h₂ := centralSecondDifference_remainder_le
    g₂ h M₂ hg₂ hfourth₂
  have hid : directionalFourNeighborStencil g₁ g₂ h =
      ((g₁ h + g₁ (-h) - 2 * g₁ 0) -
        iteratedDeriv 2 g₁ 0 * h ^ 2) +
      ((g₂ h + g₂ (-h) - 2 * g₂ 0) -
        iteratedDeriv 2 g₂ 0 * h ^ 2) := by
    unfold directionalFourNeighborStencil
    nlinarith
  rw [hid]
  calc
    |_ + _| ≤
        |(g₁ h + g₁ (-h) - 2 * g₁ 0) -
          iteratedDeriv 2 g₁ 0 * h ^ 2| +
        |(g₂ h + g₂ (-h) - 2 * g₂ 0) -
          iteratedDeriv 2 g₂ 0 * h ^ 2| := abs_add_le _ _
    _ ≤ M₁ * |h| ^ 4 / 12 + M₂ * |h| ^ 4 / 12 := add_le_add h₁ h₂
    _ = (M₁ + M₂) * |h| ^ 4 / 12 := by ring

def complexAxialFourNeighborStencil
    (f : Complex → Real) (z : Complex) (h : Real) : Real :=
  f (z + (h : Complex)) + f (z - (h : Complex)) +
    f (z + (h : Complex) * Complex.I) +
      f (z - (h : Complex) * Complex.I) - 4 * f z




theorem complexAxialFourNeighborStencil_le
    (f : Complex → Real) (z : Complex) (h M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4 (fun t : Real ↦ f (z + (t : Complex))))
    (hg₂ : ContDiff Real 4
      (fun t : Real ↦ f (z + (t : Complex) * Complex.I)))
    (hfourth₁ : ∀ t, |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex))) t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * Complex.I)) t| ≤ M₂)
    (hharmonic : iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex))) 0 +
      iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * Complex.I)) 0 = 0) :
    |complexAxialFourNeighborStencil f z h| ≤
      (M₁ + M₂) * |h| ^ 4 / 12 := by
  rw [show complexAxialFourNeighborStencil f z h =
      directionalFourNeighborStencil
        (fun t : Real ↦ f (z + (t : Complex)))
        (fun t : Real ↦ f (z + (t : Complex) * Complex.I)) h by
    unfold complexAxialFourNeighborStencil directionalFourNeighborStencil
    push_cast
    simp only [add_zero, zero_mul, sub_eq_add_neg]
    ring]
  exact harmonicDirectionalFourNeighborStencil_le
    (fun t : Real ↦ f (z + (t : Complex)))
    (fun t : Real ↦ f (z + (t : Complex) * Complex.I))
    h M₁ M₂ hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

def complexDirectionalFourNeighborStencil
    (f : Complex → Real) (z v₁ v₂ : Complex) (h : Real) : Real :=
  f (z + (h : Complex) * v₁) + f (z - (h : Complex) * v₁) +
    f (z + (h : Complex) * v₂) + f (z - (h : Complex) * v₂) - 4 * f z


theorem complexDirectionalFourNeighborStencil_le
    (f : Complex → Real) (z v₁ v₂ : Complex) (h M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4
      (fun t : Real ↦ f (z + (t : Complex) * v₁)))
    (hg₂ : ContDiff Real 4
      (fun t : Real ↦ f (z + (t : Complex) * v₂)))
    (hfourth₁ : ∀ t, |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * v₁)) t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * v₂)) t| ≤ M₂)
    (hharmonic : iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * v₁)) 0 +
      iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * v₂)) 0 = 0) :
    |complexDirectionalFourNeighborStencil f z v₁ v₂ h| ≤
      (M₁ + M₂) * |h| ^ 4 / 12 := by
  rw [show complexDirectionalFourNeighborStencil f z v₁ v₂ h =
      directionalFourNeighborStencil
        (fun t : Real ↦ f (z + (t : Complex) * v₁))
        (fun t : Real ↦ f (z + (t : Complex) * v₂)) h by
    unfold complexDirectionalFourNeighborStencil
      directionalFourNeighborStencil
    push_cast
    simp only [add_zero, zero_mul, sub_eq_add_neg]
    ring]
  exact harmonicDirectionalFourNeighborStencil_le
    (fun t : Real ↦ f (z + (t : Complex) * v₁))
    (fun t : Real ↦ f (z + (t : Complex) * v₂))
    h M₁ M₂ hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

end

end StatMech.Universality
