/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Restricted Boltzmann machine conditionals

A binary restricted Boltzmann machine has visible biases `a`, hidden biases
`b`, and cross-layer weights `W`, with score given by minus the energy
`E(v,h) = -aᵀv - bᵀh - vᵀWh`. Because the score has no hidden-hidden or
visible-visible couplings, each conditional Gibbs mass factorizes over the
conditioned layer into coordinate sigmoid factors.

The formalization uses `Bool` coordinates mapped to `{0, 1}` by `bit`, and it
defines `score` as `-E(v,h)`. Hidden coordinate `j` therefore has logit
`b j + ∑ i, bit (v i) * W i j`, and visible coordinate `i` has logit
`a i + ∑ j, W i j * bit (h j)`.

## References

* Geoffrey E. Hinton, "A Practical Guide to Training Restricted Boltzmann
  Machines" (2012), section 2, for the `{0, 1}` binary-unit convention, the
  energy `E(v,h) = -∑ᵢ aᵢvᵢ - ∑ⱼ bⱼhⱼ - ∑ᵢⱼ vᵢWᵢⱼhⱼ`, and the conditional
  probabilities `σ(bⱼ + ∑ᵢ vᵢWᵢⱼ)` and `σ(aᵢ + ∑ⱼ Wᵢⱼhⱼ)`. This file adapts
  those formulas to finite `Bool` vectors and states the conditionals as
  exponentiated-score ratios.

## Main declarations

* `score`: minus the RBM energy.
* `hiddenLogit`, `visibleLogit`: one-coordinate conditional logits.
* `condHidden`, `condVisible`: conditional Gibbs masses as score ratios.
* `condHidden_eq_prod_sigmoid`, `condVisible_eq_prod_sigmoid`: factorization.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.RBM

/-- The real indicator value of a binary coordinate. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The RBM score, namely minus the energy
`E(v,h) = -aᵀv - bᵀh - vᵀWh`. -/
noncomputable def score {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) : ℝ :=
  (∑ i, a i * bit (v i)) + (∑ j, b j * bit (h j)) +
    ∑ i, ∑ j, bit (v i) * W i j * bit (h j)

/-- The logit for hidden coordinate `j` given visible vector `v`. -/
noncomputable def hiddenLogit {m k : ℕ} (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (j : Fin k) : ℝ :=
  b j + ∑ i, bit (v i) * W i j

/-- The logit for visible coordinate `i` given hidden vector `h`. -/
noncomputable def visibleLogit {m k : ℕ} (a : Fin m → ℝ)
    (W : Fin m → Fin k → ℝ) (h : Fin k → Bool) (i : Fin m) : ℝ :=
  a i + ∑ j, W i j * bit (h j)

/-- The conditional Gibbs mass of hidden vector `h` given visible vector `v`,
as a real ratio of exponentiated scores. -/
noncomputable def condHidden {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) : ℝ :=
  Real.exp (score a b W v h) / (∑ h', Real.exp (score a b W v h'))

/-- The conditional Gibbs mass of visible vector `v` given hidden vector `h`,
as a real ratio of exponentiated scores. -/
noncomputable def condVisible {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) : ℝ :=
  Real.exp (score a b W v h) / (∑ v', Real.exp (score a b W v' h))

private theorem bit_true : bit true = 1 := by simp [bit]

private theorem bit_false : bit false = 0 := by simp [bit]

private theorem sigmoid_eq_exp_div (L : ℝ) :
    Real.sigmoid L = Real.exp L / (1 + Real.exp L) := by
  rw [Real.sigmoid_def, Real.exp_neg]
  field_simp
  ring

private theorem one_sub_sigmoid (L : ℝ) :
    1 - Real.sigmoid L = 1 / (1 + Real.exp L) := by
  rw [Real.sigmoid_def, Real.exp_neg]
  field_simp
  ring

private theorem score_hidden_split {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) :
    score a b W v h =
      (∑ i, a i * bit (v i)) + ∑ j, bit (h j) * hiddenLogit b W v j := by
  unfold score hiddenLogit
  rw [add_assoc]
  congr 1
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

private theorem exp_score_hidden {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) :
    Real.exp (score a b W v h) =
      Real.exp (∑ i, a i * bit (v i)) *
        ∏ j, Real.exp (bit (h j) * hiddenLogit b W v j) := by
  rw [score_hidden_split, Real.exp_add]
  congr 1
  exact Real.exp_sum _ _

private theorem hidden_denom_coord {m k : ℕ} (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (j : Fin k) :
    (∑ bval : Bool, Real.exp (bit bval * hiddenLogit b W v j))
      = 1 + Real.exp (hiddenLogit b W v j) := by
  rw [Fintype.sum_bool]
  simp [bit_true, bit_false, one_mul, zero_mul, Real.exp_zero, add_comm]

private theorem hidden_coord_true {m k : ℕ} (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (j : Fin k) :
    Real.exp (bit true * hiddenLogit b W v j) /
        (∑ bval : Bool, Real.exp (bit bval * hiddenLogit b W v j))
      = Real.sigmoid (hiddenLogit b W v j) := by
  rw [hidden_denom_coord]
  simp only [bit_true, one_mul]
  rw [sigmoid_eq_exp_div]

private theorem hidden_coord_false {m k : ℕ} (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (j : Fin k) :
    Real.exp (bit false * hiddenLogit b W v j) /
        (∑ bval : Bool, Real.exp (bit bval * hiddenLogit b W v j))
      = 1 - Real.sigmoid (hiddenLogit b W v j) := by
  rw [hidden_denom_coord]
  simp only [bit_false, zero_mul, Real.exp_zero]
  rw [one_sub_sigmoid, one_div]

private theorem score_visible_split {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) :
    score a b W v h =
      (∑ j, b j * bit (h j)) + ∑ i, bit (v i) * visibleLogit a W h i := by
  unfold score visibleLogit
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hA : (∑ i, a i * bit (v i)) = ∑ i, bit (v i) * a i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hC : (∑ i, ∑ j, bit (v i) * W i j * bit (h j))
      = ∑ i, bit (v i) * ∑ j, W i j * bit (h j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hA, hC]
  ac_rfl

private theorem exp_score_visible {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) :
    Real.exp (score a b W v h) =
      Real.exp (∑ j, b j * bit (h j)) *
        ∏ i, Real.exp (bit (v i) * visibleLogit a W h i) := by
  rw [score_visible_split, Real.exp_add]
  congr 1
  exact Real.exp_sum _ _

private theorem visible_denom_coord {m k : ℕ} (a : Fin m → ℝ)
    (W : Fin m → Fin k → ℝ) (h : Fin k → Bool) (i : Fin m) :
    (∑ aval : Bool, Real.exp (bit aval * visibleLogit a W h i))
      = 1 + Real.exp (visibleLogit a W h i) := by
  rw [Fintype.sum_bool]
  simp [bit_true, bit_false, one_mul, zero_mul, Real.exp_zero, add_comm]

private theorem visible_coord_true {m k : ℕ} (a : Fin m → ℝ)
    (W : Fin m → Fin k → ℝ) (h : Fin k → Bool) (i : Fin m) :
    Real.exp (bit true * visibleLogit a W h i) /
        (∑ aval : Bool, Real.exp (bit aval * visibleLogit a W h i))
      = Real.sigmoid (visibleLogit a W h i) := by
  rw [visible_denom_coord]
  simp only [bit_true, one_mul]
  rw [sigmoid_eq_exp_div]

private theorem visible_coord_false {m k : ℕ} (a : Fin m → ℝ)
    (W : Fin m → Fin k → ℝ) (h : Fin k → Bool) (i : Fin m) :
    Real.exp (bit false * visibleLogit a W h i) /
        (∑ aval : Bool, Real.exp (bit aval * visibleLogit a W h i))
      = 1 - Real.sigmoid (visibleLogit a W h i) := by
  rw [visible_denom_coord]
  simp only [bit_false, zero_mul, Real.exp_zero]
  rw [one_sub_sigmoid, one_div]

/-- In a binary RBM with no hidden-hidden couplings, the hidden conditional
factorizes into coordinate sigmoids. -/
theorem condHidden_eq_prod_sigmoid {m k : ℕ} (a : Fin m → ℝ)
    (b : Fin k → ℝ) (W : Fin m → Fin k → ℝ) (v : Fin m → Bool)
    (h : Fin k → Bool) :
    condHidden a b W v h =
      ∏ j, if h j then Real.sigmoid (hiddenLogit b W v j)
        else 1 - Real.sigmoid (hiddenLogit b W v j) := by
  unfold condHidden
  have hnum : Real.exp (score a b W v h) =
      Real.exp (∑ i, a i * bit (v i)) *
        ∏ j, Real.exp (bit (h j) * hiddenLogit b W v j) :=
    exp_score_hidden a b W v h
  have hden : (∑ h', Real.exp (score a b W v h')) =
      Real.exp (∑ i, a i * bit (v i)) *
        ∏ j, ∑ bval : Bool, Real.exp (bit bval * hiddenLogit b W v j) := by
    have h1 : ∀ h' : Fin k → Bool, Real.exp (score a b W v h') =
        Real.exp (∑ i, a i * bit (v i)) *
          ∏ j, Real.exp (bit (h' j) * hiddenLogit b W v j) :=
      fun h' => exp_score_hidden a b W v h'
    simp_rw [h1]
    rw [← Finset.mul_sum]
    congr 1
    exact (Fintype.prod_sum (fun j bval => Real.exp (bit bval * hiddenLogit b W v j))).symm
  rw [hnum, hden]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _)]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : h j = true
  · rw [ite_eq_left hj, hj]
    exact hidden_coord_true b W v j
  · have hjf : h j = false := by
      cases hb : h j
      · rfl
      · simp [hb] at hj
    rw [ite_eq_right hj, hjf]
    exact hidden_coord_false b W v j

/-- In a binary RBM with no visible-visible couplings, the visible conditional
factorizes into coordinate sigmoids. -/
theorem condVisible_eq_prod_sigmoid {m k : ℕ} (a : Fin m → ℝ)
    (b : Fin k → ℝ) (W : Fin m → Fin k → ℝ) (v : Fin m → Bool)
    (h : Fin k → Bool) :
    condVisible a b W v h =
      ∏ i, if v i then Real.sigmoid (visibleLogit a W h i)
        else 1 - Real.sigmoid (visibleLogit a W h i) := by
  unfold condVisible
  have hnum : Real.exp (score a b W v h) =
      Real.exp (∑ j, b j * bit (h j)) *
        ∏ i, Real.exp (bit (v i) * visibleLogit a W h i) :=
    exp_score_visible a b W v h
  have hden : (∑ v', Real.exp (score a b W v' h)) =
      Real.exp (∑ j, b j * bit (h j)) *
        ∏ i, ∑ aval : Bool, Real.exp (bit aval * visibleLogit a W h i) := by
    have h1 : ∀ v' : Fin m → Bool, Real.exp (score a b W v' h) =
        Real.exp (∑ j, b j * bit (h j)) *
          ∏ i, Real.exp (bit (v' i) * visibleLogit a W h i) :=
      fun v' => exp_score_visible a b W v' h
    simp_rw [h1]
    rw [← Finset.mul_sum]
    congr 1
    exact (Fintype.prod_sum (fun i aval => Real.exp (bit aval * visibleLogit a W h i))).symm
  rw [hnum, hden]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _)]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : v i = true
  · rw [ite_eq_left hi, hi]
    exact visible_coord_true a W h i
  · have hif : v i = false := by
      cases hb : v i
      · rfl
      · simp [hb] at hi
    rw [ite_eq_right hi, hif]
    exact visible_coord_false a W h i

end Cslib.MachineLearning.RBM
