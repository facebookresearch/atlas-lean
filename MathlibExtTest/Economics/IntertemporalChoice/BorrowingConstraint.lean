/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.IntertemporalChoice.BorrowingConstraint
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

namespace MathlibExtTest.Economics.IntertemporalChoice.BorrowingConstraint

-- Test section with `u c = 8 * c - c ^ 2`, `β = 1`, `r = 0`, `y₀ = 0`, `y₁ = 4`.

theorem hasDerivAt_quad (x : ℝ) :
    HasDerivAt (fun c : ℝ => 8 * c - c ^ 2) (8 - 2 * x) x := by
  have hid : HasDerivAt id (1 : ℝ) x := hasDerivAt_id x
  have hmul : HasDerivAt (fun c : ℝ => 8 * id c) (8 * 1) x := hid.const_mul 8
  have hpow : HasDerivAt (fun c : ℝ => c ^ 2) ((2 : ℝ) * x ^ (2 - 1)) x :=
    hasDerivAt_pow 2 x
  have hsub : HasDerivAt (fun c : ℝ => 8 * id c - c ^ 2) (8 * 1 - 2 * x ^ (2 - 1)) x :=
    hmul.sub hpow
  have hfun : (fun c : ℝ => 8 * id c - c ^ 2) = (fun c : ℝ => 8 * c - c ^ 2) := by
    ext c
    simp
  have hder : (8 : ℝ) * 1 - 2 * x ^ (2 - 1) = 8 - 2 * x := by
    norm_num
  rw [hfun, hder] at hsub
  exact hsub

theorem deriv_quad_one : deriv (fun c : ℝ => 8 * c - c ^ 2) 1 = 6 := by
  have h := (hasDerivAt_quad 1).deriv
  norm_num at h
  exact h

theorem deriv_quad_three : deriv (fun c : ℝ => 8 * c - c ^ 2) 3 = 2 := by
  have h := (hasDerivAt_quad 3).deriv
  norm_num at h
  exact h

theorem deriv_quad_two : deriv (fun c : ℝ => 8 * c - c ^ 2) 2 = 4 := by
  have h := (hasDerivAt_quad 2).deriv
  norm_num at h
  exact h

theorem differentiableAt_quad (x : ℝ) :
    DifferentiableAt ℝ (fun c : ℝ => 8 * c - c ^ 2) x :=
  (hasDerivAt_quad x).differentiableAt

theorem binding_isMaxOn : IsMaxOn
    (MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget
      (fun c : ℝ => 8 * c - c ^ 2) 1 0 0 4)
    (MathlibExt.Economics.BorrowingConstraint.borrowingFeasible 0 0 4 1) 1 := by
  rw [isMaxOn_iff]
  intro x hx
  obtain ⟨_, _, hxle⟩ := hx
  have hdiff : MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget
        (fun c : ℝ => 8 * c - c ^ 2) 1 0 0 4 1 -
        MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget
        (fun c : ℝ => 8 * c - c ^ 2) 1 0 0 4 x
      = 2 * (1 - x) * (3 - x) := by
    simp only [MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget,
      MathlibExt.Economics.BorrowingConstraint.nextConsumption]
    ring
  have h1 : (0 : ℝ) ≤ 1 - x := by linarith
  have h3 : (0 : ℝ) ≤ 3 - x := by linarith
  have hnonneg : (0 : ℝ) ≤ 2 * (1 - x) * (3 - x) :=
    mul_nonneg (mul_nonneg (by norm_num) h1) h3
  linarith

theorem binding_mem : (1 : ℝ) ∈
    MathlibExt.Economics.BorrowingConstraint.borrowingFeasible 0 0 4 1 :=
  ⟨by norm_num, by norm_num
    [MathlibExt.Economics.BorrowingConstraint.nextConsumption], by norm_num⟩

theorem slack_isMaxOn : IsMaxOn
    (MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget
      (fun c : ℝ => 8 * c - c ^ 2) 1 0 0 4)
    (MathlibExt.Economics.BorrowingConstraint.borrowingFeasible 0 0 4 3) 2 := by
  rw [isMaxOn_iff]
  intro x _
  have hdiff : MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget
        (fun c : ℝ => 8 * c - c ^ 2) 1 0 0 4 2 -
        MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget
        (fun c : ℝ => 8 * c - c ^ 2) 1 0 0 4 x
      = 2 * (x - 2) ^ 2 := by
    simp only [MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget,
      MathlibExt.Economics.BorrowingConstraint.nextConsumption]
    ring
  have hnonneg : (0 : ℝ) ≤ 2 * (x - 2) ^ 2 := by positivity
  linarith


-- Required concrete examples.
example : IsMaxOn
    (MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget
      (fun c : ℝ => 8 * c - c ^ 2) 1 0 0 4)
    (MathlibExt.Economics.BorrowingConstraint.borrowingFeasible 0 0 4 1) 1 :=
  binding_isMaxOn

example : (1 : ℝ) ∈
    MathlibExt.Economics.BorrowingConstraint.borrowingFeasible 0 0 4 1 :=
  binding_mem

example : ∃ μ : ℝ, μ = 4 ∧ 0 ≤ μ ∧ μ * (1 - (0 + 1)) = 0 ∧
    deriv (fun c : ℝ => 8 * c - c ^ 2) 1
      = 1 * (1 + 0) * deriv (fun c : ℝ => 8 * c - c ^ 2) 3 + μ := by
  have hmax := binding_isMaxOn
  have hmem := binding_mem
  have hc₀ : (0 : ℝ) < 1 := by norm_num
  have hc₁ : (0 : ℝ)
      < MathlibExt.Economics.BorrowingConstraint.nextConsumption 0 0 4 1 := by
    norm_num [MathlibExt.Economics.BorrowingConstraint.nextConsumption]
  have hc1_eq : MathlibExt.Economics.BorrowingConstraint.nextConsumption 0 0 4 1 = 3 := by
    norm_num [MathlibExt.Economics.BorrowingConstraint.nextConsumption]
  have hu₀ := differentiableAt_quad 1
  have hu₁ : DifferentiableAt ℝ (fun c : ℝ => 8 * c - c ^ 2)
      (MathlibExt.Economics.BorrowingConstraint.nextConsumption 0 0 4 1) := by
    rw [hc1_eq]
    exact differentiableAt_quad 3
  obtain ⟨μ, hμ_nonneg, hcomp, heq⟩ :=
    MathlibExt.Economics.BorrowingConstraint.euler_complementary_slackness
      hmax hmem hc₀ hc₁ hu₀ hu₁
  rw [hc1_eq] at heq
  have h1 : deriv (fun c : ℝ => 8 * c - c ^ 2) 1 = 6 :=
    deriv_quad_one
  have h3 : deriv (fun c : ℝ => 8 * c - c ^ 2) 3 = 2 :=
    deriv_quad_three
  have heq' := heq
  rw [h1, h3] at heq'
  have hμ4 : μ = 4 := by linarith
  exact ⟨μ, hμ4, hμ_nonneg, hcomp, heq⟩

example : 1 * (1 + 0) * deriv (fun c : ℝ => 8 * c - c ^ 2) 3
    < deriv (fun c : ℝ => 8 * c - c ^ 2) 1 := by
  rw [deriv_quad_one,
    deriv_quad_three]
  norm_num

example : IsMaxOn
    (MathlibExt.Economics.BorrowingConstraint.utilityAlongBudget
      (fun c : ℝ => 8 * c - c ^ 2) 1 0 0 4)
    (MathlibExt.Economics.BorrowingConstraint.borrowingFeasible 0 0 4 3) 2 :=
  slack_isMaxOn

example : deriv (fun c : ℝ => 8 * c - c ^ 2) 2 = 1 * (1 + 0) *
    deriv (fun c : ℝ => 8 * c - c ^ 2)
      (MathlibExt.Economics.BorrowingConstraint.nextConsumption 0 0 4 2) := by
  have hmax := slack_isMaxOn
  have hc₀ : (0 : ℝ) < 2 := by norm_num
  have hc₁ : (0 : ℝ)
      < MathlibExt.Economics.BorrowingConstraint.nextConsumption 0 0 4 2 := by
    norm_num [MathlibExt.Economics.BorrowingConstraint.nextConsumption]
  have hslack : (2 : ℝ) < 0 + 3 := by norm_num
  have hu₀ := differentiableAt_quad 2
  have hc1_eq : MathlibExt.Economics.BorrowingConstraint.nextConsumption 0 0 4 2 = 2 := by
    norm_num [MathlibExt.Economics.BorrowingConstraint.nextConsumption]
  have hu₁ : DifferentiableAt ℝ (fun c : ℝ => 8 * c - c ^ 2)
      (MathlibExt.Economics.BorrowingConstraint.nextConsumption 0 0 4 2) := by
    rw [hc1_eq]
    exact differentiableAt_quad 2
  exact MathlibExt.Economics.BorrowingConstraint.euler_equation_of_slack
    hmax hc₀ hc₁ hslack hu₀ hu₁

example : MathlibExt.Economics.BorrowingConstraint.nextConsumption 0 0 4 2 = 2 := by
  norm_num [MathlibExt.Economics.BorrowingConstraint.nextConsumption]

end MathlibExtTest.Economics.IntertemporalChoice.BorrowingConstraint
