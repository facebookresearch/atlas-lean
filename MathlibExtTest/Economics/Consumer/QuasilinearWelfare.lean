/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.QuasilinearWelfare
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open Filter Topology Set

/-! Quadratic utility `φ z = z - z² / 2` on `ℝ`: demand `x p = 1 - p` and expenditure
`e p = ubar - (1 - p)² / 2`. For the price move from `1` to `0` the welfare change and the surplus
change both equal `1 / 2`, for every reference utility `ubar`. -/

namespace MathlibExtTest.Economics.Consumer.QuasilinearWelfare

open _root_.Economics.Consumer

lemma quad_surplus_le (q z : ℝ) : (z - z ^ 2 / 2) - q * z ≤ (1 - q) ^ 2 / 2 := by
  nlinarith [sq_nonneg ((1 : ℝ) - q - z)]

theorem welfare_eq_surplus (ubar : ℝ) :
    (ubar - (1 - (1 : ℝ)) ^ 2 / 2) - (ubar - (1 - (0 : ℝ)) ^ 2 / 2)
      = ∫ p in (0 : ℝ)..1, (1 - p) := by
  have he : ∀ p ∈ uIcc (1 : ℝ) (0 : ℝ), ∀ᶠ q in 𝓝 p,
      IsGLB ((fun b : ℝ × ℝ => q * b.1 + b.2) ''
        {b | b.1 ∈ Set.univ ∧ ubar ≤ (b.1 - b.1 ^ 2 / 2) + b.2})
        (ubar - (1 - q) ^ 2 / 2) := by
    intro p _
    apply Filter.Eventually.of_forall
    intro q
    apply IsLeast.isGLB
    constructor
    · refine ⟨(1 - q, ubar - ((1 - q) - (1 - q) ^ 2 / 2)), ⟨Set.mem_univ _, ?_⟩, ?_⟩
      · show ubar ≤ ((1 - q) - (1 - q) ^ 2 / 2) + (ubar - ((1 - q) - (1 - q) ^ 2 / 2))
        linarith
      · show q * (1 - q) + (ubar - ((1 - q) - (1 - q) ^ 2 / 2)) = ubar - (1 - q) ^ 2 / 2
        ring
    · intro c hc
      obtain ⟨b, hb, hcb⟩ := hc
      obtain ⟨hbZ, hbub⟩ := hb
      subst hcb
      show ubar - (1 - q) ^ 2 / 2 ≤ q * b.1 + b.2
      have h := quad_surplus_le q b.1
      linarith
  have hx : ∀ p ∈ uIcc (1 : ℝ) (0 : ℝ), (1 - p) ∈ Set.univ ∧
      ∀ z ∈ Set.univ,
        (z - z ^ 2 / 2) - p * z ≤ ((1 - p) - (1 - p) ^ 2 / 2) - p * (1 - p) := by
    intro p _
    refine ⟨Set.mem_univ _, fun z _ => ?_⟩
    have h := quad_surplus_le p z
    have hrhs : ((1 - p) - (1 - p) ^ 2 / 2) - p * (1 - p) = (1 - p) ^ 2 / 2 := by ring
    rw [hrhs]
    exact h
  have hdiff : ∀ p ∈ uIcc (1 : ℝ) (0 : ℝ),
      DifferentiableAt ℝ (fun p => ubar - (1 - p) ^ 2 / 2) p := by
    intro p _
    fun_prop
  have hint : IntervalIntegrable (fun p : ℝ => 1 - p) MeasureTheory.volume (0 : ℝ) 1 :=
    (continuous_const.sub continuous_id').intervalIntegrable 0 1
  have hmain := quasilinear_expenditure_sub_eq_integral_demand (Z := Set.univ)
    (φ := fun z => z - z ^ 2 / 2) (x := fun p => 1 - p)
    (e := fun p => ubar - (1 - p) ^ 2 / 2) (ubar := ubar) (p₀ := (1 : ℝ)) (p₁ := (0 : ℝ))
    he hx hdiff hint
  exact hmain

theorem welfare_eq_half (ubar : ℝ) :
    (ubar - (1 - (1 : ℝ)) ^ 2 / 2) - (ubar - (1 - (0 : ℝ)) ^ 2 / 2) = 1 / 2 := by
  ring

theorem surplus_eq_half : (∫ p in (0 : ℝ)..1, (1 - p)) = 1 / 2 := by
  rw [← welfare_eq_surplus 0]
  exact welfare_eq_half 0

end MathlibExtTest.Economics.Consumer.QuasilinearWelfare
