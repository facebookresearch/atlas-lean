/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Producer.InteriorFirstOrderConditions
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set
open MathlibExt.Economics.Producer

/-! A two-input binding cost minimum with unequal marginal products and positive prices. -/
example : ∃ lam : ℝ, 0 < lam ∧ lam = 3 ∧ (2 : ℝ) / 1 = 6 / 3 := by
  let f : (Fin 2 → ℝ) → ℝ := fun y ↦ 2 * y 0 + y 1
  let x : Fin 2 → ℝ := fun _ ↦ 1
  let w : Fin 2 → ℝ := fun i ↦ if i = 0 then 6 else 3
  have hx (i : Fin 2) : 0 < x i := by norm_num [x]
  have hw (i : Fin 2) : 0 < w i := by
    by_cases h : i = 0 <;> simp [w, h]
  have hdiff : DifferentiableAt ℝ f x := by
    fun_prop
  have hderiv : HasFDerivAt f
      ((2 : ℝ) • (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        ContinuousLinearMap.proj 1) x := by
    let d₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
    let d₁ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
    exact (d₀.hasFDerivAt.const_mul (2 : ℝ)).add d₁.hasFDerivAt
  have hcoord0 : fderiv ℝ f x (Pi.basisFun ℝ (Fin 2) 0) = 2 := by
    norm_num [hderiv.fderiv, Pi.basisFun_apply]
  have hcoord1 : fderiv ℝ f x (Pi.basisFun ℝ (Fin 2) 1) = 1 := by
    norm_num [hderiv.fderiv, Pi.basisFun_apply]
  have hreg : fderiv ℝ f x ≠ 0 := by
    intro h
    simp [h] at hcoord0
  have hbind : f x = 3 := by norm_num [f, x]
  have hmin : IsMinOn (fun y ↦ w ⬝ᵥ y) {y | (∀ i, 0 < y i) ∧ 3 ≤ f y} x := by
    intro y hy
    change w ⬝ᵥ x ≤ w ⬝ᵥ y
    have hout : 3 ≤ 2 * y 0 + y 1 := hy.2
    simp [dotProduct, Fin.sum_univ_two, w, x]
    linarith
  obtain ⟨lam, hlam, hcoord, -, hratio⟩ :=
    interior_first_order_conditions.2.1 hx hdiff hw hbind hreg hmin
  refine ⟨lam, hlam, ?_, ?_⟩
  · have h := hcoord 1
    rw [hcoord1, mul_one] at h
    simpa [w] using h.symm
  · have h := hratio 0 1
    rw [hcoord0, hcoord1] at h
    simpa [w] using h

/-! A strictly concave one-input technology, with an interior optimum at unit input. -/
example : (2 : ℝ) * fderiv ℝ (fun y : Fin 1 → ℝ ↦ 3 * y 0 - (y 0) ^ 2)
    (fun _ ↦ 1) (Pi.basisFun ℝ (Fin 1) 0) = 2 := by
  let f : (Fin 1 → ℝ) → ℝ := fun y ↦ 3 * y 0 - (y 0) ^ 2
  let x : Fin 1 → ℝ := fun _ ↦ 1
  let w : Fin 1 → ℝ := fun _ ↦ 2
  have hx (i : Fin 1) : 0 < x i := by norm_num [x]
  have hf : DifferentiableAt ℝ f x := by fun_prop
  have hmax : IsMaxOn (fun y ↦ 2 * f y - w ⬝ᵥ y) {y | ∀ i, 0 < y i} x := by
    intro y _
    change 2 * f y - w ⬝ᵥ y ≤ 2 * f x - w ⬝ᵥ x
    simp [f, x, w, dotProduct]
    nlinarith [sq_nonneg (y 0 - 1)]
  exact interior_first_order_conditions.1 hx hf hmax 0

-- Concavity of the technology and stationarity compose through the public API.
example {f : (Fin 2 → ℝ) → ℝ} {x w : Fin 2 → ℝ} {p : ℝ}
    (hx : ∀ i, 0 < x i) (hf : DifferentiableAt ℝ f x) (hp : 0 ≤ p)
    (hconc : ConcaveOn ℝ {y | ∀ i, 0 < y i} f)
    (hcoord : ∀ i, p * fderiv ℝ f x (Pi.basisFun ℝ (Fin 2) i) = w i) :
    IsMaxOn (fun y ↦ p * f y - w ⬝ᵥ y) {y | ∀ i, 0 < y i} x := by
  obtain ⟨hmax, hprofit⟩ := interior_first_order_conditions.2.2.1 (w := w) (p := p) hx hf
  exact hmax (hprofit hp hconc) hcoord

-- The same ordinary import exposes the counterexample, including unbounded profit.
example : deriv (fun t : ℝ ↦ t ^ 2) (1 / 2) = 1 ∧
    ¬ IsMaxOn (fun t : ℝ ↦ t ^ 2 - t) (Ioi 0) (1 / 2) ∧
    ∀ b : ℝ, ∃ t > 0, b < t ^ 2 - t := by
  obtain ⟨hd, -, hnot, hunbounded⟩ := interior_first_order_conditions.{0}.2.2.2.1
  refine ⟨hd.deriv, hnot, fun b ↦ ?_⟩
  by_contra! h
  exact hunbounded ⟨b, by
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht⟩

-- Two genuinely fractional exponents (total weight 1/2), not a unit-weight special case.
example : ConcaveOn ℝ {y : Fin 2 → ℝ | ∀ i, 0 < y i}
    (cobbDouglas 1 (fun _ ↦ (1 / 4 : ℝ))) := by
  exact interior_first_order_conditions.2.2.2.2 (fun _ ↦ by norm_num)
    (by norm_num [Fin.sum_univ_two])
