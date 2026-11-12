/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import MathlibExt.Probability.FiniteProbability

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Cheeger's inequality: the easy direction

If `gap` is a Poincare constant for a reversible Markov kernel,
then every set of stationary mass in `(0, 1/2]` has
`gap ≤ 2 * conductance`. The positivity of the mass is essential:
a zero-mass set has conductance `0` by convention while the
Poincare hypothesis is vacuous on it (an earlier draft of this
statement without positivity was refuted by the `Fin 2` point-mass
example). This extends `MathlibExt/Probability/MarkovChainPoincare.lean`
(roadmap package ML-26).

The mean and variance are `FiniteProbability.expectation` /
`FiniteProbability.variance`; the one-step function evolution
would be `Matrix.mulVec` and is not needed here, so no local copies
of either are defined.

Source: Levin and Peres, Markov Chains and Mixing Times (2017),
Chapter 12.
-/

open Finset

namespace MathlibExt.Probability.MarkovChainConductance

open MathlibExt.Probability.FiniteProbability

/-- The Dirichlet form of the kernel `K` at `f` against `π`. -/
noncomputable def dirichletForm {α : Type*} [Fintype α] (K : α → α → ℝ)
    (π : α → ℝ) (f : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, π x * K x y * (f y - f x) ^ 2

/-- The conductance of a set `S`: the stationary flow out of `S`
divided by the stationary mass of `S` (`0` if the mass is `0`). -/
noncomputable def conductance {α : Type*} [Fintype α] [DecidableEq α] (K : α → α → ℝ)
    (π : α → ℝ) (S : Finset α) : ℝ :=
  (∑ x ∈ S, ∑ y ∈ Finset.univ \ S, π x * K x y) / (∑ x ∈ S, π x)

/-- Cheeger's inequality, easy direction (test-function form): if
`gap` is a Poincaré constant for `K` (every function's Dirichlet
form dominates `gap` times its variance), then for every set `S`
of stationary mass at most `1 / 2`, `gap ≤ 2 * conductance S`. -/

theorem gap_le_two_mul_conductance {α : Type*} [Fintype α] [DecidableEq α]
    {K : α → α → ℝ} {π : α → ℝ} {gap : ℝ}
    (hK_nonneg : ∀ x y, 0 ≤ K x y)
    (hK_sum : ∀ x, ∑ y, K x y = 1)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : ∀ y, ∑ x, π x * K x y = π y)
    (hrev : ∀ x y, π x * K x y = π y * K y x)
    (hpoincare : ∀ f : α → ℝ, gap * variance π f ≤ dirichletForm K π f)
    (S : Finset α) (hS : ∑ x ∈ S, π x ≤ 1 / 2)
    (hSpos : 0 < ∑ x ∈ S, π x) :
    gap ≤ 2 * conductance K π S := by
  set πS : ℝ := ∑ x ∈ S, π x with hπS
  set flow : ℝ := ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, π x * K x y with hflow
  set f : α → ℝ := fun x => if x ∈ S then (1 : ℝ) else 0 with hf
  have hfx_mem : ∀ x ∈ S, f x = 1 := fun x hx => by simp [hf, hx]
  have hfx_nmem : ∀ x ∉ S, f x = 0 := fun x hx => by simp [hf, hx]
  have h1 : ∀ x ∈ (Finset.univ : Finset α), π x * f x = (if x ∈ S then π x else 0) := by
    intro x _
    by_cases hx : x ∈ S
    · rw [hfx_mem x hx]; simp [hx]
    · rw [hfx_nmem x hx]; simp [hx]
  have hside : ∀ x ∈ (Finset.univ : Finset α), x ∉ S → (if x ∈ S then π x else 0) = 0 := by
    intro x _ hx
    simp [hx]
  have hmean : expectation π f = πS := by
    simp only [expectation]
    rw [hπS]
    calc ∑ x, π x * f x = ∑ x, (if x ∈ S then π x else 0) :=
            Finset.sum_congr rfl h1
      _ = ∑ x ∈ S, (if x ∈ S then π x else 0) :=
            (Finset.sum_subset (Finset.subset_univ S) hside).symm
      _ = ∑ x ∈ S, π x :=
            Finset.sum_congr rfl (fun x hx => by simp [hx])
  have hS_part : ∑ x ∈ S, π x * (f x - πS) ^ 2 = πS * (1 - πS) ^ 2 := by
    have hterm : ∀ x ∈ S, π x * (f x - πS) ^ 2 = π x * (1 - πS) ^ 2 := by
      intro x hx
      rw [hfx_mem x hx]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hπS]
  have hsum : ∑ x ∈ Finset.univ \ S, π x = 1 - πS := by
    have htot : (∑ x ∈ Finset.univ \ S, π x) + (∑ x ∈ S, π x) = ∑ x, π x :=
      Finset.sum_sdiff (Finset.subset_univ S)
    rw [hπ_sum] at htot
    have hSS : ∑ x ∈ S, π x = πS := hπS.symm
    rw [hSS] at htot
    linarith [htot]
  have hSc_part : ∑ x ∈ Finset.univ \ S, π x * (f x - πS) ^ 2 = (1 - πS) * πS ^ 2 := by
    have hterm : ∀ x ∈ Finset.univ \ S, π x * (f x - πS) ^ 2 = π x * πS ^ 2 := by
      intro x hx
      have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
      rw [hfx_nmem x hxS]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hsum]
  have hvar : variance π f = πS * (1 - πS) := by
    simp only [variance]
    rw [hmean]
    simp only [expectation]
    have hsplit : (∑ x ∈ Finset.univ \ S, π x * (f x - πS) ^ 2)
        + (∑ x ∈ S, π x * (f x - πS) ^ 2)
        = ∑ x, π x * (f x - πS) ^ 2 :=
      Finset.sum_sdiff (Finset.subset_univ S)
    rw [hSc_part, hS_part] at hsplit
    have hring : (1 - πS) * πS ^ 2 + πS * (1 - πS) ^ 2 = πS * (1 - πS) := by ring
    rw [hring] at hsplit
    exact hsplit.symm
  have hG : ∀ x, (∑ y, π x * K x y * (f y - f x) ^ 2)
      = (∑ y ∈ S, π x * K x y * (f y - f x) ^ 2)
        + ∑ y ∈ Finset.univ \ S, π x * K x y * (f y - f x) ^ 2 := by
    intro x
    have h : (∑ y ∈ Finset.univ \ S, π x * K x y * (f y - f x) ^ 2)
        + (∑ y ∈ S, π x * K x y * (f y - f x) ^ 2)
        = ∑ y, π x * K x y * (f y - f x) ^ 2 :=
      Finset.sum_sdiff (Finset.subset_univ S)
    rw [← h]
    ring
  have hGS : ∀ x ∈ S, (∑ y, π x * K x y * (f y - f x) ^ 2)
      = ∑ y ∈ Finset.univ \ S, π x * K x y := by
    intro x hx
    rw [hG x]
    have hz : (∑ y ∈ S, π x * K x y * (f y - f x) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [hfx_mem x hx, hfx_mem y hy]
      ring
    have ho : (∑ y ∈ Finset.univ \ S, π x * K x y * (f y - f x) ^ 2)
        = ∑ y ∈ Finset.univ \ S, π x * K x y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
      rw [hfx_mem x hx, hfx_nmem y hyS]
      ring
    rw [hz, ho, zero_add]
  have hGSc : ∀ x ∉ S, (∑ y, π x * K x y * (f y - f x) ^ 2)
      = ∑ y ∈ S, π x * K x y := by
    intro x hx
    rw [hG x]
    have hz : (∑ y ∈ Finset.univ \ S, π x * K x y * (f y - f x) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
      rw [hfx_nmem x hx, hfx_nmem y hyS]
      ring
    have ho : (∑ y ∈ S, π x * K x y * (f y - f x) ^ 2)
        = ∑ y ∈ S, π x * K x y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hfx_nmem x hx, hfx_mem y hy]
      ring
    rw [hz, ho, add_zero]
  have hS_outer : (∑ x ∈ S, ∑ y, π x * K x y * (f y - f x) ^ 2)
      = ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, π x * K x y :=
    Finset.sum_congr rfl (fun x hx => hGS x hx)
  have hSc_outer : (∑ x ∈ Finset.univ \ S, ∑ y, π x * K x y * (f y - f x) ^ 2)
      = ∑ x ∈ Finset.univ \ S, ∑ y ∈ S, π x * K x y :=
    Finset.sum_congr rfl (fun x hx => hGSc x ((Finset.mem_sdiff.mp hx).2))
  have hsplit : (∑ x ∈ Finset.univ \ S, ∑ y, π x * K x y * (f y - f x) ^ 2)
      + (∑ x ∈ S, ∑ y, π x * K x y * (f y - f x) ^ 2)
      = ∑ x, ∑ y, π x * K x y * (f y - f x) ^ 2 :=
    Finset.sum_sdiff (Finset.subset_univ S)
  have hrev_sum : (∑ x ∈ Finset.univ \ S, ∑ y ∈ S, π x * K x y)
      = ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, π x * K x y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    exact hrev x y
  have hform : dirichletForm K π f = flow := by
    simp only [dirichletForm]
    rw [← hsplit, hSc_outer, hS_outer, hrev_sum, ← hflow]
    ring
  have hflow_nonneg : 0 ≤ flow := by
    rw [hflow]
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (hπ_nonneg x) (hK_nonneg x y)
  have hprod_pos : 0 < πS * (1 - πS) := mul_pos hSpos (by linarith [hS])
  have hmain : gap * (πS * (1 - πS)) ≤ flow := by
    have h := hpoincare f
    rw [hvar, hform] at h
    exact h
  have hcond_eq : conductance K π S = flow / πS := by
    simp only [conductance]
    rw [hflow, hπS]
  rw [hcond_eq]
  refine le_of_mul_le_mul_right (a := πS * (1 - πS)) ?_ hprod_pos
  have hπS_ne : πS ≠ 0 := ne_of_gt hSpos
  have hcancel : (2 * (flow / πS)) * (πS * (1 - πS)) = 2 * flow * (1 - πS) := by
    field_simp
  rw [hcancel]
  have hle : flow ≤ 2 * flow * (1 - πS) := by
    have h1 : (0 : ℝ) ≤ flow * (1 - 2 * πS) := mul_nonneg hflow_nonneg (by linarith [hS])
    linarith [h1]
  exact le_trans hmain hle

end MathlibExt.Probability.MarkovChainConductance

