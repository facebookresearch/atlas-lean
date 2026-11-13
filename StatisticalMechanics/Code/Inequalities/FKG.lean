/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















import Code.Inequalities.IncreasingEvent

open Finset

namespace StatMech

variable {E : Type*}








theorem fkg_inequality [Fintype E] [DecidableEq E] {π : ConfigSpace E → ℝ}
    (hπ₀ : 0 ≤ π) (hnorm : ∑ ω, π ω = 1) (hπ : FKGLatticeCondition π)
    {f g : ConfigSpace E → ℝ} (hf : Monotone f) (hg : Monotone g) :
    (∑ ω, π ω * f ω) * (∑ ω, π ω * g ω) ≤ ∑ ω, π ω * (f ω * g ω) := by
  
  have key : ∀ (f g : ConfigSpace E → ℝ), Monotone f → Monotone g →
      (0 : ConfigSpace E → ℝ) ≤ f → (0 : ConfigSpace E → ℝ) ≤ g →
      (∑ ω, π ω * f ω) * (∑ ω, π ω * g ω) ≤ ∑ ω, π ω * (f ω * g ω) := by
    intro f g hf hg hf0 hg0
    have hlatt : ∀ a b, π a * π b ≤ π (a ⊓ b) * π (a ⊔ b) :=
      fun a b => (hπ a b).trans (le_of_eq (mul_comm _ _))
    have h := fkg f g π hπ₀ hf0 hg0 hf hg hlatt
    rwa [hnorm, one_mul] at h
  
  have hfc : ∀ ω, f ⊥ ≤ f ω := fun ω => hf bot_le
  have hgd : ∀ ω, g ⊥ ≤ g ω := fun ω => hg bot_le
  set c := f ⊥ with hc
  set d := g ⊥ with hd
  have hf'm : Monotone (fun ω => f ω - c) := fun a b h => sub_le_sub_right (hf h) c
  have hg'm : Monotone (fun ω => g ω - d) := fun a b h => sub_le_sub_right (hg h) d
  have hf'0 : (0 : ConfigSpace E → ℝ) ≤ fun ω => f ω - c := fun ω => sub_nonneg.mpr (hfc ω)
  have hg'0 : (0 : ConfigSpace E → ℝ) ≤ fun ω => g ω - d := fun ω => sub_nonneg.mpr (hgd ω)
  have hk := key _ _ hf'm hg'm hf'0 hg'0
  have e1 : ∑ ω, π ω * (f ω - c) = (∑ ω, π ω * f ω) - c := by
    have h : ∀ ω, π ω * (f ω - c) = π ω * f ω - c * π ω := fun ω => by ring
    simp_rw [h]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, mul_one]
  have e2 : ∑ ω, π ω * (g ω - d) = (∑ ω, π ω * g ω) - d := by
    have h : ∀ ω, π ω * (g ω - d) = π ω * g ω - d * π ω := fun ω => by ring
    simp_rw [h]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, mul_one]
  have e3 : ∑ ω, π ω * ((f ω - c) * (g ω - d))
      = (∑ ω, π ω * (f ω * g ω)) - c * (∑ ω, π ω * g ω) - d * (∑ ω, π ω * f ω) + c * d := by
    have h : ∀ ω, π ω * ((f ω - c) * (g ω - d))
        = π ω * (f ω * g ω) - c * (π ω * g ω) - d * (π ω * f ω) + (c * d) * π ω :=
      fun ω => by ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hnorm, mul_one]
  rw [e1, e2, e3] at hk
  nlinarith [hk]




theorem fkg_inequality_events [Fintype E] [DecidableEq E] {π : ConfigSpace E → ℝ}
    (hπ₀ : 0 ≤ π) (hnorm : ∑ ω, π ω = 1) (hπ : FKGLatticeCondition π)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (∑ ω, π ω * A.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, π ω * B.indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ ω, π ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
  have hAB : (A ∩ B).indicator (fun _ => (1 : ℝ))
      = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
      simp [Set.indicator, ha, hb, Set.mem_inter_iff]
  rw [hAB]
  exact fkg_inequality hπ₀ hnorm hπ hA.indicator_monotone hB.indicator_monotone







theorem holley_inequality [Fintype E] [DecidableEq E] {μ₁ μ₂ : ConfigSpace E → ℝ}
    (h₁ : 0 ≤ μ₁) (h₂ : 0 ≤ μ₂) (hsum : ∑ ω, μ₁ ω = ∑ ω, μ₂ ω)
    (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b))
    {t : ConfigSpace E → ℝ} (ht : Monotone t) (ht0 : 0 ≤ t) :
    ∑ ω, t ω * μ₁ ω ≤ ∑ ω, t ω * μ₂ ω :=
  holley μ₁ μ₂ t ht0 h₁ h₂ ht hsum hcond




theorem holley_dominates [Fintype E] [DecidableEq E] {μ₁ μ₂ : ConfigSpace E → ℝ}
    (h₁ : 0 ≤ μ₁) (h₂ : 0 ≤ μ₂) (hsum : ∑ ω, μ₁ ω = ∑ ω, μ₂ ω)
    (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b))
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * μ₁ ω
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * μ₂ ω :=
  holley_inequality h₁ h₂ hsum hcond hA.indicator_monotone (indicator_nonneg' A)

end StatMech
