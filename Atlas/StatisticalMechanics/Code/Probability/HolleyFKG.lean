/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Code.Probability.StrassenFinite
import Mathlib.Combinatorics.SetFamily.FourFunctions

open Finset
open scoped NNReal

namespace StatMech
namespace Probability

variable {α : Type*}








section Conditions




def HolleyLatticeCondition [Lattice α] (μ₁ μ₂ : α → ℝ≥0) : Prop :=
  ∀ x y, μ₁ x * μ₂ y ≤ μ₁ (x ⊓ y) * μ₂ (x ⊔ y)



def FKGCondition [Lattice α] (μ : α → ℝ≥0) : Prop :=
  ∀ x y, μ x * μ y ≤ μ (x ⊓ y) * μ (x ⊔ y)


lemma FKGCondition.holleyLatticeCondition [Lattice α] {μ : α → ℝ≥0}
    (h : FKGCondition μ) : HolleyLatticeCondition μ μ := h

end Conditions





section Holley

variable [Fintype α] [DecidableEq α] [DistribLattice α]


private theorem upper_indicator_monotone {β : Type*} [Preorder β] [DecidableEq β] (U : Finset β)
    (hU : ∀ ⦃a b⦄, a ≤ b → a ∈ U → b ∈ U) :
    Monotone (fun a => if a ∈ U then (1 : ℝ) else 0) := by
  intro x y hxy
  by_cases hx : x ∈ U
  · simp only [hx, if_true, hU hxy hx, le_refl]
  · simp only [hx, if_false]
    split_ifs <;> norm_num

omit [DecidableEq α] in




theorem holley_le_of_monotone {μ₁ μ₂ : α → ℝ≥0}
    (hsum : ∑ a, μ₁ a = ∑ a, μ₂ a) (hcond : HolleyLatticeCondition μ₁ μ₂)
    {t : α → ℝ} (ht : Monotone t) (ht0 : 0 ≤ t) :
    ∑ a, t a * (μ₁ a : ℝ) ≤ ∑ a, t a * (μ₂ a : ℝ) := by
  
  have h₁ : (0 : α → ℝ) ≤ fun a => (μ₁ a : ℝ) := fun a => (μ₁ a).coe_nonneg
  have h₂ : (0 : α → ℝ) ≤ fun a => (μ₂ a : ℝ) := fun a => (μ₂ a).coe_nonneg
  have hsumR : (∑ a, (μ₁ a : ℝ)) = ∑ a, (μ₂ a : ℝ) := by exact_mod_cast hsum
  have hcondR : ∀ x y, (μ₁ x : ℝ) * (μ₂ y : ℝ) ≤ (μ₁ (x ⊓ y) : ℝ) * (μ₂ (x ⊔ y) : ℝ) := by
    intro x y; exact_mod_cast hcond x y
  exact holley (fun a => (μ₁ a : ℝ)) (fun a => (μ₂ a : ℝ)) t ht0 h₁ h₂ ht hsumR hcondR







theorem holley_domination {μ₁ μ₂ : α → ℝ≥0}
    (hsum : ∑ a, μ₁ a = ∑ a, μ₂ a) (hcond : HolleyLatticeCondition μ₁ μ₂) :
    StochasticDom μ₁ μ₂ := by
  intro U hU
  
  have hkey := holley_le_of_monotone (t := fun a => if a ∈ U then (1 : ℝ) else 0)
    hsum hcond (upper_indicator_monotone U hU)
    (fun a => by dsimp only; split_ifs <;> norm_num)
  
  have hL : ∀ (μ : α → ℝ≥0),
      ∑ a, (if a ∈ U then (1 : ℝ) else 0) * (μ a : ℝ) = ∑ a ∈ U, (μ a : ℝ) := by
    intro μ
    rw [← Finset.sum_filter_add_sum_filter_not (univ) (fun a => a ∈ U)]
    have h0 : ∑ a ∈ univ.filter (fun a => ¬ a ∈ U), (if a ∈ U then (1 : ℝ) else 0) * (μ a : ℝ) = 0 := by
      refine Finset.sum_eq_zero (fun a ha => ?_)
      rw [Finset.mem_filter] at ha
      rw [if_neg ha.2, zero_mul]
    rw [h0, add_zero]
    have hUfilter : univ.filter (fun a => a ∈ U) = U := by ext a; simp
    rw [hUfilter]
    exact Finset.sum_congr rfl (fun a ha => by rw [if_pos ha, one_mul])
  rw [hL μ₁, hL μ₂] at hkey
  
  have : (↑(∑ a ∈ U, μ₁ a) : ℝ) ≤ (↑(∑ a ∈ U, μ₂ a) : ℝ) := by push_cast; exact hkey
  exact_mod_cast this

end Holley



section Coupling

variable [Fintype α] [DecidableEq α] [DistribLattice α]
  [DecidableRel ((· ≤ ·) : α → α → Prop)]











theorem holley_exists_isMonotoneCoupling {μ₁ μ₂ : α → ℝ≥0}
    (hsum : ∑ a, μ₁ a = ∑ a, μ₂ a) (hcond : HolleyLatticeCondition μ₁ μ₂) :
    ∃ π : α × α → ℝ≥0, IsMonotoneCoupling μ₁ μ₂ π :=
  exists_isMonotoneCoupling_of_stochasticDom hsum (holley_domination hsum hcond)








theorem holley_domination_iff_monotoneCoupling {μ₁ μ₂ : α → ℝ≥0}
    (hsum : ∑ a, μ₁ a = ∑ a, μ₂ a) (hcond : HolleyLatticeCondition μ₁ μ₂) :
    StochasticDom μ₁ μ₂ ↔ ∃ π : α × α → ℝ≥0, IsMonotoneCoupling μ₁ μ₂ π :=
  ⟨fun _ => holley_exists_isMonotoneCoupling hsum hcond,
   fun ⟨_, hπ⟩ => StochasticDom.of_isMonotoneCoupling hπ⟩

end Coupling








section FKG

variable [Fintype α] [DecidableEq α] [DistribLattice α] [OrderBot α]

omit [DecidableEq α] in







theorem fkg_inequality {π : α → ℝ}
    (hπ₀ : 0 ≤ π) (hnorm : ∑ a, π a = 1)
    (hπ : ∀ x y, π x * π y ≤ π (x ⊓ y) * π (x ⊔ y))
    {f g : α → ℝ} (hf : Monotone f) (hg : Monotone g) :
    (∑ a, π a * f a) * (∑ a, π a * g a) ≤ ∑ a, π a * (f a * g a) := by
  
  have key : ∀ (f g : α → ℝ), Monotone f → Monotone g →
      (0 : α → ℝ) ≤ f → (0 : α → ℝ) ≤ g →
      (∑ a, π a * f a) * (∑ a, π a * g a) ≤ ∑ a, π a * (f a * g a) := by
    intro f g hf hg hf0 hg0
    have h := fkg f g π hπ₀ hf0 hg0 hf hg hπ
    rwa [hnorm, one_mul] at h
  
  have hfc : ∀ a, f ⊥ ≤ f a := fun a => hf bot_le
  have hgd : ∀ a, g ⊥ ≤ g a := fun a => hg bot_le
  set c := f ⊥ with hc
  set d := g ⊥ with hd
  have hf'm : Monotone (fun a => f a - c) := fun a b h => sub_le_sub_right (hf h) c
  have hg'm : Monotone (fun a => g a - d) := fun a b h => sub_le_sub_right (hg h) d
  have hf'0 : (0 : α → ℝ) ≤ fun a => f a - c := fun a => sub_nonneg.mpr (hfc a)
  have hg'0 : (0 : α → ℝ) ≤ fun a => g a - d := fun a => sub_nonneg.mpr (hgd a)
  have hk := key _ _ hf'm hg'm hf'0 hg'0
  have e1 : ∑ a, π a * (f a - c) = (∑ a, π a * f a) - c := by
    have h : ∀ a, π a * (f a - c) = π a * f a - c * π a := fun a => by ring
    simp_rw [h]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, mul_one]
  have e2 : ∑ a, π a * (g a - d) = (∑ a, π a * g a) - d := by
    have h : ∀ a, π a * (g a - d) = π a * g a - d * π a := fun a => by ring
    simp_rw [h]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, mul_one]
  have e3 : ∑ a, π a * ((f a - c) * (g a - d))
      = (∑ a, π a * (f a * g a)) - c * (∑ a, π a * g a) - d * (∑ a, π a * f a) + c * d := by
    have h : ∀ a, π a * ((f a - c) * (g a - d))
        = π a * (f a * g a) - c * (π a * g a) - d * (π a * f a) + (c * d) * π a :=
      fun a => by ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hnorm, mul_one]
  rw [e1, e2, e3] at hk
  nlinarith [hk]

end FKG












section Conditioning

variable [Fintype α] [DecidableEq α] [DistribLattice α]


private noncomputable def restrictTo (π : α → ℝ≥0) (S : Finset α) : α → ℝ≥0 :=
  fun a => if a ∈ S then π a else 0









theorem fkg_conditioning_domination {π : α → ℝ≥0} (hπ : FKGCondition π)
    {S : Finset α} (hS : ∀ ⦃a b⦄, a ≤ b → a ∈ S → b ∈ S) :
    StochasticDom ((∑ a ∈ S, π a) • π) ((∑ a, π a) • restrictTo π S) := by
  set Z : ℝ≥0 := ∑ a, π a with hZ
  set ZS : ℝ≥0 := ∑ a ∈ S, π a with hZS
  
  have hmass : ∑ a, (ZS • π) a = ∑ a, (Z • restrictTo π S) a := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hZ]
    have hsumR : ∑ a, restrictTo π S a = ZS := by
      unfold restrictTo
      rw [← Finset.sum_filter]
      congr 1
      ext a; simp
    rw [hsumR, mul_comm]
  
  have hcross : HolleyLatticeCondition ((ZS • π)) ((Z • restrictTo π S)) := by
    intro x y
    simp only [Pi.smul_apply, smul_eq_mul, restrictTo]
    by_cases hy : y ∈ S
    · have hxy : x ⊔ y ∈ S := hS le_sup_right hy
      rw [if_pos hy, if_pos hxy]
      
      have hfkg := hπ x y
      calc ZS * π x * (Z * π y)
            = (Z * ZS) * (π x * π y) := by ring
        _ ≤ (Z * ZS) * (π (x ⊓ y) * π (x ⊔ y)) := by
              gcongr
        _ = ZS * π (x ⊓ y) * (Z * π (x ⊔ y)) := by ring
    · rw [if_neg hy, mul_zero, mul_zero]
      exact zero_le'
  exact holley_domination hmass hcross

end Conditioning

end Probability
end StatMech
