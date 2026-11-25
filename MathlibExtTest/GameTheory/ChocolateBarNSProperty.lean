/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ChocolateBarNSProperty

open MetaMathlibExt

-- For the constant-one function the threshold supplied by the theorem must be zero.
example : ∃ m : ℕ, m = 0 ∧ (fun _ : ℕ ↦ 1) = (Set.Ici m).indicator (1 : ℕ → ℕ) := by
  obtain ⟨m, _, hm⟩ := (indicator_Ici_even_iff_hasNSProperty monotone_const
    (fun _ ↦ le_rfl) ⟨0, rfl⟩).mpr (hasNSProperty_const 1)
  refine ⟨m, ?_, hm⟩
  by_contra hn
  simpa [Set.indicator, hn] using congrFun hm 0

-- A positive even threshold gives a nonconstant function with the NS property.
example : HasNSProperty (fun z : ℕ ↦ if 4 ≤ z then 1 else 0) := by
  have hmono : Monotone (fun z : ℕ ↦ if 4 ≤ z then 1 else 0) := by
    intro a b hab
    dsimp only
    split_ifs <;> omega
  apply (indicator_Ici_even_iff_hasNSProperty hmono (fun z ↦ by split_ifs <;> decide)
    ⟨4, rfl⟩).mp
  exact ⟨4, ⟨2, rfl⟩, by funext z; simp [Set.indicator]⟩

-- The odd threshold three separates two inputs in the same block of length two.
example : ¬ HasNSProperty ((Set.Ici 3).indicator (1 : ℕ → ℕ)) := by
  intro hns
  have hpair := hns.2 2 3 1 (by decide) (by decide)
  simp [Set.indicator] at hpair

-- Inputs in the same block of eight have quotients by four in the same block of four.
example {a b : ℕ} (h : a / 8 = b / 8) : a / 4 / 4 = b / 4 / 4 :=
  (hasNSProperty_div_two_pow (m := 2) (by decide)).2 a b 3 (by decide) h

-- Exponent zero gives the identity, so positivity of the exponent is necessary.
example : ¬ HasNSProperty (fun x : ℕ ↦ x / 2 ^ 0) := by
  intro h
  have hpair := h.2 0 1 1 (by decide) rfl
  exact absurd hpair (by decide)

-- At cutoff zero, every function qualifies regardless of its values at positive inputs.
example (h : ℕ → ℕ) : HasNSProperty (fun x ↦ if x ≤ 0 then h x else h 0) := by
  apply hasNSProperty_extend_const
  · intro a b hab hb
    have : a = b := by omega
    simp [this]
  · intro a b i ha hb _ _
    simp [Nat.le_zero.mp ha, Nat.le_zero.mp hb]

-- The dyadic block {2, 3} straddles the cutoff of this nonconstant extension.
example : HasNSProperty (fun x : ℕ ↦ if x ≤ 2 then x / 2 else 1) := by
  have hh := hasNSProperty_div_two_pow (m := 1) (by decide)
  exact hasNSProperty_extend_const 2 (fun x ↦ x / 2)
    (fun _ _ hab _ ↦ hh.1 hab) (fun a b i _ _ ↦ hh.2 a b i)
