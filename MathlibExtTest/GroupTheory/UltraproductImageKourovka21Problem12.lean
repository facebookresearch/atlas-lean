/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.UltraproductImageKourovka21Problem12
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic

open MathlibExt.GroupTheory.UltraproductImageKourovka21Problem12Wanted

-- Evaluation at a principal ultrafilter works even when the cyclic subgroup is infinite.
example (k : ℕ) (B : Type) [Group B] : IsLocallyUltrapowerImage (pure k) B := by
  intro b
  let ψ : Multiplicative (ℕ → ℤ) →* Subgroup.zpowers b :=
    { toFun := fun f => ⟨b ^ f.toAdd k, Subgroup.zpow_mem_zpowers _ _⟩
      map_one' := Subtype.ext (zpow_zero b)
      map_mul' := fun _ _ => Subtype.ext (zpow_add b _ _) }
  refine ⟨_, ψ, Subgroup.mem_zpowers b, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    exact ⟨Multiplicative.ofAdd (fun _ => n), rfl⟩
  · intro f hf
    have hk : f k = 0 := hf
    exact Subtype.ext (show b ^ f k = 1 by rw [hk, zpow_zero])

-- Extract a counterexample for a specific nonprincipal ultrafilter.
example : ∃ (B : Type) (_ : Group B), IsLocallyUltrapowerImage (Filter.hyperfilter ℕ) B ∧
    ¬ ∃ (G : ℕ → Type) (_ : ∀ i, Group (G i)) (φ : (∀ i, G i) →* B), Function.Surjective φ ∧
      ∀ f : ∀ i, G i, (∀ᶠ i in Filter.hyperfilter ℕ, f i = 1) → φ f = 1 := by
  by_contra h
  apply locallyUltrapowerImageIsUltraproductImage_refuted
  refine ⟨_, Filter.hyperfilter_le_cofinite, ?_⟩
  intro B inst hB
  by_contra hφ
  exact h ⟨B, inst, hB, hφ⟩
