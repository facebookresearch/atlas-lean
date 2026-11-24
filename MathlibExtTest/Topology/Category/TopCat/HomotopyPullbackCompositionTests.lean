/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback

/-!
# Simplifying composition of full homotopy-pullback maps

The composition rule matches both actual squares on its simplifier
left-hand side. The original theorem statement is retained.
-/

public section

open CategoryTheory

universe u

example {X₀ Y₀ B₀ X₁ Y₁ B₁ X₂ Y₂ B₂ : TopCat.{u}}
    {f₀ : X₀ ⟶ B₀} {g₀ : Y₀ ⟶ B₀}
    {f₁ : X₁ ⟶ B₁} {g₁ : Y₁ ⟶ B₁}
    {f₂ : X₂ ⟶ B₂} {g₂ : Y₂ ⟶ B₂}
    (l₁ : X₀ ⟶ X₁) (r₁ : Y₀ ⟶ Y₁) (h₁ : B₀ ⟶ B₁)
    (l₂ : X₁ ⟶ X₂) (r₂ : Y₁ ⟶ Y₂) (h₂ : B₁ ⟶ B₂)
    (hf₁ : f₀ ≫ h₁ = l₁ ≫ f₁) (hg₁ : g₀ ≫ h₁ = r₁ ≫ g₁)
    (hf₂ : f₁ ≫ h₂ = l₂ ≫ f₂) (hg₂ : g₁ ≫ h₂ = r₂ ≫ g₂)
    (hf : f₀ ≫ (h₁ ≫ h₂) = (l₁ ≫ l₂) ≫ f₂)
    (hg : g₀ ≫ (h₁ ≫ h₂) = (r₁ ≫ r₂) ≫ g₂) :
    TopCat.homotopyPullbackMap l₁ r₁ h₁ hf₁ hg₁ ≫
        TopCat.homotopyPullbackMap l₂ r₂ h₂ hf₂ hg₂ =
      TopCat.homotopyPullbackMap (l₁ ≫ l₂) (r₁ ≫ r₂) (h₁ ≫ h₂) hf hg := by
  simp
