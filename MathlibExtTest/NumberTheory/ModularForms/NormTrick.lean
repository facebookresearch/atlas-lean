/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.NormTrick

@[expose] public section

open scoped ModularForm

example (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne]
    {k : ℤ} (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : UpperHalfPlane → ℂ) ∣[k] h) * (⇑G : UpperHalfPlane → ℂ) =
      (⇑F : UpperHalfPlane → ℂ) * ((⇑G : UpperHalfPlane → ℂ) ∣[k] h)) :
    ∃ Φ : ModularForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ)),
      (⇑Φ : UpperHalfPlane → ℂ) * (⇑G : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) * (⇑(ModularForm.norm ℋ G) : UpperHalfPlane → ℂ) :=
  ModularForm.exists_mul_eq_mul_norm_of_forall_slash_mul_eq 𝒢 ℋ F G hFG

example (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne]
    {k : ℤ} :
    ∃ Φ : ModularForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ)),
      (⇑Φ : UpperHalfPlane → ℂ) * (⇑(0 : ModularForm 𝒢 k) : UpperHalfPlane → ℂ) =
        (⇑(0 : ModularForm 𝒢 k) : UpperHalfPlane → ℂ) *
          (⇑(ModularForm.norm ℋ (0 : ModularForm 𝒢 k)) : UpperHalfPlane → ℂ) :=
  ModularForm.exists_mul_eq_mul_norm_of_forall_slash_mul_eq 𝒢 ℋ 0 0 (fun h _ => by simp)
