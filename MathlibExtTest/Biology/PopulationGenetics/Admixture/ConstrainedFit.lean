/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Admixture.ConstrainedFit

/-! Tests for the nonnegativity-constrained qpGraph fit: generic restatements
against the repository `scoreS1`, and the one-edge boundary example. -/

open Matrix

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.ConstrainedFit

open MathlibExt.Biology.PopulationGenetics.QpGraph

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

example {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) (B : Matrix ι E ℝ) (f : ι → ℝ) :
    ∃ l : E → ℝ, IsConstrainedMaximizer Q B f l :=
  exists_isConstrainedMaximizer hQ B f

example {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) (B : Matrix ι E ℝ) (f : ι → ℝ)
    {l : E → ℝ} :
    IsConstrainedMaximizer Q B f l ↔
      (∀ e, 0 ≤ l e) ∧ (∀ e, (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e ≤ 0) ∧
        ∀ e, l e * (Bᵀ *ᵥ (Q⁻¹ *ᵥ (f - B *ᵥ l))) e = 0 :=
  isConstrainedMaximizer_iff hQ B f

example {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {B : Matrix ι E ℝ} {f : ι → ℝ}
    {l₁ l₂ : E → ℝ} (h₁ : IsConstrainedMaximizer Q B f l₁)
    (h₂ : IsConstrainedMaximizer Q B f l₂) : B *ᵥ l₁ = B *ᵥ l₂ :=
  mulVec_eq_of_isConstrainedMaximizer hQ h₁ h₂

example :
    IsConstrainedMaximizer (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (-1 : ℝ)) 0 ∧
      ∀ l : Fin 1 → ℝ, IsConstrainedMaximizer (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (-1 : ℝ)) l → l = 0 :=
  isConstrainedMaximizer_one_neg

end MathlibExtTest.Biology.PopulationGenetics.Admixture.ConstrainedFit
