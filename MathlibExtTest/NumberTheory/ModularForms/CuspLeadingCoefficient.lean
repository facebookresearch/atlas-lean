/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CuspLeadingCoefficient

@[expose] public section

open UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm

-- Consumer with the original binders.
example (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) (h : ℕ) (hh : 0 < h) (hper : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ /
        Function.Periodic.qParam h τ ^ n) atImInfty (𝓝 a) :=
  ModularForm.exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem Γ k f hf σ h hh hper

-- The nonvanishing hypothesis matters: for the zero form the quotient is
-- identically zero, so it cannot tend to a nonzero limit.
example (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (σ : SL(2, ℤ)) (h : ℕ) :
    ¬ ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => (((0 : ModularForm Γ k) : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ /
        Function.Periodic.qParam h τ ^ n) atImInfty (𝓝 a) := by
  rintro ⟨n, a, ha, hlim⟩
  have hzero : (fun τ : ℍ => (((0 : ModularForm Γ k) : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ /
      Function.Periodic.qParam h τ ^ n) = fun _ => (0 : ℂ) := by
    funext τ
    simp
  rw [hzero] at hlim
  exact ha (tendsto_nhds_unique hlim tendsto_const_nhds)
