/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.LevelNStructure

@[expose] public section

open WLight UpperHalfPlane

open scoped MatrixGroups Manifold

/-- Consumer with the original binders: the source statement, with `L`, `W`, `fricke` and `jf`
given by their defining equations, follows from `WLight.levelN_structure_package`. -/
private theorem exactSource
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    let A_N : Subalgebra ℂ (ℍ → ℂ) := Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v})
    let vecMul : (Fin 2 → ZMod N) → SL(2, ℤ) → Fin 2 → ZMod N := fun v γ ↦
      Matrix.vecMul v ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))
    ({γ : SL(2, ℤ) | ∀ v : Fin 2 → ZMod N, v ≠ 0 → fricke (vecMul v γ) = fricke v} =
      {γ : SL(2, ℤ) | γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N})
    ∧ (∀ a b : ℍ → ℂ, a ∈ A_N → b ∈ A_N → b ≠ 0 →
        (∀ γ : SL(2, ℤ), a * (b ∘ (γ • ·)) = (a ∘ (γ • ·)) * b) →
        ∃ p q : Polynomial ℂ, q ≠ 0 ∧ a * (fun τ ↦ q.eval (jf τ)) = b * (fun τ ↦ p.eval (jf τ)))
    ∧ (∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ d : ℕ, ∃ c : ℕ → Polynomial ℂ,
        ∀ τ, fricke v τ ^ d
          + ∑ k ∈ Finset.range d, (c k).eval (jf τ) * fricke v τ ^ k = 0)
    ∧ (∀ P : Polynomial ℂ, (∀ τ : ℍ, P.eval (jf τ) = 0) → P = 0)
    ∧ (∀ F ∈ A_N, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    ∧ (∀ a b : ℍ → ℂ, a ∈ A_N → b ∈ A_N → a * b = 0 → a = 0 ∨ b = 0) := by
  have hLp : ∀ τ, L τ = periodPairOfTau τ := fun τ ↦ by
    have h1 := (hL τ).1
    have h2 := (hL τ).2
    revert h1 h2
    generalize L τ = P
    rcases P with ⟨ω₁, ω₂, _⟩
    intro h1 h2
    dsimp only at h1 h2
    subst h1 h2
    rfl
  obtain rfl : jf = jFunction := funext hjf
  obtain rfl : fricke = frickeFunction N := funext₂ fun v τ ↦ by
    rw [hfricke, hW, hLp]; rfl
  intro A_N vecMul
  have hAN : A_N = levelNAlgebra N := by
    simp only [A_N, levelNAlgebra, mem_nonzeroTorsionLabels]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := levelN_structure_package N
  exact ⟨h1, hAN ▸ h2, h3, h4, hAN ▸ h5, hAN ▸ h6⟩

/-- The `±` in the stabilizer matters: `-1` fixes every Fricke function. -/
example (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    frickeFunction N (labelVecMul N v (-1)) = frickeFunction N v :=
  (frickeFunction_labelVecMul_eq_iff N (-1)).2 (Or.inr (by simp)) v hv

/-- The nonzero-label hypothesis matters for the monic relations: the zero label's Fricke
function is identically `0`, which satisfies the relation `f ^ 1 = 0`, while each nonzero
label gives some relation over `ℂ[j]`. -/
example (N : ℕ) [NeZero N] :
    ∀ τ : ℍ, frickeFunction N 0 τ ^ 1 = 0 := by
  intro τ
  simp [frickeFunction, weierstrassTorsion, PeriodPair.weierstrassP_zero]

/-- The level-`N` algebra contains `j`, so `j` is holomorphic. -/
example (N : ℕ) [NeZero N] : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jFunction :=
  mdifferentiable_of_mem_levelNAlgebra (jFunction_mem_levelNAlgebra N)
