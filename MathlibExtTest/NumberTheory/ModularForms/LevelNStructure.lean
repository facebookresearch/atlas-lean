/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_WLight_levelN_structure_package.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
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

/-- `-1` fixes every Fricke function at a nonzero label, at every level. -/
example (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    frickeFunction N (labelVecMul N v (-1)) = frickeFunction N v :=
  (frickeFunction_labelVecMul_eq_iff N (-1)).2 (Or.inr (by simp)) v hv

/-- The zero label is a degenerate case, not a counterexample: Mathlib's `℘` is `0` at the
lattice point `0`, so the Fricke function at the zero label vanishes identically and the
conclusion of `exists_monic_relation_frickeFunction` also holds there, with `d = 1` and
`c = 0`. -/
example (N : ℕ) [NeZero N] :
    ∃ d : ℕ, ∃ c : ℕ → Polynomial ℂ, ∀ τ : ℍ,
      frickeFunction N 0 τ ^ d +
        ∑ k ∈ Finset.range d, (c k).eval (jFunction τ) * frickeFunction N 0 τ ^ k = 0 :=
  ⟨1, 0, fun τ ↦ by simp [frickeFunction, weierstrassTorsion, PeriodPair.weierstrassP_zero]⟩

/-- The level-`N` algebra contains `j`, so `j` is holomorphic. -/
example (N : ℕ) [NeZero N] : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jFunction :=
  mdifferentiable_of_mem_levelNAlgebra (jFunction_mem_levelNAlgebra N)

/-! ### Level `3` -/

/-- Labels are row vectors: `T = !![1, 1; 0, 1]` sends `(1, 0)` to `(1, 1)` and fixes `(0, 1)`,
where the column action `v ↦ T v` would fix `(1, 0)` and move `(0, 1)`. -/
example : labelVecMul 3 ![1, 0] ModularGroup.T = ![1, 1] ∧
    labelVecMul 3 ![0, 1] ModularGroup.T = ![0, 1] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [labelVecMul, Matrix.vecMul, dotProduct, Fin.sum_univ_two, ModularGroup.coe_T]

/-- The `±` matters at level `3`: `-1 ∉ Γ(3)` and `-1` moves every nonzero label, yet it fixes
every Fricke function at a nonzero label. -/
example : -1 ∉ CongruenceSubgroup.Gamma 3 ∧
    (∀ v : Fin 2 → ZMod 3, v ≠ 0 → labelVecMul 3 v (-1) ≠ v) ∧
    ∀ v : Fin 2 → ZMod 3, v ≠ 0 →
      frickeFunction 3 (labelVecMul 3 v (-1)) = frickeFunction 3 v := by
  refine ⟨?_, fun v hv h ↦ hv ?_,
    (frickeFunction_labelVecMul_eq_iff 3 (-1)).2 (Or.inr (by simp))⟩
  · rw [CongruenceSubgroup.Gamma_mem]
    decide
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [labelVecMul, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h1
    have key : ∀ x : ZMod 3, -x = x → x = 0 := by decide
    funext i
    fin_cases i
    · exact key _ h0
    · exact key _ h1

/-- The hard direction of `frickeFunction_labelVecMul_eq_iff` at level `3`: neither `T` nor
`-T` lies in `Γ(3)`, so `T` moves the Fricke function at some nonzero label. -/
example : ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧
    frickeFunction 3 (labelVecMul 3 v ModularGroup.T) ≠ frickeFunction 3 v := by
  have hT : ¬ (ModularGroup.T ∈ CongruenceSubgroup.Gamma 3 ∨
      -ModularGroup.T ∈ CongruenceSubgroup.Gamma 3) := by
    simp only [CongruenceSubgroup.Gamma_mem, Matrix.SpecialLinearGroup.coe_neg,
      ModularGroup.coe_T]
    decide
  have h := mt (frickeFunction_labelVecMul_eq_iff 3 ModularGroup.T).1 hT
  simp only [not_forall, exists_prop] at h
  exact h
