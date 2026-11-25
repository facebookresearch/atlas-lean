/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-
Portions of this file are adapted from:

`Definitions/Def_PeriodPair_Uniformization.lean`,
`Theorems/Thm_PeriodPair_weierstrassP_scale.lean`
and
`P2M/Sol/S_PeriodPair_weierstrassP_scale.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

/-!
# Homothetic complex period lattices

Two period lattices are homothetic when one is a nonzero complex scaling of the other.
-/

@[expose] public section

open scoped Pointwise

namespace PeriodPair

/-- **Homothetic period pairs.** A period pair is a pair $(\omega_1, \omega_2)$ of complex
numbers that are linearly independent over $\mathbb{R}$, and its lattice is
$\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2 \subseteq \mathbb{C}$. Two period pairs
$L$ and $L'$ with lattices $\Lambda$ and $\Lambda'$ are homothetic when there is a nonzero
complex number $c$ such that $\Lambda' = c\Lambda = \{c\lambda : \lambda \in \Lambda\}$. -/
def IsHomothetic (L L' : PeriodPair) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)

/-- **Homothety of period pairs is reflexive.** Every period pair $L$ is
homothetic to itself. -/
theorem IsHomothetic.refl (L : PeriodPair) : IsHomothetic L L :=
  ⟨1, one_ne_zero, (one_smul ℂ (L.lattice : Set ℂ)).symm⟩

/-- **Homothety of period pairs is symmetric.** If a period pair $L$ is homothetic to a period
pair $L'$, then $L'$ is homothetic to $L$. -/
theorem IsHomothetic.symm {L L' : PeriodPair} (h : IsHomothetic L L') :
    IsHomothetic L' L := by
  obtain ⟨c, hc, hLat⟩ := h
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [hLat, inv_smul_smul₀ hc]⟩

/-- **Homothety of period pairs is transitive.** For period pairs $L_1$, $L_2$, $L_3$,
if $L_1$ is homothetic to $L_2$ and $L_2$ is homothetic to $L_3$, then $L_1$ is homothetic
to $L_3$. -/
theorem IsHomothetic.trans {L₁ L₂ L₃ : PeriodPair}
    (h₁₂ : IsHomothetic L₁ L₂) (h₂₃ : IsHomothetic L₂ L₃) :
    IsHomothetic L₁ L₃ := by
  obtain ⟨c₁, hc₁, h₁₂⟩ := h₁₂
  obtain ⟨c₂, hc₂, h₂₃⟩ := h₂₃
  exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, by rw [h₂₃, h₁₂, smul_smul]⟩

/-- **Homothety of period pairs is an equivalence relation.** On period pairs,
homothety is reflexive, symmetric and transitive. -/
theorem isHomothetic_equivalence : Equivalence IsHomothetic :=
  ⟨IsHomothetic.refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- The period pair obtained by scaling both periods by a complex unit. -/
def scale (L : PeriodPair) (α : ℂˣ) : PeriodPair where
  ω₁ := (α : ℂ) * L.ω₁
  ω₂ := (α : ℂ) * L.ω₂
  indep := by
    have h : ![(α : ℂ) * L.ω₁, (α : ℂ) * L.ω₂] =
        (LinearMap.mulLeft ℝ (α : ℂ)) ∘ ![L.ω₁, L.ω₂] := by
      funext i
      fin_cases i <;> simp
    rw [h]
    exact L.indep.map' (LinearMap.mulLeft ℝ (α : ℂ))
      (LinearMap.ker_eq_bot_of_injective (mul_right_injective₀ α.ne_zero))

@[simp] theorem scale_ω₁ (L : PeriodPair) (α : ℂˣ) :
    (L.scale α).ω₁ = (α : ℂ) * L.ω₁ :=
  rfl

@[simp] theorem scale_ω₂ (L : PeriodPair) (α : ℂˣ) :
    (L.scale α).ω₂ = (α : ℂ) * L.ω₂ :=
  rfl

/-- Homothety covariance of the Weierstrass `℘`-function: scaling the period
lattice by `α` scales `℘` by `α⁻²`. -/
theorem weierstrassP_scale (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    (L.scale α).weierstrassP ((α : ℂ) * z) = ((α : ℂ) ^ 2)⁻¹ * L.weierstrassP z := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP,
    ← (L.scale α).latticeEquivProd.symm.toEquiv.tsum_eq,
    ← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
  congr 1 with p
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, scale_ω₁, scale_ω₂]
  rw [show (α : ℂ) * z - ((p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂)) =
      α * (z - (p.1 * L.ω₁ + p.2 * L.ω₂)) by ring,
    show ((p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂)) =
      α * (p.1 * L.ω₁ + p.2 * L.ω₂) by ring,
    mul_pow, mul_pow, one_div, one_div, one_div, one_div, mul_inv, mul_inv, mul_sub]

end PeriodPair
