/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

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

end PeriodPair
