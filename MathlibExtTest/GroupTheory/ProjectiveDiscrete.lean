/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.ProjectiveDiscrete

@[expose] public section

open CerednikDrinfeld.Omega
open scoped MatrixGroups

/-- Consumer with the original binders: discreteness unfolds to
finiteness of the bounded-lift sets at every nonzero threshold. -/
private theorem exactSource {K₀ : Type*} [Field K₀] (K : Type*) [Field K]
    [Algebra K₀ K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) :
    IsDiscrete K ρ ↔
      ∀ ε : Γ₀, ε ≠ 0 →
        {γ : G | ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = ρ γ ∧
          (∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1) ∧
          ε ≤ Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)))}.Finite :=
  isDiscrete_iff ρ

/-- Threshold monotonicity, exercised through the public API. -/
example {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type*} [Group G] {ρ : G →* PGL(2, K₀)} (hρ : IsDiscrete K ρ)
    {ε ε' : Γ₀} (hε : ε ≠ 0) (hle : ε ≤ ε') :
    {γ : G | ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = ρ γ ∧
      (∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1) ∧
      ε' ≤ Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)))}.Finite :=
  hρ.finite_of_le hε hle
