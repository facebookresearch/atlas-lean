/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_DiscreteProjectiveAction.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Discrete projective actions

A homomorphism `ρ : G →* PGL(2, K₀)` is *discrete* when, for every
nonzero threshold `ε` in the value group, only finitely many `γ : G`
have a lift to `GL (Fin 2) K₀` whose entries have valuation at most
`1` and whose determinant has valuation at least `ε`, after mapping
the entries into an extension field `K`.
-/

@[expose] public section

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace Omega

/-- Discreteness of a projective representation: for each nonzero
`ε`, the set of group elements with a bounded lift of determinant
valuation at least `ε` is finite. -/
public def IsDiscrete {K₀ : Type*} [Field K₀] (K : Type*) [Field K]
    [Algebra K₀ K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) : Prop :=
  ∀ ε : Γ₀, ε ≠ 0 →
    {γ : G | ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = ρ γ ∧
      (∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1) ∧
      ε ≤ Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)))}.Finite

public theorem isDiscrete_iff {K₀ : Type*} [Field K₀] {K : Type*} [Field K]
    [Algebra K₀ K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) :
    IsDiscrete K ρ ↔
      ∀ ε : Γ₀, ε ≠ 0 →
        {γ : G | ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = ρ γ ∧
          (∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1) ∧
          ε ≤ Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)))}.Finite :=
  Iff.rfl

/-- Discreteness at a threshold `ε` persists at every larger
threshold: the corresponding set of group elements only shrinks. -/
public theorem IsDiscrete.finite_of_le {K₀ : Type*} [Field K₀] {K : Type*}
    [Field K] [Algebra K₀ K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] {G : Type*} [Group G]
    {ρ : G →* PGL(2, K₀)} (hρ : IsDiscrete K ρ) {ε ε' : Γ₀} (hε : ε ≠ 0)
    (hle : ε ≤ ε') :
    {γ : G | ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = ρ γ ∧
      (∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1) ∧
      ε' ≤ Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)))}.Finite :=
  (hρ ε hε).subset fun γ hγ => by
    obtain ⟨g, hg, hentries, hdet⟩ := hγ
    exact ⟨g, hg, hentries, le_trans hle hdet⟩

end Omega
end CerednikDrinfeld
