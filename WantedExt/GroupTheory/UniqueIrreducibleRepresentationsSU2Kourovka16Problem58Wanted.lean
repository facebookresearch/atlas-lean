/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups with one irreducible representation of each dimension (Kourovka Notebook Problem 16.58)

Kourovka Notebook, Archive of Solved Problems, Problem 16.58 (J. McKay): is `SU₂(ℂ)` the only group
that has just one irreducible complex representation of dimension `n` for each `n = 1, 2, …`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace MathlibExt.GroupTheory.UniqueIrreducibleRepresentationsSU2Kourovka16Problem58Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.58 (J.
McKay). UnsolvedMath record UM-00701250 (`KOU-16.58`), dataset ulamai/UnsolvedMath v1.8.0.

Representations are all homomorphisms `G →* GLₙ(ℂ)` of the abstract group, without continuity, as in
the Archive's answer; irreducible means no invariant subspace other than `0` and `ℂⁿ`, and "just
one" means one up to conjugation by `GLₙ(ℂ)`. "`SU₂(ℂ)` is the only such group" is stated as: a
group in `Type` has the property if and only if it is isomorphic to `SU₂(ℂ)`
(`Matrix.specialUnitaryGroup (Fin 2) ℂ`).
-/

/-- The complex representation `ρ : G →* GLₙ(ℂ)` is irreducible: `n ≥ 1` and the only subspaces of
`ℂⁿ` invariant under every `ρ g` are `0` and `ℂⁿ`. -/
def IsIrreducibleRep {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  0 < n ∧ ∀ W : Submodule ℂ (Fin n → ℂ),
    (∀ g : G, ∀ v ∈ W, (ρ g : Matrix (Fin n) (Fin n) ℂ).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/-- The representations `ρ` and `σ` are equivalent: conjugate by an invertible matrix. -/
def IsEquivalentRep {G : Type*} [Group G] {n : ℕ}
    (ρ σ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup (Fin n) ℂ, ∀ g : G, σ g = P * ρ g * P⁻¹

/-- `G` has exactly one irreducible complex representation of each dimension `n ≥ 1`, up to
equivalence. -/
def HasUniqueIrreducibleRepOfEachDim (G : Type*) [Group G] : Prop :=
  ∀ n : ℕ, 0 < n →
    (∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ, IsIrreducibleRep ρ) ∧
    ∀ ρ σ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ,
      IsIrreducibleRep ρ → IsIrreducibleRep σ → IsEquivalentRep ρ σ

/-- Kourovka 16.58 (J. McKay): `SU₂(ℂ)` is the only group, up to isomorphism, that has exactly one
irreducible complex representation of dimension `n` for each `n = 1, 2, …`. -/
def su2OnlyGroupWithUniqueIrreducibleReps : Prop :=
  ∀ (G : Type) [Group G],
    HasUniqueIrreducibleRepOfEachDim G ↔ Nonempty (G ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ)

/--
Resolved false: the Kourovka Archive answers 16.58 "No, it is not": applying an automorphism `φ` of
`ℂ` to matrix entries gives irreducible 2-dimensional representations `x ↦ x^φ` of the abstract
group `SU₂(ℂ)`, infinitely many of them pairwise non-equivalent (von Neumann), so `SU₂(ℂ)` itself
does not have the property. It does have it if only unitary representations are counted, as these
are continuous (Cartan). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 16.58 (J. McKay); resolution: V. P. Burichenko, letter of 16 July 2013, as recorded in the
Kourovka Archive (observation of J. von Neumann), Kourovka Archive, Problem 16.58 (No: for field
automorphisms φ of ℂ the representations x ↦ x^φ of SU₂(ℂ) are irreducible and infinitely many are
pairwise non-equivalent, so SU₂(ℂ) itself lacks the property; it has it for unitary representations,
which are continuous by É. Cartan).
-/
public theorem_wanted su2OnlyGroupWithUniqueIrreducibleReps_refuted :
    ¬ su2OnlyGroupWithUniqueIrreducibleReps

end MathlibExt.GroupTheory.UniqueIrreducibleRepresentationsSU2Kourovka16Problem58Wanted
