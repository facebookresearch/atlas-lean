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

/-- **Irreducible representations into $\mathrm{GL}_n(\mathbb{C})$.** Let $G$ be a group and
$\rho \colon G \to \mathrm{GL}_n(\mathbb{C})$ a homomorphism. Then $\rho$ is irreducible when
$n \ge 1$ and the only subspaces $W$ of $\mathbb{C}^n$ with $\rho(g)v \in W$ for all $g \in G$ and
$v \in W$ are $0$ and $\mathbb{C}^n$. -/
def IsIrreducibleRep {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  0 < n ∧ ∀ W : Submodule ℂ (Fin n → ℂ),
    (∀ g : G, ∀ v ∈ W, (ρ g : Matrix (Fin n) (Fin n) ℂ).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/-- **Equivalent representations into $\mathrm{GL}_n(\mathbb{C})$.** Let $G$ be a group. Two
homomorphisms $\rho, \sigma \colon G \to \mathrm{GL}_n(\mathbb{C})$ are equivalent when there is a
matrix $P \in \mathrm{GL}_n(\mathbb{C})$ with $\sigma(g) = P \rho(g) P^{-1}$ for all $g \in G$. -/
def IsEquivalentRep {G : Type*} [Group G] {n : ℕ}
    (ρ σ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup (Fin n) ℂ, ∀ g : G, σ g = P * ρ g * P⁻¹

/-- **Groups with exactly one irreducible representation of each dimension.** A group $G$ has
exactly one irreducible complex representation of each dimension when for every $n \ge 1$ there
is an irreducible homomorphism $G \to \mathrm{GL}_n(\mathbb{C})$ and any two irreducible
homomorphisms $G \to \mathrm{GL}_n(\mathbb{C})$ are equivalent. Representations are arbitrary
homomorphisms of the abstract group $G$; no continuity is required. -/
def HasUniqueIrreducibleRepOfEachDim (G : Type*) [Group G] : Prop :=
  ∀ n : ℕ, 0 < n →
    (∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ, IsIrreducibleRep ρ) ∧
    ∀ ρ σ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ,
      IsIrreducibleRep ρ → IsIrreducibleRep σ → IsEquivalentRep ρ σ

/-- **McKay's question on $\mathrm{SU}_2(\mathbb{C})$ (Kourovka 16.58).** A group $G$ has exactly
one irreducible complex representation of each dimension $n = 1, 2, \dots$, up to equivalence, if
and only if $G$ is isomorphic to $\mathrm{SU}_2(\mathbb{C})$. Here a representation of dimension
$n$ is any homomorphism $G \to \mathrm{GL}_n(\mathbb{C})$ of abstract groups, with no continuity
required. -/
def su2OnlyGroupWithUniqueIrreducibleReps : Prop :=
  ∀ (G : Type) [Group G],
    HasUniqueIrreducibleRepOfEachDim G ↔ Nonempty (G ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ)

/-- **McKay's question 16.58 has a negative answer.** It is not the case that a group has exactly
one irreducible complex representation of each dimension $n \ge 1$, up to equivalence, if and only
if it is isomorphic to $\mathrm{SU}_2(\mathbb{C})$. Here a representation of dimension $n$ is any
homomorphism to $\mathrm{GL}_n(\mathbb{C})$ of abstract groups, with no continuity required.

Applying a field automorphism $\varphi$ of $\mathbb{C}$ to matrix entries gives irreducible
$2$-dimensional representations $x \mapsto x^\varphi$ of the abstract group
$\mathrm{SU}_2(\mathbb{C})$, infinitely many of them pairwise non-equivalent (von Neumann), so
$\mathrm{SU}_2(\mathbb{C})$ itself lacks the property. It does have it if only unitary
representations are counted, as these are continuous (Cartan).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
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
