/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Irreducible characters of equal degree of symmetric groups (Kourovka Notebook Problem 16.67)

Kourovka Notebook, Archive of Solved Problems, Problem 16.67 (A. Moretó): conjecture: given any
integer `k`, there exists an integer `n₀ = n₀(k)` such that if `n ≥ n₀` then the symmetric group of
degree `n` has at least `k` different ordinary irreducible characters of equal degrees.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.SymmetricGroupEqualCharacterDegreesKourovka16Problem67Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.67 (A.
Moretó). UnsolvedMath record UM-00701259 (`KOU-16.67`), dataset ulamai/UnsolvedMath v1.8.0.

Ordinary irreducible characters of `Sₙ` correspond to equivalence classes of irreducible complex
representations, and the degree is the dimension; so the target asks for `k` pairwise inequivalent
irreducible representations `Sₙ →* GL_d(ℂ)` of one dimension `d`, irreducibility and equivalence
being as in Problem 16.58.
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

/-- Kourovka 16.67 (A. Moretó), conjecture: for every `k` there is `n₀` such that for all
`n ≥ n₀` the symmetric group `Sₙ` has at least `k` distinct irreducible complex characters of the
same degree, i.e. `k` pairwise inequivalent irreducible representations of one dimension `d`. -/
def symmetricGroupManyCharactersOfEqualDegree : Prop :=
  ∀ k : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ (d : ℕ)
    (ρ : Fin k → (Equiv.Perm (Fin n) →* Matrix.GeneralLinearGroup (Fin d) ℂ)),
    (∀ i, IsIrreducibleRep (ρ i)) ∧ ∀ i j, i ≠ j → ¬ IsEquivalentRep (ρ i) (ρ j)

/--
Resolved true: Craven (Theorem 1.2) proves that the size of a largest set of irreducible characters
of `Sₙ` of one degree tends to infinity with `n`, which is the conjecture; it is the case `k = 1` of
his Theorem 1.1. The Kourovka Archive records 16.67 as proved. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.67 (A. Moretó); resolution: D. A.
Craven, Symmetric group character degrees and hook numbers, Proc. London Math. Soc. (3) 96 (2008),
26-50, arXiv:0709.0897, Theorem 1.2 (the size of a largest set of irreducible characters of S_n of
one degree tends to infinity), the case k = 1 of Theorem 1.1 (for any k and ℓ and all sufficiently
large n, S_n has k disjoint sets of ℓ irreducible characters, equal degrees within each set);
Kourovka Archive, Problem 16.67 (This is proved), https://arxiv.org/abs/0709.0897.
-/
public theorem_wanted symmetricGroupManyCharactersOfEqualDegree_holds :
    symmetricGroupManyCharactersOfEqualDegree

end MathlibExt.GroupTheory.SymmetricGroupEqualCharacterDegreesKourovka16Problem67Wanted
