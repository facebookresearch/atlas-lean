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

/-- **Irreducible complex matrix representations (Kourovka 16.67).** Let $G$ be a group and $n$ a
natural number. A homomorphism $\rho \colon G \to \mathrm{GL}_n(\mathbb{C})$ is irreducible when
$n \ge 1$ and every subspace $W$ of $\mathbb{C}^n$ such that $\rho(g) v \in W$ for all $g \in G$
and all $v \in W$ is either $0$ or $\mathbb{C}^n$. -/
def IsIrreducibleRep {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  0 < n ∧ ∀ W : Submodule ℂ (Fin n → ℂ),
    (∀ g : G, ∀ v ∈ W, (ρ g : Matrix (Fin n) (Fin n) ℂ).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/-- **Equivalent complex matrix representations (Kourovka 16.67).** Let $G$ be a group and $n$ a
natural number. Two homomorphisms $\rho, \sigma \colon G \to \mathrm{GL}_n(\mathbb{C})$ are
equivalent when there is a single invertible matrix $P \in \mathrm{GL}_n(\mathbb{C})$ with
$\sigma(g) = P \rho(g) P^{-1}$ for every $g \in G$. -/
def IsEquivalentRep {G : Type*} [Group G] {n : ℕ}
    (ρ σ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup (Fin n) ℂ, ∀ g : G, σ g = P * ρ g * P⁻¹

/-- **Moretó's conjecture on equal character degrees of symmetric groups.** For every natural
number $k$ there is a natural number $n_0$ such that for every $n \ge n_0$ there are a natural
number $d$ and irreducible representations $\rho_1, \dots, \rho_k$ of the symmetric group $S_n$
into $\mathrm{GL}_d(\mathbb{C})$ that are pairwise inequivalent: $\rho_i$ and $\rho_j$ are not
equivalent whenever $i \ne j$.

Since irreducible complex characters correspond to equivalence classes of irreducible complex
representations and the degree of a character is the dimension, this says that $S_n$ has at least
$k$ distinct irreducible complex characters of the same degree. -/
def symmetricGroupManyCharactersOfEqualDegree : Prop :=
  ∀ k : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ (d : ℕ)
    (ρ : Fin k → (Equiv.Perm (Fin n) →* Matrix.GeneralLinearGroup (Fin d) ℂ)),
    (∀ i, IsIrreducibleRep (ρ i)) ∧ ∀ i j, i ≠ j → ¬ IsEquivalentRep (ρ i) (ρ j)

/-- **Symmetric groups have many irreducible characters of equal degree.** Moretó's conjecture
holds: for every natural number $k$ there is a natural number $n_0$ such that for every
$n \ge n_0$ there are a natural number $d$ and irreducible representations
$\rho_1, \dots, \rho_k$ of the symmetric group $S_n$ into $\mathrm{GL}_d(\mathbb{C})$ that are
pairwise inequivalent.

Source: E. I. Khukhro and V. D.
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
