/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite modular lattices and the lattice of formations (Kourovka Notebook Problem 13.51)

Kourovka Notebook, Problem 13.51 (A. N. Skiba): is every finite modular lattice embeddable in the
lattice of formations of finite groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.ModularLattice

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 13.51 (A. N. Skiba). UnsolvedMath record
UM-00700969 (`KOU-13.51`), dataset ulamai/UnsolvedMath v1.8.0.

A class of finite groups is a predicate on finite groups in `Type`; a formation is closed under
homomorphic images and finite subdirect products (`G / N₁, G / N₂ ∈ 𝔉 → G / (N₁ ∩ N₂) ∈ 𝔉`), and the
empty class counts as a formation, as in the resolving preprint. Meets are intersections and joins
are generated formations. An embedding is an injective map preserving binary meets and joins;
preservation of the least or greatest element is not required. Allowing the empty formation makes
the refuted statement weaker, since the nonempty formations form a sublattice.
-/

/-- **Class of finite groups (Kourovka 13.51).** A class of finite groups is a property of finite
groups: for each finite group $G$ it states whether $G$ belongs to the class.

Closure under isomorphism is not part of the definition. -/
abbrev FiniteGroupClass : Type 1 := ∀ (G : Type) [Group G] [Finite G], Prop

/-- **Formation of finite groups (Kourovka 13.51).** A class $\mathfrak F$ of finite groups is a
formation when it is closed under homomorphic images (if $G \in \mathfrak F$ and $\varphi : G
\to H$ is a surjective homomorphism of finite groups, then $H \in \mathfrak F$) and, for every
finite group $G$ and normal subgroups $N_1$ and $N_2$ of $G$, $G/N_1 \in \mathfrak F$ and $G/N_2
\in \mathfrak F$ imply $G/(N_1 \cap N_2) \in \mathfrak F$ (closure under finite subdirect
products).

The empty class is a formation. -/
def IsFormation (𝔉 : FiniteGroupClass) : Prop :=
  (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H] (φ : G →* H),
      Function.Surjective φ → 𝔉 G → 𝔉 H) ∧
    ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
      𝔉 (G ⧸ N₁) → 𝔉 (G ⧸ N₂) → 𝔉 (G ⧸ (N₁ ⊓ N₂))

/-- **Intersection of classes of finite groups.** For classes $\mathfrak F_1$ and $\mathfrak F_2$ of
finite groups, their intersection $\mathfrak F_1 \cap \mathfrak F_2$ is the class of finite
groups $G$ with $G \in \mathfrak F_1$ and $G \in \mathfrak F_2$. For formations $\mathfrak F_1$
and $\mathfrak F_2$ it is their meet in the lattice of formations. -/
def classMeet (𝔉₁ 𝔉₂ : FiniteGroupClass) : FiniteGroupClass :=
  fun G _ _ => 𝔉₁ G ∧ 𝔉₂ G

/-- **Join of formations (Kourovka 13.51).** For classes $\mathfrak F_1$ and $\mathfrak F_2$ of
finite groups, their formation join is the class of finite groups $G$ that belong to every
formation containing all groups of $\mathfrak F_1$ and of $\mathfrak F_2$: the intersection of
all formations containing $\mathfrak F_1 \cup \mathfrak F_2$, which is the smallest such
formation. For formations $\mathfrak F_1$ and $\mathfrak F_2$ it is their join in the lattice of
formations. -/
def formationJoin (𝔉₁ 𝔉₂ : FiniteGroupClass) : FiniteGroupClass :=
  fun G _ _ => ∀ 𝔉 : FiniteGroupClass, IsFormation 𝔉 →
    (∀ (H : Type) [Group H] [Finite H], 𝔉₁ H ∨ 𝔉₂ H → 𝔉 H) → 𝔉 G

/-- **Kourovka Problem 13.51 (Skiba): finite modular lattices embed in the lattice of formations.**
For every finite modular lattice $L$ there is an injective map $f$ from $L$ to the formations of
finite groups such that, for all $a, b \in L$, $f(a \wedge b) = f(a) \cap f(b)$ and $f(a \vee
b)$ is the smallest formation containing $f(a) \cup f(b)$.

The map is not required to preserve the least or the greatest element. -/
def finiteModularLatticeEmbedsInFormations : Prop :=
  ∀ (L : Type) [Lattice L] [IsModularLattice L] [Finite L],
    ∃ f : L → FiniteGroupClass, (∀ a, IsFormation (f a)) ∧ Function.Injective f ∧
      (∀ a b, f (a ⊓ b) = classMeet (f a) (f b)) ∧ ∀ a b, f (a ⊔ b) = formationJoin (f a) (f b)

/--
**Not every finite modular lattice embeds in the lattice of formations.** There is a finite modular
lattice $L$ that admits no injective map $f$ from $L$ to the formations of finite groups such that,
for all $a, b \in L$, $f(a \wedge b) = f(a) \cap f(b)$ and $f(a \vee b)$ is the smallest formation
containing $f(a) \cup f(b)$. This answers Kourovka Problem 13.51 (Skiba) in the negative.

Jayadevan constructs a modular lattice with 184 elements that admits no such map (a six-variable
Desargues implication holds for formations and fails in the lattice); the Kourovka Notebook (21st
issue) answers 13.51 "No, not every" (AI solution confirmed by A. N. Skiba).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 13.51 (A. N. Skiba); resolution: A.
Jayadevan, A finite modular lattice not embeddable in the lattice of formations of finite groups,
preprint, Zenodo record 22863019 (2026), main theorem: a modular lattice with 184 elements (the dual
of an incidence lattice with 91 points and 91 lines) admits no injective map preserving binary meets
and joins into the lattice of formations; the Kourovka Notebook (21st issue) marks 13.51 solved (AI
solution confirmed by A. N. Skiba), https://zenodo.org/records/22863019.
-/
public theorem_wanted finiteModularLatticeEmbedsInFormations_refuted :
    ¬ finiteModularLatticeEmbedsInFormations

end MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
