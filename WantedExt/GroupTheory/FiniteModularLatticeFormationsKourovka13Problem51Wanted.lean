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

/-- A class of finite groups, as a predicate on finite groups in `Type`. -/
abbrev FiniteGroupClass : Type 1 := ∀ (G : Type) [Group G] [Finite G], Prop

/-- `𝔉` is a formation of finite groups: it is closed under homomorphic images, and
`G / N₁, G / N₂ ∈ 𝔉` implies `G / (N₁ ∩ N₂) ∈ 𝔉` (closure under finite subdirect products). The
empty class is a formation. -/
def IsFormation (𝔉 : FiniteGroupClass) : Prop :=
  (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H] (φ : G →* H),
      Function.Surjective φ → 𝔉 G → 𝔉 H) ∧
    ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
      𝔉 (G ⧸ N₁) → 𝔉 (G ⧸ N₂) → 𝔉 (G ⧸ (N₁ ⊓ N₂))

/-- The intersection of two classes: the meet in the lattice of formations. -/
def classMeet (𝔉₁ 𝔉₂ : FiniteGroupClass) : FiniteGroupClass :=
  fun G _ _ => 𝔉₁ G ∧ 𝔉₂ G

/-- The smallest formation containing `𝔉₁ ∪ 𝔉₂`: the join in the lattice of formations. -/
def formationJoin (𝔉₁ 𝔉₂ : FiniteGroupClass) : FiniteGroupClass :=
  fun G _ _ => ∀ 𝔉 : FiniteGroupClass, IsFormation 𝔉 →
    (∀ (H : Type) [Group H] [Finite H], 𝔉₁ H ∨ 𝔉₂ H → 𝔉 H) → 𝔉 G

/-- Kourovka 13.51 (A. N. Skiba): every finite modular lattice `L` embeds in the lattice of
formations of finite groups: there is an injective map from `L` to formations preserving binary
meets and joins. -/
def finiteModularLatticeEmbedsInFormations : Prop :=
  ∀ (L : Type) [Lattice L] [IsModularLattice L] [Finite L],
    ∃ f : L → FiniteGroupClass, (∀ a, IsFormation (f a)) ∧ Function.Injective f ∧
      (∀ a b, f (a ⊓ b) = classMeet (f a) (f b)) ∧ ∀ a b, f (a ⊔ b) = formationJoin (f a) (f b)

/--
Resolved false: Jayadevan constructs a modular lattice with 184 elements that admits no injective
map preserving binary meets and joins into the lattice of formations of finite groups (a
six-variable Desargues implication holds for formations and fails in the lattice); the Kourovka
Notebook (21st issue) answers 13.51 "No, not every" (AI solution confirmed by A. N. Skiba). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 13.51 (A. N. Skiba); resolution: A. Jayadevan, A
finite modular lattice not embeddable in the lattice of formations of finite groups, preprint,
Zenodo record 22863019 (2026), main theorem: a modular lattice with 184 elements (the dual of an
incidence lattice with 91 points and 91 lines) admits no injective map preserving binary meets and
joins into the lattice of formations; the Kourovka Notebook (21st issue) marks 13.51 solved (AI
solution confirmed by A. N. Skiba), https://zenodo.org/records/22863019.
-/
public theorem_wanted finiteModularLatticeEmbedsInFormations_refuted :
    ¬ finiteModularLatticeEmbedsInFormations

end MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
