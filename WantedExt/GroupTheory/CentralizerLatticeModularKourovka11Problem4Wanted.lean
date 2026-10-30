/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Modularity of the lattice of centralizers (Kourovka Notebook Problem 11.4)

Kourovka Notebook, Archive of Solved Problems, Problem 11.4 (V. A. Antonov): is the lattice of
centralizers in a group modular if it is a sublattice of the lattice of all subgroups? (True for
finite groups.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.CentralizerLatticeModularKourovka11Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.4 (V. A.
Antonov). UnsolvedMath record UM-00700697 (`KOU-11.4`), dataset ulamai/UnsolvedMath v1.8.0.

Centralizers are the subgroups `C_G(X)`, `X ⊆ G`. They are always closed under intersection (`C(X) ∩
C(Y) = C(X ∪ Y)`), so being a sublattice of the subgroup lattice means being closed under the
subgroup join. Modularity is the modular law `A ≤ C → (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C)` for centralizers
`A`, `B`, `C`, with the lattice operations of the subgroup lattice.
-/

/-- `H` is a centralizer in `G`: `H = C_G(X)` for some subset `X ⊆ G`. -/
def IsCentralizer {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ X : Set G, H = Subgroup.centralizer X

/-- Kourovka 11.4 (V. A. Antonov): if the centralizers of a group `G` form a sublattice of the
subgroup lattice (they are always closed under `⊓`; here also under `⊔`), then this lattice of
centralizers is modular. -/
def centralizerSublatticeModular : Prop :=
  ∀ (G : Type) [Group G],
    (∀ A B : Subgroup G, IsCentralizer A → IsCentralizer B → IsCentralizer (A ⊔ B)) →
    ∀ A B C : Subgroup G, IsCentralizer A → IsCentralizer B → IsCentralizer C → A ≤ C →
      (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C)

/--
Resolved false: the Kourovka Archive answers 11.4 "No, not always" (Obraztsov): some group has its
centralizers closed under the subgroup join while the modular law fails for three of them (for
finite groups the answer is yes). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 11.4 (V. A. Antonov); resolution: V. N. Obraztsov, J. Algebra 199, no. 1 (1998),
337-343, Kourovka Archive, Problem 11.4: "No, not always", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted centralizerSublatticeModular_refuted : ¬ centralizerSublatticeModular

end MathlibExt.GroupTheory.CentralizerLatticeModularKourovka11Problem4Wanted
