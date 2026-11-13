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

/-- **Centralizer subgroups.** A subgroup $H$ of a group $G$ is a centralizer if $H = C_G(X)$ for
some subset $X \subseteq G$, where $C_G(X)$ is the subgroup of elements of $G$ that commute with
every element of $X$. -/
def IsCentralizer {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ X : Set G, H = Subgroup.centralizer X

/-- **Modularity of centralizer sublattices (Kourovka 11.4).** Call a subgroup of a group $G$ a
centralizer if it equals $C_G(X)$ for some subset $X \subseteq G$. This is the proposition that for
every group $G$ in which the join (in the subgroup lattice) of any two centralizers is again a
centralizer, any three centralizers $A$, $B$, $C$ of $G$ with $A \le C$ satisfy the modular law
$(A \sqcup B) \sqcap C = A \sqcup (B \sqcap C)$, where $\sqcup$ and $\sqcap$ are the join and meet
in the subgroup lattice of $G$.

Centralizers are always closed under intersection, so the hypothesis says that they form a
sublattice of the subgroup lattice. The question is due to V. A. Antonov. -/
def centralizerSublatticeModular : Prop :=
  ∀ (G : Type) [Group G],
    (∀ A B : Subgroup G, IsCentralizer A → IsCentralizer B → IsCentralizer (A ⊔ B)) →
    ∀ A B C : Subgroup G, IsCentralizer A → IsCentralizer B → IsCentralizer C → A ≤ C →
      (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C)

/-- **Lattices of centralizers need not be modular (Kourovka 11.4).** Call a subgroup of a group
$G$ a centralizer if it equals $C_G(X)$ for some subset $X \subseteq G$. Modularity of centralizer
sublattices fails: there is a group $G$ in which the join (in the subgroup lattice) of any two
centralizers is again a centralizer, but which has centralizers $A$, $B$, $C$ with $A \le C$ and
$(A \sqcup B) \sqcap C \ne A \sqcup (B \sqcap C)$, where $\sqcup$ and $\sqcap$ are the join and meet
in the subgroup lattice of $G$.

The Kourovka Archive answers 11.4 "No, not always" (Obraztsov); for finite groups the answer is
yes.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 11.4 (V. A. Antonov); resolution: V. N. Obraztsov, J. Algebra 199, no. 1 (1998),
337-343, Kourovka Archive, Problem 11.4: "No, not always", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted centralizerSublatticeModular_refuted : ¬ centralizerSublatticeModular

end MathlibExt.GroupTheory.CentralizerLatticeModularKourovka11Problem4Wanted
