/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hereditarily just infinite groups: torsion and linearity (Kourovka Notebook Problem 15.18)

Kourovka Notebook, Archive of Solved Problems, Problem 15.18 (L. Bartholdi, R. I. Grigorchuk, Z.
Šunić): a group is hereditarily just infinite if it is residually finite and all of its non-trivial
normal subgroups are just infinite. (a) Do there exist finitely generated hereditarily just infinite
torsion groups? (b) Is every finitely generated hereditarily just infinite group necessarily linear?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.HereditarilyJustInfiniteGroupsKourovka15Problem18Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.18 (L.
Bartholdi, R. I. Grigorchuk, Z. Šunić). UnsolvedMath record UM-00701106 (`KOU-15.18`), dataset
ulamai/UnsolvedMath v1.8.0.

The definition is the notebook's with `G` infinite added: read literally, the trivial group
qualifies vacuously (it has no nontrivial normal subgroups), while for a nontrivial group `G` itself
is a nontrivial normal subgroup and so is just infinite. The usual definition (every subgroup of
finite index is just infinite) implies this one. Linear means a faithful representation in `GLₙ(K)`
for a field `K : Type`; a finitely generated linear group needs only a countable field.
-/

/-- **Just infinite groups.** A group $G$ is just infinite if it is infinite and every nontrivial
normal subgroup of $G$ has finite index in $G$. -/
def IsJustInfinite (G : Type*) [Group G] : Prop :=
  Infinite G ∧ ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N.FiniteIndex

/-- **Residually finite groups.** A group $G$ is residually finite if every element $g \ne 1$ of
$G$ lies outside some normal subgroup of finite index in $G$. -/
def IsResiduallyFinite (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ g ∉ N

/-- **Hereditarily just infinite groups.** A group $G$ is hereditarily just infinite (in the
sense of Kourovka 15.18) if it is infinite, residually finite, and every nontrivial normal
subgroup of $G$, viewed as a group in its own right, is just infinite. -/
def IsHereditarilyJustInfinite (G : Type*) [Group G] : Prop :=
  Infinite G ∧ IsResiduallyFinite G ∧ ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → IsJustInfinite N

/-- **Kourovka 15.18(a): hereditarily just infinite torsion groups.** The proposition that there
exists a finitely generated hereditarily just infinite group $G$ that is a torsion group, i.e.
every element of $G$ has finite order. -/
def fgHereditarilyJustInfiniteTorsionGroup : Prop :=
  ∃ (G : Type) (_ : Group G), Group.FG G ∧ IsHereditarilyJustInfinite G ∧ ∀ g : G, IsOfFinOrder g

/-- **Kourovka 15.18(b): linearity of hereditarily just infinite groups.** The proposition that
every finitely generated hereditarily just infinite group $G$ is linear, i.e. that there are a
field $K$, a natural number $n$ and an injective group homomorphism $G \to \mathrm{GL}_n(K)$. -/
def fgHereditarilyJustInfiniteIsLinear : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → IsHereditarilyJustInfinite G →
    ∃ (K : Type) (_ : Field K) (n : ℕ) (ρ : G →* Matrix.GeneralLinearGroup (Fin n) K),
      Function.Injective ρ

/--
**Finitely generated hereditarily just infinite torsion groups exist.** There is a finitely
generated hereditarily just infinite group $G$ in which every element has finite order.

This answers Kourovka 15.18(a) positively, as recorded in the Kourovka Archive ("Yes, such groups
exist"; Ershov and Jaikin-Zapirain).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.18 (L.
Bartholdi, R. I. Grigorchuk, Z. Šunić); resolution: M. Ershov and A. Jaikin-Zapirain, Groups of
positive weighted deficiency and their applications, J. Reine Angew. Math. 677 (2013), 71-134,
arXiv:1007.1489, Kourovka Archive, Problem 15.18 ((a) Yes, such groups exist; (b) No, not every);
the abstract constructs finitely generated residually finite p-torsion groups and shows that every
group of positive weighted deficiency has a hereditarily just infinite quotient,
https://arxiv.org/abs/1007.1489.
-/
public theorem_wanted fgHereditarilyJustInfiniteTorsionGroup_holds :
    fgHereditarilyJustInfiniteTorsionGroup

/--
**Not every finitely generated hereditarily just infinite group is linear.** There is a finitely
generated hereditarily just infinite group $G$ such that for no field $K$ and no natural number
$n$ is there an injective group homomorphism $G \to \mathrm{GL}_n(K)$.

This answers Kourovka 15.18(b) negatively, as recorded in the Kourovka Archive ("No, not every";
Ershov and Jaikin-Zapirain). As the problem notes, a positive answer to (b) would contradict (a):
a finitely generated linear torsion group is finite, while a just infinite group is infinite.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.18 (L.
Bartholdi, R. I. Grigorchuk, Z. Šunić); resolution: M. Ershov and A. Jaikin-Zapirain, Groups of
positive weighted deficiency and their applications, J. Reine Angew. Math. 677 (2013), 71-134,
arXiv:1007.1489, Kourovka Archive, Problem 15.18 ((a) Yes, such groups exist; (b) No, not every);
the abstract constructs finitely generated residually finite p-torsion groups and shows that every
group of positive weighted deficiency has a hereditarily just infinite quotient,
https://arxiv.org/abs/1007.1489.
-/
public theorem_wanted fgHereditarilyJustInfiniteIsLinear_refuted :
    ¬ fgHereditarilyJustInfiniteIsLinear

end MathlibExt.GroupTheory.HereditarilyJustInfiniteGroupsKourovka15Problem18Wanted
