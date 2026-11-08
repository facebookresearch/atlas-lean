/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Order dimension of subgroup lattices of Chernikov groups (Kourovka Notebook Problem 11.116)

Kourovka Notebook, Problem 11.116 (L. N. Shevrin): for any Chernikov group that does not contain a
direct product of two quasicyclic groups over the same prime, does the subgroup lattice have finite
dimension (the least number of linear orders whose intersection is the order)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.116 (L. N. Shevrin). UnsolvedMath record
UM-00700808 (`KOU-11.116`), dataset ulamai/UnsolvedMath v1.8.0.

A quasicyclic group is an infinite abelian group all of whose proper subgroups are finite (this
characterizes the Prüfer groups `C_{p^∞}`). A Chernikov group has a normal subgroup of finite index
isomorphic to a finite direct product of quasicyclic groups; finite groups are the case of zero
factors. "Contains a direct product of two quasicyclic groups over the same prime" is read as an
embedding of `Q × Q` for a quasicyclic `Q`, since quasicyclic groups over one prime are isomorphic.
Finite dimension means the subgroup order is the intersection of finitely many linear orders on
`Subgroup G` (Dushnik-Miller dimension).
-/

/-- A quasicyclic group (a Prüfer group `C_{p^∞}` for some prime `p`): an infinite abelian group
all of whose proper subgroups are finite. -/
def IsQuasicyclic (Q : Type*) [Group Q] : Prop :=
  (∀ a b : Q, a * b = b * a) ∧ Infinite Q ∧ ∀ K : Subgroup Q, K ≠ ⊤ → (K : Set Q).Finite

/-- A Chernikov group: a finite extension of a direct product of finitely many quasicyclic groups,
i.e. a group with a normal subgroup of finite index isomorphic to `Q₁ × ⋯ × Q_r`, each `Qᵢ`
quasicyclic (`r = 0` is allowed, so finite groups are Chernikov groups). -/
def IsChernikov (G : Type*) [Group G] : Prop :=
  ∃ D : Subgroup G, D.Normal ∧ D.FiniteIndex ∧
    ∃ (r : ℕ) (Q : Fin r → Type) (_ : ∀ i, Group (Q i)),
      (∀ i, IsQuasicyclic (Q i)) ∧ Nonempty (D ≃* ((i : Fin r) → Q i))

/-- `G` contains a direct product of two quasicyclic groups over the same prime: `Q × Q` embeds in
`G` for some quasicyclic group `Q` (quasicyclic groups over the same prime are isomorphic). -/
def ContainsQuasicyclicSquare (G : Type*) [Group G] : Prop :=
  ∃ (Q : Type) (_ : Group Q), IsQuasicyclic Q ∧ ∃ f : Q × Q →* G, Function.Injective f

/-- A partially ordered set has finite (order) dimension: its order relation is the intersection
of finitely many linear orders on the same set. -/
def HasFiniteOrderDimension (P : Type*) [PartialOrder P] : Prop :=
  ∃ (n : ℕ) (L : Fin n → LinearOrder P), ∀ x y : P, x ≤ y ↔ ∀ i, (L i).le x y

/-- Kourovka 11.116 (L. N. Shevrin): for every Chernikov group that does not contain a direct
product of two quasicyclic groups over the same prime, the lattice of subgroups has finite
dimension. -/
def chernikovSubgroupLatticeFiniteDimension : Prop :=
  ∀ (G : Type) [Group G], IsChernikov G → ¬ ContainsQuasicyclicSquare G →
    HasFiniteOrderDimension (Subgroup G)

/--
Resolved true: if `G` has a normal subgroup `D` of index `m` with `D ≅ C_{p₁^∞} × ⋯ × C_{p_r^∞}` for
distinct primes (which the excluded configuration forces), Kinyon and Urban embed the subgroup
lattice of `G` into a product of `2rm` chains (fibres of `H` over the cosets of `D`, each a coset of
`H ∩ D`, coded by base-`p` digit intervals), so its dimension is at most `2rm`; finite groups have
finite subgroup lattices. The Kourovka Notebook (21st issue) marks 11.116 solved, "Yes, it is true"
(AI solution confirmed by P. Shumyatsky). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
11.116 (L. N. Shevrin); resolution: M. Kinyon and J. Urban (with Codex gpt-6-astra), Results on
problems from the Kourovka Notebook, preprint, version 4 (19 September 2026), Section 3.9: if `D ⊴
G` has index `m` and `D = C_{p₁^∞} × ⋯ × C_{p_r^∞}` with distinct primes, the subgroup lattice of
`G` embeds in a product of `2rm` chains, so its order dimension is at most `2rm`; the Kourovka
Notebook (21st issue) marks 11.116 solved (AI solution confirmed by P. Shumyatsky),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted chernikovSubgroupLatticeFiniteDimension_holds :
    chernikovSubgroupLatticeFiniteDimension

end MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted
