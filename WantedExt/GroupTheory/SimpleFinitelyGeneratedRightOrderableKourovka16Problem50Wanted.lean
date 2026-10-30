/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated simple right-orderable groups (Kourovka Notebook Problem 16.50)

Kourovka Notebook, Archive of Solved Problems, Problem 16.50 (V. M. Kopytov, N. Ya. Medvedev): do
there exist simple finitely generated right-orderable groups? (Bergman: there are finitely generated
right-orderable groups equal to their derived subgroup.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleFinitelyGeneratedRightOrderableKourovka16Problem50Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.50 (V. M.
Kopytov, N. Ya. Medvedev). UnsolvedMath record UM-00701242 (`KOU-16.50`), dataset
ulamai/UnsolvedMath v1.8.0.

Right-orderable as in Problem 16.48 (a linear order invariant under right multiplication); simple is
`IsSimpleGroup`, which excludes the trivial group.
-/

/-- The right orders of `G`: linear orders (as relations) invariant under right multiplication. -/
def rightOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (a * c) (b * c)}

/-- Kourovka 16.50 (V. M. Kopytov, N. Ya. Medvedev): there is a finitely generated simple
right-orderable group. -/
def existsSimpleFGRightOrderable : Prop :=
  ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ Group.FG G ∧ (rightOrders G).Nonempty

/--
Resolved true: Hyde and Lodha (Theorem 1.3) construct finitely generated simple groups of
orientation-preserving homeomorphisms of the real line, which are finitely generated simple left (or
right) orderable groups (Corollary 1.5 and the abstract). The Kourovka Archive answers 16.50 "Yes,
such groups do exist". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 16.50 (V. M. Kopytov, N. Ya. Medvedev); resolution: J. Hyde and Y. Lodha, Finitely generated
infinite simple groups of homeomorphisms of the real line, Invent. Math. 218 (2019), 83-112,
arXiv:1807.06478, Theorem 1.3 (G_ρ is a finitely generated simple subgroup of Homeo+(ℝ)) and
Corollary 1.5 (finitely generated simple left orderable groups exist; by the abstract, equivalently
left or right orderable); Kourovka Archive, Problem 16.50 (Yes, such groups do exist),
https://arxiv.org/abs/1807.06478.
-/
public theorem_wanted existsSimpleFGRightOrderable_holds : existsSimpleFGRightOrderable

end MathlibExt.GroupTheory.SimpleFinitelyGeneratedRightOrderableKourovka16Problem50Wanted
