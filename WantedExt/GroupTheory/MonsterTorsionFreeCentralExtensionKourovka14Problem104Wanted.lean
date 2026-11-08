/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion-free central extensions of monsters (Kourovka Notebook Problem 14.104)

Kourovka Notebook, Archive of Solved Problems, Problem 14.104 (V. P. Shunkov): an infinite group `G`
is a monster of the first kind if it has elements of order `> 2` and for any such element `a` and
any proper subgroup `H` there is `g ∈ G \ H` with `⟨a, a^g⟩ = G`. Is every monster of the first kind
the quotient of a torsion-free group by a central cyclic subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.MonsterTorsionFreeCentralExtensionKourovka14Problem104Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.104 (V. P.
Shunkov). UnsolvedMath record UM-00701088 (`KOU-14.104`), dataset ulamai/UnsolvedMath v1.8.0.

Elements of infinite order count as having order `> 2` (`orderOf a = 0` in Mathlib); the monsters
relevant to the resolution (infinite groups all of whose proper subgroups are finite, Archive 6.63)
are periodic, so this choice does not affect them. "Central extension of a cyclic group by `M`" is a
group `E` with a central cyclic subgroup `C` and `E / C ≅ M`.
-/

/-- `G` is a monster of the first kind (V. P. Shunkov): `G` is infinite, has an element of order
greater than `2`, and for every such element `a` and every proper subgroup `H` there is `g ∉ H`
with `⟨a, g⁻¹ a g⟩ = G`. An element of infinite order (`orderOf a = 0`) counts as having order
greater than `2`. -/
def IsMonsterFirstKind (G : Type*) [Group G] : Prop :=
  Infinite G ∧ (∃ a : G, orderOf a ∉ ({1, 2} : Set ℕ)) ∧
    ∀ a : G, orderOf a ∉ ({1, 2} : Set ℕ) → ∀ H : Subgroup G, H ≠ ⊤ →
      ∃ g ∉ H, Subgroup.closure {a, g⁻¹ * a * g} = ⊤

/-- Kourovka 14.104 (V. P. Shunkov): for every monster of the first kind `M` there is a
torsion-free group `E` with a central cyclic subgroup `C` such that `E / C ≅ M`. -/
def monsterHasTorsionFreeCyclicCentralExtension : Prop :=
  ∀ (M : Type) [Group M], IsMonsterFirstKind M →
    ∃ (E : Type) (_ : Group E) (C : Subgroup E), (∀ x : E, x ≠ 1 → ¬ IsOfFinOrder x) ∧
      C ≤ Subgroup.center E ∧ IsCyclic C ∧ ∃ _ : C.Normal, Nonempty (E ⧸ C ≃* M)

/--
Resolved false: the Kourovka Archive answers 14.104 "No, not always" (Sozutov): if a torsion-free
`E` has a central cyclic `C` with `E / C ≅ M`, every finite subgroup of `M` is cyclic, and some
monsters of the first kind have non-cyclic finite subgroups. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 14.104 (V. P. Shunkov); resolution: A. I. Sozutov,
letter of 20 November 2001, Kourovka Archive, Problem 14.104: such an extension forces every finite
subgroup of the monster to be cyclic, which fails for some monsters (answer: No, not always).
-/
public theorem_wanted monsterHasTorsionFreeCyclicCentralExtension_refuted :
    ¬ monsterHasTorsionFreeCyclicCentralExtension

end MathlibExt.GroupTheory.MonsterTorsionFreeCentralExtensionKourovka14Problem104Wanted
