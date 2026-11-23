/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mixed and torsion-free monsters of the second kind (Kourovka Notebook Problem 6.64)

Kourovka Notebook, Archive of Solved Problems, Problem 6.64 (V. P. Shunkov): a group G is a monster
of the second kind if it has elements of order > 2 and for any such element a and any proper
subgroup H there is an infinite set of conjugates of a by elements of G \ H such that ⟨a, c⟩ = G for
every c in it. Do mixed monsters (with elements of both finite and infinite orders) of the second
kind exist? Do there exist torsion-free monsters of the second kind?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.MonsterSecondKindExistenceKourovka6Problem64Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.64 (V. P.
Shunkov). UnsolvedMath record UM-00700406 (`KOU-6.64`), dataset ulamai/UnsolvedMath v1.8.0.

`IsMonsterSecondKind` follows the definition, with infinite order counted as order greater than `2`
(as `IsMonsterFirstKind` of the Kourovka 14.104 module does; otherwise torsion-free monsters could
not exist). The conjugates `g⁻¹ a g` with `g ∉ H` and `⟨a, g⁻¹ a g⟩ = G` form an infinite set. Mixed
means a non-trivial element of finite order and an element of infinite order. Torsion-free is
written `∀ g, g ≠ 1 → ¬ IsOfFinOrder g`.
-/

/-- `G` is a monster of the second kind (V. P. Shunkov): `G` has an element of order greater than
`2` (infinite order included, `orderOf a = 0`), and for every such `a` and every proper subgroup
`H` there are infinitely many conjugates `c = g⁻¹ a g`, `g ∉ H`, with `⟨a, c⟩ = G`. -/
def IsMonsterSecondKind (G : Type) [Group G] : Prop :=
  (∃ a : G, orderOf a ∉ ({1, 2} : Set ℕ)) ∧
    ∀ a : G, orderOf a ∉ ({1, 2} : Set ℕ) → ∀ H : Subgroup G, H ≠ ⊤ →
      {c : G | ∃ g ∉ H, c = g⁻¹ * a * g ∧ Subgroup.closure {a, c} = ⊤}.Infinite

/-- Kourovka 6.64(a) (V. P. Shunkov): there is a mixed monster of the second kind (with non-trivial
elements of finite order and elements of infinite order). -/
def existsMixedMonsterSecondKind : Prop :=
  ∃ (G : Type) (_ : Group G), IsMonsterSecondKind G ∧ (∃ x : G, x ≠ 1 ∧ IsOfFinOrder x) ∧
    ∃ y : G, ¬ IsOfFinOrder y

/-- Kourovka 6.64(b) (V. P. Shunkov): there is a torsion-free monster of the second kind. -/
def existsTorsionFreeMonsterSecondKind : Prop :=
  ∃ (G : Type) (_ : Group G), IsMonsterSecondKind G ∧ ∀ x : G, x ≠ 1 → ¬ IsOfFinOrder x

/--
Resolved true: the Kourovka Archive answers 6.64 "Yes, such monsters exist, in both cases", citing
Olshanskii's book (1991); in particular some monster of the second kind has non-trivial elements of
finite order and elements of infinite order. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 6.64 (V. P. Shunkov); resolution: A. Yu. Olshanskii, The
geometry of defining relations in groups, Kluwer, Dordrecht, 1991, Kourovka Archive, Problem 6.64:
Yes, such monsters exist, in both cases (Olshanskii), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted existsMixedMonsterSecondKind_holds : existsMixedMonsterSecondKind

/--
Resolved true: the Kourovka Archive answers 6.64 "Yes, such monsters exist, in both cases", citing
Olshanskii's book (1991); in particular some monster of the second kind is torsion-free. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.64 (V. P. Shunkov);
resolution: A. Yu. Olshanskii, The geometry of defining relations in groups, Kluwer, Dordrecht,
1991, Kourovka Archive, Problem 6.64: Yes, such monsters exist, in both cases (Olshanskii),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted existsTorsionFreeMonsterSecondKind_holds : existsTorsionFreeMonsterSecondKind

end MathlibExt.GroupTheory.MonsterSecondKindExistenceKourovka6Problem64Wanted
