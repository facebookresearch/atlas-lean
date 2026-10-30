/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Covering Frattini and avoiding complemented chief factors (Kourovka Notebook Problem 19.38)

Kourovka Notebook, Problem 19.38 (S. F. Kamornikov), marked solved in the 21st issue: suppose that
`H` is a subgroup of a finite soluble group `G` that covers all Frattini chief factors of `G` and
avoids all complemented chief factors of `G`. Is it true that there are elements `x, y ∈ G` such
that `H ∩ H^x ∩ H^y = H_G`, the largest normal subgroup of `G` contained in `H`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.CoverAvoidIntersectionCoreKourovka19Problem38Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.38 (S. F. Kamornikov). UnsolvedMath
record UM-00701586 (`KOU-19.38`), dataset ulamai/UnsolvedMath v1.8.0.

A chief factor `A / B` consists of normal subgroups `B < A` with no normal subgroup strictly
between; it is Frattini when `A / B ≤ Φ(G / B)` (`A` lies in every maximal subgroup containing `B`)
and complemented when `M A = G`, `M ∩ A = B` for some subgroup `M`. `H` covers `A / B` when `A ≤ H
B` and avoids it when `H ∩ A ≤ B`; `H_G` is Mathlib's `Subgroup.normalCore`. `IsChiefFactor` is the
shared definition in `WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- A chief factor `A / B` is a Frattini chief factor: `A / B ≤ Φ(G / B)`, that is, `A` lies in
every maximal subgroup of `G` containing `B`. -/
def IsFrattiniChiefFactor {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  IsChiefFactor A B ∧ ∀ M : Subgroup G, IsCoatom M → B ≤ M → A ≤ M

/-- A chief factor `A / B` is complemented: some subgroup `M` has `M ⊔ A = G` and `M ⊓ A = B`. -/
def IsComplementedChiefFactor {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  IsChiefFactor A B ∧ ∃ M : Subgroup G, M ⊔ A = ⊤ ∧ M ⊓ A = B

/-- Kourovka 19.38 (S. F. Kamornikov): if a subgroup `H` of a finite soluble group `G` covers every
Frattini chief factor `A / B` (`A ≤ H B`) and avoids every complemented chief factor (`H ∩ A ≤ B`),
then `H ∩ H^x ∩ H^y = H_G` for some `x, y ∈ G`, where `H_G` is the normal core of `H`. -/
def coverAvoidTripleIntersectionCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → ∀ H : Subgroup G,
    (∀ A B : Subgroup G, IsFrattiniChiefFactor A B → A ≤ H ⊔ B) →
    (∀ A B : Subgroup G, IsComplementedChiefFactor A B → H ⊓ A ≤ B) →
    ∃ x y : G, H ⊓ H.map (MulAut.conj x).toMonoidHom ⊓ H.map (MulAut.conj y).toMonoidHom =
      H.normalCore

/--
Resolved true: Kamornikov and Shemetkova proved that such an `H` satisfies `H ∩ H^x ∩ H^y = H_G` for
some `x, y`; the 21st issue of the Kourovka Notebook marks 19.38 solved ("Yes, it is true"). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 19.38 (S. F. Kamornikov); resolution: S. F.
Kamornikov and O. L. Shemetkova, On a question concerning the intersection of Φ-isolators of finite
soluble groups, J. Algebra 641 (2024), 1-8, doi:10.1016/j.jalgebra.2023.11.029, the Kourovka
Notebook (21st issue) marks 19.38 solved: Yes, it is true, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted coverAvoidTripleIntersectionCore_holds : coverAvoidTripleIntersectionCore

end MathlibExt.GroupTheory.CoverAvoidIntersectionCoreKourovka19Problem38Wanted
