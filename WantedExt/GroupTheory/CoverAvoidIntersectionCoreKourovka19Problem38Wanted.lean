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

/-- **Frattini chief factor.** For subgroups $A$ and $B$ of a group $G$, $A/B$ is a Frattini chief
factor of $G$ when $A/B$ is a chief factor of $G$ and $A$ is contained in every maximal subgroup
of $G$ that contains $B$; equivalently, $A/B \le \Phi(G/B)$, where $\Phi$ denotes the Frattini
subgroup. -/
def IsFrattiniChiefFactor {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  IsChiefFactor A B ∧ ∀ M : Subgroup G, IsCoatom M → B ≤ M → A ≤ M

/-- **Complemented chief factor.** For subgroups $A$ and $B$ of a group $G$, $A/B$ is a
complemented chief factor of $G$ when $A/B$ is a chief factor of $G$ and some subgroup $M$ of $G$
satisfies $\langle M, A \rangle = G$ and $M \cap A = B$ (as $A$ is normal, the first condition
says $MA = G$). -/
def IsComplementedChiefFactor {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  IsChiefFactor A B ∧ ∃ M : Subgroup G, M ⊔ A = ⊤ ∧ M ⊓ A = B

/-- **Kourovka Problem 19.38.** The statement that for every finite soluble group $G$ and every
subgroup $H$ of $G$ that covers every Frattini chief factor $A/B$ of $G$, that is,
$A \le \langle H, B \rangle$ (which is $HB$, as $B$ is normal), and avoids every complemented
chief factor $A/B$ of $G$, that is, $H \cap A \le B$, there are $x, y \in G$ such that
$H \cap H^x \cap H^y = H_G$, where $H^x = xHx^{-1}$ and $H_G$ is the normal core of $H$, the
largest normal subgroup of $G$ contained in $H$. -/
def coverAvoidTripleIntersectionCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → ∀ H : Subgroup G,
    (∀ A B : Subgroup G, IsFrattiniChiefFactor A B → A ≤ H ⊔ B) →
    (∀ A B : Subgroup G, IsComplementedChiefFactor A B → H ⊓ A ≤ B) →
    ∃ x y : G, H ⊓ H.map (MulAut.conj x).toMonoidHom ⊓ H.map (MulAut.conj y).toMonoidHom =
      H.normalCore

/-- **Kamornikov–Shemetkova theorem (Kourovka Problem 19.38).** Let $H$ be a subgroup of a
finite soluble group $G$. Suppose that $H$ covers every Frattini chief factor $A/B$ of $G$, that
is, $A \le \langle H, B \rangle$ (which is $HB$, as $B$ is normal), and avoids every complemented
chief factor $A/B$ of $G$, that is, $H \cap A \le B$. Then there are $x, y \in G$ such that
$H \cap H^x \cap H^y = H_G$, where $H^x = xHx^{-1}$ and $H_G$ is the normal core of $H$, the
largest normal subgroup of $G$ contained in $H$.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 19.38 (S. F. Kamornikov); resolution: S. F.
Kamornikov and O. L. Shemetkova, On a question concerning the intersection of Φ-isolators of finite
soluble groups, J. Algebra 641 (2024), 1-8, doi:10.1016/j.jalgebra.2023.11.029, the Kourovka
Notebook (21st issue) marks 19.38 solved: Yes, it is true, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted coverAvoidTripleIntersectionCore_holds : coverAvoidTripleIntersectionCore

end MathlibExt.GroupTheory.CoverAvoidIntersectionCoreKourovka19Problem38Wanted
