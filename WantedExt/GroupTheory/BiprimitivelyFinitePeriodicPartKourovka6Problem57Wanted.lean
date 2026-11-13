/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elements of finite order in biprimitively finite groups (Kourovka Notebook Problem 6.57)

Kourovka Notebook, Archive of Solved Problems, Problem 6.57 (V. P. Shunkov): a group G is
(conjugacy, p-conjugacy) biprimitively finite if, for any finite subgroup H, any two elements of
prime order (any two conjugate elements of prime order, of prime order p) in N_G(H)/H generate a
finite subgroup. Do the elements of finite order in a (conjugacy) biprimitively finite group G form
a subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.BiprimitivelyFinitePeriodicPartKourovka6Problem57Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.57 (V. P.
Shunkov). UnsolvedMath record UM-00700399 (`KOU-6.57`), dataset ulamai/UnsolvedMath v1.8.0.

Biprimitively finite is `IsBiprimitivelyFinite`, copied from the OpenConjectures entry for Kourovka
6.59 (WantedExt cannot import OpenConjectures): for every finite subgroup `H`, any two elements of
prime order of `N_G(H) ⧸ H` generate a finite subgroup. Cherep's group is biprimitively finite
(zbMATH review Zbl 0648.20040), and every biprimitively finite group is conjugacy biprimitively
finite, so the refutation answers both variants of the question. The elements of finite order form a
subgroup exactly when products of such elements have finite order.
-/

/-- `G` is biprimitively finite (Kourovka 6.57; the definition of the OpenConjectures entry for
Kourovka 6.59): for every finite subgroup `H`, any two elements of prime order of `N_G(H) ⧸ H`
generate a finite subgroup. -/
def IsBiprimitivelyFinite (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, (H : Set G).Finite →
    ∀ a b : Subgroup.normalizer (H : Set G) ⧸ H.subgroupOf (Subgroup.normalizer (H : Set G)),
      (orderOf a).Prime → (orderOf b).Prime → Finite (Subgroup.closure {a, b})

/-- Kourovka 6.57 (V. P. Shunkov): in a biprimitively finite group the elements of finite order
form a subgroup, that is, a product of two elements of finite order has finite order. -/
def biprimitivelyFinitePeriodicPartSubgroup : Prop :=
  ∀ (G : Type) [Group G], IsBiprimitivelyFinite G →
    ∀ a b : G, IsOfFinOrder a → IsOfFinOrder b → IsOfFinOrder (a * b)

/--
Resolved false: Cherep (1987) constructs a biprimitively finite group whose elements of finite order
do not form a subgroup; since biprimitively finite groups are conjugacy biprimitively finite, this
answers both variants of 6.57, which the Kourovka Archive answers "Not always". Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.57 (V. P. Shunkov);
resolution: A. A. Cherep, The set of elements of finite order in a biprimitively finite group,
Algebra and Logic 26 (1987), 311-313 (Algebra i Logika 26, no. 4 (1987), 518-521; the Archive prints
volume 29), zbMATH review Zbl 0648.20040 (Yu. I. Merzlyakov): the author answers Problem 6.57
negatively by constructing a biprimitively finite group whose periodic elements do not form a
subgroup; Kourovka Archive, Problem 6.57: Not always (Cherep), https://doi.org/10.1007/BF01980245.
-/
public theorem_wanted biprimitivelyFinitePeriodicPartSubgroup_refuted :
    ¬ biprimitivelyFinitePeriodicPartSubgroup

end MathlibExt.GroupTheory.BiprimitivelyFinitePeriodicPartKourovka6Problem57Wanted
