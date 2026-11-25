/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Periodicity of the derived subgroup under `[x, y]ⁿ = 1` (Kourovka Notebook Problem 13.34)

Kourovka Notebook, Archive of Solved Problems, Problem 13.34 (I. D. Macdonald; V. D. Mazurov): if
the identity `[x, y]ⁿ = 1` holds on a group, is the derived subgroup of the group periodic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.CommutatorPowerPeriodicDerivedKourovka13Problem34Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.34 (I. D.
Macdonald; V. D. Mazurov). UnsolvedMath record UM-00700952 (`KOU-13.34`), dataset
ulamai/UnsolvedMath v1.8.0.

`n ≥ 1` (for `n = 0` the identity is vacuous and the claim fails for free groups); periodic means
that every element of the derived subgroup has finite order.
-/

open scoped commutatorElement

/-- **Derived subgroups under a commutator power identity (Kourovka 13.34).** This is the
proposition that for every integer $n \ge 1$ and every group $G$ with $[x, y]^n = 1$ for all
$x, y \in G$, every element of the derived subgroup $[G, G]$ has finite order, that is, the derived
subgroup of $G$ is periodic.

This is Kourovka Notebook Problem 13.34 (I. D. Macdonald). -/
def commutatorIdentityPeriodicDerived : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (G : Type) [Group G], (∀ x y : G, ⁅x, y⁆ ^ n = 1) →
    ∀ g ∈ commutator G, IsOfFinOrder g

/--
**A commutator power identity need not make the derived subgroup periodic.** There exist an
integer $n \ge 1$ and a group $G$ such that $[x, y]^n = 1$ for all $x, y \in G$ but some element of
the derived subgroup $[G, G]$ has infinite order. This answers Kourovka Notebook Problem 13.34
(I. D. Macdonald; V. D. Mazurov) in the negative, by results of G. S. Deryabina and P. A.
Kozhevnikov from 1999 and of S. I. Adyan from 2000.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 13.34 (I. D. Macdonald; V. D. Mazurov); resolution: G. S. Deryabina and P.
A. Kozhevnikov, Commun. Algebra 27 (1999), no. 9, 4525-4530; S. I. Adyan, Dokl. Math. 62 (2000), no.
2, 174-176, Kourovka Archive, Problem 13.34: No, not always.
-/
public theorem_wanted commutatorIdentityPeriodicDerived_refuted :
    ¬ commutatorIdentityPeriodicDerived

end MathlibExt.GroupTheory.CommutatorPowerPeriodicDerivedKourovka13Problem34Wanted
