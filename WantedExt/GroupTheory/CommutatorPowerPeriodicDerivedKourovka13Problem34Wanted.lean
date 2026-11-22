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

/-- Kourovka 13.34 (I. D. Macdonald): for every `n ≥ 1`, every group satisfying the identity
`[x, y]ⁿ = 1` has a periodic derived subgroup. -/
def commutatorIdentityPeriodicDerived : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (G : Type) [Group G], (∀ x y : G, ⁅x, y⁆ ^ n = 1) →
    ∀ g ∈ commutator G, IsOfFinOrder g

/--
Resolved false: the Kourovka Archive answers 13.34 "No, not always" (G. S. Deryabina and P. A.
Kozhevnikov, 1999; S. I. Adyan, 2000): for some `n ≥ 1` some group satisfying `[x, y]ⁿ = 1` has a
derived subgroup that is not periodic. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 13.34 (I. D. Macdonald; V. D. Mazurov); resolution: G. S. Deryabina and P.
A. Kozhevnikov, Commun. Algebra 27 (1999), no. 9, 4525-4530; S. I. Adyan, Dokl. Math. 62 (2000), no.
2, 174-176, Kourovka Archive, Problem 13.34: No, not always.
-/
public theorem_wanted commutatorIdentityPeriodicDerived_refuted :
    ¬ commutatorIdentityPeriodicDerived

end MathlibExt.GroupTheory.CommutatorPowerPeriodicDerivedKourovka13Problem34Wanted
