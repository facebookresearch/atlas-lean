/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complements of insoluble minimal normal subgroups (Kourovka Notebook Problem 3.59)

Kourovka Notebook, Archive of Solved Problems, Problem 3.59 (L. A. Shemetkov): let `H` be an
insoluble minimal normal subgroup of a finite group `G`, and suppose that `H` has cyclic Sylow
`p`-subgroups for every prime `p` dividing `|G : H|`. Prove that `H` has at least one complement in
`G`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow
public import WantedExt.GroupTheory.CentralizerDimensionSocleQuotientKourovka19Problem101Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.InsolubleMinimalNormalComplementKourovka3Problem59Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.59 (L. A.
Shemetkov). UnsolvedMath record UM-00700207 (`KOU-3.59`), dataset ulamai/UnsolvedMath v1.8.0.

Groups are finite types; `H` is minimal normal (non-trivial, containing no normal subgroup of `G`
other than `⊥` and `H`; `IsMinimalNormal` of the Kourovka 19.101 entry, reused here) and not soluble
(`Group.IsSolvable`). The Sylow hypothesis ranges over primes `p` dividing `H.index`; a complement
is a subgroup `K` with `H ∩ K = 1` and `HK = G` (`Subgroup.IsComplement'`).
-/

open MathlibExt.GroupTheory.CentralizerDimensionSocleQuotientKourovka19Problem101Wanted

/-- Kourovka 3.59 (L. A. Shemetkov): if `H` is an insoluble minimal normal subgroup of a finite
group `G` and the Sylow `p`-subgroups of `H` are cyclic for every prime `p` dividing `|G : H|`,
then `H` has a complement in `G`. -/
def insolubleMinimalNormalComplemented : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), IsMinimalNormal H →
    ¬ Group.IsSolvable H → (∀ p : ℕ, p.Prime → p ∣ H.index → ∀ P : Sylow p H, IsCyclic P) →
    ∃ K : Subgroup G, H.IsComplement' K

/--
Resolved true: Syskin and Shemetkov proved that an insoluble minimal normal subgroup `H` of a finite
group `G` whose Sylow `p`-subgroups are cyclic for every prime `p` dividing `|G : H|` has a
complement in `G`; the Kourovka Archive records 3.59 as proved. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.59 (L. A. Shemetkov); resolution:
S. A. Syskin, Complementarity in finite groups, Siberian Math. J. 12 (1971), 342-344; L. A.
Shemetkov, On the existence of π-complements for normal subgroups of finite groups, Soviet Math.
Dokl. 11 (1970), 1436-1438, Kourovka Archive of Solved Problems, Problem 3.59: This was proved,
https://doi.org/10.1007/BF00969061.
-/
public theorem_wanted insolubleMinimalNormalComplemented_holds : insolubleMinimalNormalComplemented

end MathlibExt.GroupTheory.InsolubleMinimalNormalComplementKourovka3Problem59Wanted
