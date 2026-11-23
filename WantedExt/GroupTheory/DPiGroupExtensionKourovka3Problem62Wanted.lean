/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Extensions of D_π-groups (Kourovka Notebook Problem 3.62)

Kourovka Notebook, Archive of Solved Problems, Problem 3.62 (L. A. Shemetkov): (well-known problem)
a finite group is said to be a `D_π`-group if any two of its maximal `π`-subgroups are conjugate. Is
an extension of a `D_π`-group by a `D_π`-group always a `D_π`-group?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.DPiGroupExtensionKourovka3Problem62Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.62 (L. A.
Shemetkov). UnsolvedMath record UM-00700210 (`KOU-3.62`), dataset ulamai/UnsolvedMath v1.8.0.

`D_π`-groups are the `IsDPiGroup` of the Kourovka 18.31 entry, which transcribes the definition of
3.62 (any two maximal `π`-subgroups conjugate), reused here. An extension of a `D_π`-group by a
`D_π`-group is a finite group `G` with a normal subgroup `N` such that `N` and `G / N` are
`D_π`-groups. `π` is any set of natural numbers (only its primes matter).
-/

open MathlibExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted

/-- Kourovka 3.62 (L. A. Shemetkov, well-known problem): an extension of a `D_π`-group by a
`D_π`-group is a `D_π`-group: if `N` is a normal subgroup of a finite group `G` and both `N` and
`G / N` are `D_π`-groups (any two maximal `π`-subgroups are conjugate), then so is `G`. -/
def dPiGroupExtensionClosed : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal],
    IsDPiGroup π N → IsDPiGroup π (G ⧸ N) → IsDPiGroup π G

/--
Resolved true, modulo the classification of finite simple groups: Revin and Vdovin prove that an
extension of a `D_π`-group by a `D_π`-group is a `D_π`-group; the Kourovka Archive answers 3.62
"Yes, it is mod CFSG". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 3.62 (L. A. Shemetkov); resolution: D. O. Revin and E. P. Vdovin, Hall subgroups of finite
groups, in: Ischia Group Theory 2004, Contemp. Math. 402 (2006), 229-263, main result 1 (M.
Deaconescu's zbMATH review, Zbl 1104.20023: an extension of a `D_π`-group by a `D_π`-group is a
`D_π`-group, answering Shemetkov's problem); Kourovka Archive of Solved Problems, Problem 3.62: Yes,
it is mod CFSG, https://doi.org/10.1090/conm/402/07585.
-/
public theorem_wanted dPiGroupExtensionClosed_holds : dPiGroupExtensionClosed

end MathlibExt.GroupTheory.DPiGroupExtensionKourovka3Problem62Wanted
