/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely presented soluble groups without max-n (Kourovka Notebook Problem 8.47)

Kourovka Notebook, Archive of Solved Problems, Problem 8.47 (Yu. I. Merzlyakov): do there exist
finitely presented soluble groups in which the maximum condition for normal subgroups fails but all
central sections are finitely generated?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyPresentedSolubleMaxNCentralSectionsKourovka8Problem47Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.47 (Yu. I.
Merzlyakov). UnsolvedMath record UM-00700497 (`KOU-8.47`), dataset ulamai/UnsolvedMath v1.8.0.

Finitely presented is Mathlib's `Group.IsFinitelyPresented`. The maximum condition for normal
subgroups fails when the normal subgroups are not well-founded under `>`. A central section of `G`
is `H / K` with `K` normal in `G`, `K ≤ H` and `[H, G] ≤ K` (so `H / K` lies in the centre of `G /
K`); finitely generated is `Group.FG` of `H / K`.
-/

/-- Kourovka 8.47 (Yu. I. Merzlyakov): there is a finitely presented soluble group that does not
satisfy the maximal condition on normal subgroups but all of whose central sections `H / K` (`K` a
normal subgroup of `G`, `K ≤ H`, `[H, G] ≤ K`) are finitely generated. -/
def finitelyPresentedSolubleCentralSectionsFG : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ Group.IsSolvable G ∧
    ¬ WellFoundedGT {N : Subgroup G // N.Normal} ∧
    ∀ (H K : Subgroup G) [K.Normal], K ≤ H → (∀ h ∈ H, ∀ g : G, h * g * h⁻¹ * g⁻¹ ∈ K) →
      Group.FG (H ⧸ K.subgroupOf H)

/--
Resolved true: the Kourovka Archive answers 8.47 "Yes", citing Sosnovskii, Finitely presented
solvable groups that do not satisfy the maximal condition for normal subgroups (1984). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.47 (Yu. I. Merzlyakov);
resolution: Yu. V. Sosnovskii, Finitely presented solvable groups that do not satisfy the maximal
condition for normal subgroups, Math. Notes 36 (1984), 577-580, Kourovka Archive, Problem 8.47: Yes
(Sosnovskii), https://doi.org/10.1007/BF01137405.
-/
public theorem_wanted finitelyPresentedSolubleCentralSectionsFG_holds :
    finitelyPresentedSolubleCentralSectionsFG

end MathlibExt.GroupTheory.FinitelyPresentedSolubleMaxNCentralSectionsKourovka8Problem47Wanted
