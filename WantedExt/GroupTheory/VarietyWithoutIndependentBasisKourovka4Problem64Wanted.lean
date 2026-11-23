/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A variety of groups without an independent basis of identities (Kourovka Notebook Problem 4.64)

Kourovka Notebook, Archive of Solved Problems, Problem 4.64 (A. Tarski): does there exist a variety
of groups that does not admit an independent system of defining identities?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.GroupLawsShared

@[expose] public section

namespace MathlibExt.GroupTheory.VarietyWithoutIndependentBasisKourovka4Problem64Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.64 (A.
Tarski). UnsolvedMath record UM-00700271 (`KOU-4.64`), dataset ulamai/UnsolvedMath v1.8.0.

Laws and varieties are `SatisfiesLaws` of the Kourovka 11.21 entry, reused here, and consequence is
that of the shared module `WantedExt.GroupTheory.GroupLawsShared`: a law is a word of `FreeGroup ℕ`,
the variety defined by a set `W` of laws consists of the groups in which every law of `W` holds,
every variety arises this way, and consequence is semantic over all groups in `Type` (equivalently,
by the completeness theorem, derivability). An independent system of defining identities of the
variety defined by `W` is a set `B` of laws with the same consequences as `W` such that no member of
`B` is a consequence of the others.
-/

open MathlibExt.GroupTheory.GroupLawsShared

/-- Kourovka 4.64 (A. Tarski): some variety of groups has no independent system of defining
identities: for some set `W` of laws, no independent set of laws has the same consequences. -/
def existsVarietyWithoutIndependentBasis : Prop :=
  ∃ W : Set (FreeGroup ℕ), ¬ HasIndependentLawBasis W

/--
Resolved true: the Kourovka Archive answers 4.64 "Yes, there does", citing Kleiman, Some questions
in the theory of varieties of groups (Math. USSR-Izv. 22 (1984), 33-65), whose abstract lists among
its results an example of a group variety that does not have an independent basis of identities.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.64 (A.
Tarski); resolution: Yu. G. Kleiman, Some questions in the theory of varieties of groups, Math.
USSR-Izv. 22 (1984), 33-65, abstract: among the results is an example of a group variety that does
not have an independent basis of identities; Kourovka Archive, Problem 4.64: Yes, there does
(Kleiman), https://doi.org/10.1070/IM1984v022n01ABEH001433.
-/
public theorem_wanted existsVarietyWithoutIndependentBasis_holds :
    existsVarietyWithoutIndependentBasis

end MathlibExt.GroupTheory.VarietyWithoutIndependentBasisKourovka4Problem64Wanted
