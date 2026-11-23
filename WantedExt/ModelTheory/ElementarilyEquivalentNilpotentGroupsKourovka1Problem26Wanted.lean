/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elementarily equivalent finitely generated nilpotent groups (Kourovka Notebook Problem 1.26)

Kourovka Notebook, Archive of Solved Problems, Problem 1.26 (M. I. Kargapolov): does elementary
equivalence of two finitely generated nilpotent groups imply that they are isomorphic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExt.ModelTheory.ElementarilyEquivalentNilpotentGroupsKourovka1Problem26Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.26 (M. I.
Kargapolov). UnsolvedMath record UM-00700021 (`KOU-1.26`), dataset ulamai/UnsolvedMath v1.8.0.

Elementary equivalence is Mathlib's `ElementarilyEquivalent` for the first-order language of groups
`groupLanguage` (MathlibExt) with the canonical structures.
-/

open FirstOrder Language

/-- Kourovka 1.26 (M. I. Kargapolov): finitely generated nilpotent groups that are elementarily
equivalent in the first-order language of groups are isomorphic. -/
def elemEquivFGNilpotentGroupsIsomorphic : Prop :=
  ∀ (G H : Type) [Group G] [Group H], Group.FG G → Group.FG H → Group.IsNilpotent G →
    Group.IsNilpotent H →
      (letI := groupLanguageStructure G; letI := groupLanguageStructure H;
        groupLanguage.ElementarilyEquivalent G H) → Nonempty (G ≃* H)

/--
Resolved false: the Kourovka Archive answers 1.26 "No", citing Zil'ber's two finitely generated
nilpotent groups of class 2 ("metabelian" in the title, in the older sense of nilpotent of class 2)
that are elementarily equivalent but not isomorphic. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 1.26 (M. I. Kargapolov); resolution: B. I. Zil'ber, An example
of two elementarily equivalent, but nonisomorphic finitely generated metabelian groups, Algebra and
Logic 10 (1971), 192-197 (Zbl 0256.20004), Kourovka Archive, Problem 1.26 (No).
-/
public theorem_wanted elemEquivFGNilpotentGroupsIsomorphic_refuted :
    ¬ elemEquivFGNilpotentGroupsIsomorphic

end MathlibExt.ModelTheory.ElementarilyEquivalentNilpotentGroupsKourovka1Problem26Wanted
