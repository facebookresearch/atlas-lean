/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elementary equivalence of wreath products (Kourovka Notebook Problem 2.20)

Kourovka Notebook, Archive of Solved Problems, Problem 2.20 (M. I. Kargapolov): is it true that the
wreath products `A ≀ B` and `A₁ ≀ B₁` are elementarily equivalent if and only if `A`, `B` are
elementarily equivalent to `A₁`, `B₁`, respectively?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.ModelTheory.GroupLanguage
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.ModelTheory.WreathProductElementaryEquivalenceKourovka2Problem20Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.20 (M. I.
Kargapolov). UnsolvedMath record UM-00700096 (`KOU-2.20`), dataset ulamai/UnsolvedMath v1.8.0.

Elementary equivalence is Mathlib's `ElementarilyEquivalent` for MathlibExt's first-order language
of groups `groupLanguage`. The wreath product is the restricted (standard) one, the finitely
supported part of Mathlib's regular wreath product `A ≀ᵣ B = (B → A) ⋊ B`, written as a generated
subgroup; for finite `B` it is all of `A ≀ᵣ B` (Timoshenko's paper cites P. M. Neumann's work on
standard wreath products). The four groups are nontrivial: with a trivial factor the question
degenerates (`1 ≀ C₂ ≅ C₂ ≅ C₂ ≀ 1`, while `1` and `C₂` are not even universally equivalent), and
the same example would contradict Timoshenko's positive answer for universal equivalence, which
therefore concerns nontrivial groups. `restrictedWreath` is the shared definition in
`WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

open FirstOrder Language

/-- Kourovka 2.20 (M. I. Kargapolov): for nontrivial groups `A`, `B`, `A₁`, `B₁`, the wreath
products `A ≀ B` and `A₁ ≀ B₁` are elementarily equivalent if and only if `A` is elementarily
equivalent to `A₁` and `B` to `B₁` (first-order language of groups). -/
def wreathElementaryEquivalenceIff : Prop :=
  ∀ (A B A₁ B₁ : Type) [Group A] [Group B] [Group A₁] [Group B₁] [Nontrivial A] [Nontrivial B]
    [Nontrivial A₁] [Nontrivial B₁],
    (letI := groupLanguageStructure (restrictedWreath A B);
      letI := groupLanguageStructure (restrictedWreath A₁ B₁);
      groupLanguage.ElementarilyEquivalent (restrictedWreath A B) (restrictedWreath A₁ B₁)) ↔
    ((letI := groupLanguageStructure A; letI := groupLanguageStructure A₁;
        groupLanguage.ElementarilyEquivalent A A₁) ∧
      (letI := groupLanguageStructure B; letI := groupLanguageStructure B₁;
        groupLanguage.ElementarilyEquivalent B B₁))

/--
Resolved false: the Kourovka Archive answers 2.20 "No", citing Timoshenko, who also proved the
statement with universal equivalence in place of elementary equivalence. Stated for nontrivial
groups, where the question has content. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 2.20 (M. I. Kargapolov); resolution: E. I. Timoshenko, Preservation of
elementary and universal equivalence under the wreath product, Algebra and Logic 7 (1968), no. 4,
273-276, Kourovka Archive, Problem 2.20: No, but if "elementarily" is replaced by "universally" then
it is true, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted wreathElementaryEquivalenceIff_refuted : ¬ wreathElementaryEquivalenceIff

end MathlibExt.ModelTheory.WreathProductElementaryEquivalenceKourovka2Problem20Wanted
