/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Normal subgroups of Z̄-groups (Kourovka Notebook Problem 8.16)

Kourovka Notebook, Problem 8.16 (Sh. S. Kemkhadze), marked solved in the 21st issue: is the class of
all `Z̄`-groups closed under taking normal subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.ZBarGroupNormalSubgroupKourovka8Problem16Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 8.16 (Sh. S. Kemkhadze). UnsolvedMath
record UM-00700468 (`KOU-8.16`), dataset ulamai/UnsolvedMath v1.8.0.

A `Z̄`-group (Kurosh and Chernikov; Kargapolov and Merzljakov, Fundamentals of the Theory of Groups,
§22.1) is a group every normal system of which (a complete chain of normal subgroups, in the
preprint's terminology) is contained in a central one. The resolving preprint proves (Lemma 2.1)
that this holds exactly when every chief factor `A / B` is central, `[A, G] ≤ B`, where a chief
factor is a pair of normal subgroups `B < A` with no normal subgroup strictly between
(`IsChiefFactor` of `KourovkaNotebookShared`); that characterization is the definition used here.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared (IsChiefFactor)

/-- `G` is a `Z̄`-group (Kurosh and Chernikov): every normal system of `G` refines to a central
one; equivalently, every chief factor `A / B` of `G` is central, `[A, G] ≤ B`. -/
def IsZBarGroup (G : Type*) [Group G] : Prop :=
  ∀ A B : Subgroup G, IsChiefFactor A B → ∀ a ∈ A, ∀ g : G, a * g * a⁻¹ * g⁻¹ ∈ B

/-- Kourovka 8.16 (Sh. S. Kemkhadze): the class of `Z̄`-groups is closed under taking normal
subgroups. -/
def zBarClosedUnderNormalSubgroups : Prop :=
  ∀ (G : Type) [Group G], IsZBarGroup G → ∀ N : Subgroup G, N.Normal → IsZBarGroup N

/--
Resolved false: the 21st issue marks 8.16 solved, "No, it is not", citing Jayadevan's 2026 preprint
(an AI-generated solution confirmed by J. S. Wilson). By its Theorem 1.1 and Corollary 1.2 every
chief factor of the affine group `G = ℤ₂⁺ ⋊ ℤ₂ˣ` over the `2`-adic integers is central, while by its
Lemma 4.1 its normal subgroup `N = ℤ₂⁺ ⋊ {±1}` has the non-central chief factor `ℤ / 3ℤ` of integer
translations; by its Lemma 2.1 this means `G` is a `Z̄`-group and `N` is not. Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 8.16 (Sh. S. Kemkhadze); resolution: A. Jayadevan, Central chief
factors of affine groups over local rings, preprint, Zenodo, 2026 (AI-generated solution confirmed
by J. S. Wilson), Kourovka Notebook 21st issue, Problem 8.16, marked solved: No, it is not;
preprint, Lemma 2.1, Theorem 1.1, Corollary 1.2 and Lemma 4.1, https://zenodo.org/records/22821641.
-/
public theorem_wanted zBarClosedUnderNormalSubgroups_refuted : ¬ zBarClosedUnderNormalSubgroups

end MathlibExt.GroupTheory.ZBarGroupNormalSubgroupKourovka8Problem16Wanted
