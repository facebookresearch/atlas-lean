/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Locally normal groups modulo the second centre (Kourovka Notebook Problem 1.9)

Kourovka Notebook, Archive of Solved Problems, Problem 1.9 (Yu. M. Gorchakov): can the factor-group
of a locally normal group by the second term of its upper central series be embedded
(isomorphically) in a direct product of finite groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.LocallyNormalSecondCentreQuotientKourovka1Problem9Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.9 (Yu. M.
Gorchakov). UnsolvedMath record UM-00700007 (`KOU-1.9`), dataset ulamai/UnsolvedMath v1.8.0.

Locally normal: every finite subset lies in a finite normal subgroup. A direct product of finite
groups is the restricted product: the subgroup of `∏ᵢ Hᵢ` of elements with finite support. In the
unrestricted product the answer would be immediate, already for `G / Z(G)`: in a locally normal
group every centralizer `C_G(x)` has finite index, so `G / Z(G)` is residually finite. The index
type and the factors are taken in `Type`.
-/

/-- `G` is locally normal: every finite subset lies in a finite normal subgroup. -/
def IsLocallyNormal (G : Type*) [Group G] : Prop :=
  ∀ S : Finset G, ∃ N : Subgroup G, N.Normal ∧ (N : Set G).Finite ∧ (S : Set G) ⊆ N

/-- Kourovka 1.9 (Yu. M. Gorchakov): for every locally normal group `G`, the quotient of `G` by the
second term `ζ₂(G)` of its upper central series embeds in a direct product of finite groups: an
injective homomorphism into `∏ᵢ Hᵢ` (finite `Hᵢ`) all of whose values have finite support. -/
def locallyNormalModSecondCentreEmbedsInDirectProduct : Prop :=
  ∀ (G : Type) [Group G], IsLocallyNormal G →
    ∃ (ι : Type) (H : ι → Type) (_ : ∀ i, Group (H i)) (_ : ∀ i, Finite (H i))
      (f : G ⧸ Subgroup.upperCentralSeries G 2 →* ((i : ι) → H i)),
      Function.Injective f ∧ ∀ x, {i | f x i ≠ 1}.Finite

/--
Resolved true: the Kourovka Archive answers "Yes, it can", citing Gorchakov (1976): for every
locally normal group `G`, `G / ζ₂(G)` embeds in a direct product of finite groups. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.9 (Yu. M. Gorchakov);
resolution: Yu. M. Gorchakov, Subgroups of direct products, Algebra and Logic 15 (1976), 386-390,
Kourovka Archive, Problem 1.9 ("Yes, it can").
-/
public theorem_wanted locallyNormalModSecondCentreEmbedsInDirectProduct_holds :
    locallyNormalModSecondCentreEmbedsInDirectProduct

end MathlibExt.GroupTheory.LocallyNormalSecondCentreQuotientKourovka1Problem9Wanted
