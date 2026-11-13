/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three isospectral finite simple groups (Kourovka Notebook Problem 16.25)

Kourovka Notebook, Archive of Solved Problems, Problem 16.25 (A. V. Vasil'ev): do there exist three
pairwise non-isomorphic finite non-abelian simple groups with the same spectrum?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.ThreeIsospectralSimpleGroupsKourovka16Problem25Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.25 (A. V.
Vasil'ev). UnsolvedMath record UM-00701217 (`KOU-16.25`), dataset ulamai/UnsolvedMath v1.8.0.

The spectrum `ω(G)` is the set of element orders, `Set.range orderOf`. Groups are finite and in
`Type`; non-isomorphic means that no `MulEquiv` exists.
-/

/-- **Spectrum of a group.** The spectrum $\omega(G)$ of a group $G$ is the set of orders of its
elements, where an element of infinite order is counted as having order $0$. -/
def spectrum (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- Kourovka 16.25 (A. V. Vasil'ev): there are three pairwise non-isomorphic finite non-abelian
simple groups with the same spectrum. -/
def threeIsospectralSimpleGroups : Prop :=
  ∃ (G₁ G₂ G₃ : Type) (_ : Group G₁) (_ : Group G₂) (_ : Group G₃)
    (_ : Finite G₁) (_ : Finite G₂) (_ : Finite G₃),
    IsSimpleGroup G₁ ∧ IsSimpleGroup G₂ ∧ IsSimpleGroup G₃ ∧
    (∃ a b : G₁, a * b ≠ b * a) ∧ (∃ a b : G₂, a * b ≠ b * a) ∧ (∃ a b : G₃, a * b ≠ b * a) ∧
    IsEmpty (G₁ ≃* G₂) ∧ IsEmpty (G₁ ≃* G₃) ∧ IsEmpty (G₂ ≃* G₃) ∧
    spectrum G₁ = spectrum G₂ ∧ spectrum G₂ = spectrum G₃

/--
**No three non-isomorphic finite non-abelian simple groups are isospectral.** There do not exist
three pairwise non-isomorphic finite non-abelian simple groups $G_1, G_2, G_3$ with
$\omega(G_1) = \omega(G_2) = \omega(G_3)$, where the spectrum $\omega(G)$ of a group $G$ is the
set of orders of its elements.

This answers Kourovka Problem 16.25 (A. V. Vasil'ev) in the negative; the Kourovka Archive cites
Buturlakin (2010).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.25 (A. V.
Vasil'ev); resolution: A. A. Buturlakin, Sib. Èlektron. Mat. Izv. 7 (2010), 111-114, Kourovka
Archive, Problem 16.25 (No).
-/
public theorem_wanted threeIsospectralSimpleGroups_refuted : ¬ threeIsospectralSimpleGroups

end MathlibExt.GroupTheory.ThreeIsospectralSimpleGroupsKourovka16Problem25Wanted
