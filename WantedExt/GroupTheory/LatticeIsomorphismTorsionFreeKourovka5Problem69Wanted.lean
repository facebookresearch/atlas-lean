/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lattice isomorphisms of torsion-free groups (Kourovka Notebook Problem 5.69)

Kourovka Notebook, Archive of Solved Problems, Problem 5.69 (B. V. Yakovlev): is every lattice
isomorphism between torsion-free groups having no non-trivial cyclic normal subgroups induced by a
group isomorphism?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.LatticeIsomorphismTorsionFreeKourovka5Problem69Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.69 (B. V.
Yakovlev). UnsolvedMath record UM-00700347 (`KOU-5.69`), dataset ulamai/UnsolvedMath v1.8.0.

A lattice isomorphism is an order isomorphism `Subgroup G ≃o Subgroup H` of subgroup lattices; it is
induced by `f : G ≃* H` when it maps every `K` to `f(K)`. Torsion-free is written `∀ g, g ≠ 1 → ¬
IsOfFinOrder g`. A non-trivial cyclic normal subgroup is `⟨g⟩` normal with `g ≠ 1`.
-/

/-- Kourovka 5.69 (B. V. Yakovlev): every isomorphism `Subgroup G ≃o Subgroup H` of subgroup
lattices of torsion-free groups having no non-trivial cyclic normal subgroups is induced by a group
isomorphism `G ≃* H`. -/
def latticeIsomorphismInduced : Prop :=
  ∀ (G H : Type) [Group G] [Group H],
    (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) → (∀ h : H, h ≠ 1 → ¬ IsOfFinOrder h) →
    (∀ g : G, (Subgroup.zpowers g).Normal → g = 1) →
    (∀ h : H, (Subgroup.zpowers h).Normal → h = 1) →
    ∀ φ : Subgroup G ≃o Subgroup H, ∃ f : G ≃* H, ∀ K : Subgroup G, φ K = K.map f.toMonoidHom

/--
Resolved false: the Kourovka Archive answers 5.69 "No", citing Olshanskii (1979): some isomorphism
of subgroup lattices between torsion-free groups without non-trivial cyclic normal subgroups is not
induced by any group isomorphism. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 5.69 (B. V. Yakovlev); resolution: A. Yu. Olshanskii, Groups with cyclic
subgroups, C. R. Acad. Bulgare Sci. 32 (1979), 1165-1166, Kourovka Archive, Problem 5.69: No
(Olshanskii), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted latticeIsomorphismInduced_refuted : ¬ latticeIsomorphismInduced

end MathlibExt.GroupTheory.LatticeIsomorphismTorsionFreeKourovka5Problem69Wanted
