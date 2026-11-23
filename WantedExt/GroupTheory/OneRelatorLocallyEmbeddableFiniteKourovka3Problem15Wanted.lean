/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local embeddability of one-relator groups into finite groups (Kourovka Notebook Problem 3.15)

Kourovka Notebook, Archive of Solved Problems, Problem 3.15 (M. I. Kargapolov): a group `G` is said
to be `U`-embeddable in a class `𝔎` of groups if, for any finite submodel `M ⊂ G`, there is a group
`A ∈ 𝔎` such that `M` is isomorphic to some submodel of `A`. Are the following groups `U`-embeddable
in the class of finite groups: (a) every group with one defining relation? (b) every group defined
by one relation in the variety of soluble groups of a given derived length?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorLocallyEmbeddableFiniteKourovka3Problem15Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.15 (M. I.
Kargapolov). UnsolvedMath record UM-00700169 (`KOU-3.15`), dataset ulamai/UnsolvedMath v1.8.0.

`U`-embeddability in finite groups is stated as local embeddability: every finite subset `M` maps
injectively into a finite group preserving the products `x y` with `x, y, x y ∈ M`. This is
equivalent to the submodel formulation (apply it to `M ∪ M M ∪ {1} ∪ M⁻¹` to get reflection of
products and preservation of `1` and inverses). One-relator groups are `PresentedGroup {r}`, `r ∈
FreeGroup (Fin n)`; in (b) the group defined by `r` in the variety of soluble groups of derived
length at most `k` is `F_n / (F_n^(k) ⟨⟨r⟩⟩)`, and the claim is stated for every `k`.
-/

/-- `G` is `U`-embeddable in the class of finite groups (locally embeddable into finite groups):
every finite subset `M` of `G` admits a map into a finite group that is injective on `M` and
preserves every product `x y` with `x, y, x y ∈ M`. -/
def IsLocallyEmbeddableIntoFinite (G : Type) [Group G] : Prop :=
  ∀ M : Finset G, ∃ (A : Type) (_ : Group A) (_ : Finite A) (f : G → A),
    Set.InjOn f (M : Set G) ∧ ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M → f (x * y) = f x * f y

/-- Kourovka 3.15(a) (M. I. Kargapolov): every group with one defining relation is
`U`-embeddable in the class of finite groups. -/
def oneRelatorGroupsLocallyEmbeddable : Prop :=
  ∀ (n : ℕ) (r : FreeGroup (Fin n)), IsLocallyEmbeddableIntoFinite (PresentedGroup {r})

/-- Kourovka 3.15(b) (M. I. Kargapolov): for every `k`, every group defined by one relation in the
variety of soluble groups of derived length at most `k`, i.e. `F_n / (F_n^(k) ⟨⟨r⟩⟩)`, is
`U`-embeddable in the class of finite groups. -/
def solubleOneRelatorGroupsLocallyEmbeddable : Prop :=
  ∀ (k n : ℕ) (r : FreeGroup (Fin n)), IsLocallyEmbeddableIntoFinite
    (FreeGroup (Fin n) ⧸ (derivedSeries (FreeGroup (Fin n)) k ⊔ Subgroup.normalClosure {r}))

/--
Resolved false: the Kourovka Archive answers 3.15 "No, in both cases", citing Budkin and Gorbunov
(Algebra and Logic 14 (1975)); the Archive's example is the non-Hopfian one-relator group `⟨a, b |
(b²)^a = b³⟩`, which is not `U`-embeddable into finite groups. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.15 (M. I. Kargapolov); resolution:
A. I. Budkin and V. A. Gorbunov, Algebra and Logic 14 (1975), 73-84; Yu. I. Merzlyakov (1969),
example in the Kourovka Archive, Kourovka Archive, Problem 3.15: No, in both cases; the Archive's
example: ⟨a, b | (b²)^a = b³⟩ is non-Hopfian (Baumslag and Solitar, 1962), hence not U-embeddable
into finite groups, and G/G^(k) is also non-Hopfian for a suitable k,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted oneRelatorGroupsLocallyEmbeddable_refuted :
    ¬ oneRelatorGroupsLocallyEmbeddable

/--
Resolved false: the Kourovka Archive answers 3.15 "No, in both cases", citing Budkin and Gorbunov
(Algebra and Logic 14 (1975)); in the Archive's example `G / G^(k)`, for `G = ⟨a, b | (b²)^a = b³⟩`
and a suitable `k`, is a non-Hopfian group defined by one relation in the variety of soluble groups
of derived length `k`, so it is not `U`-embeddable into finite groups. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.15 (M. I. Kargapolov); resolution:
A. I. Budkin and V. A. Gorbunov, Algebra and Logic 14 (1975), 73-84; Yu. I. Merzlyakov (1969),
example in the Kourovka Archive, Kourovka Archive, Problem 3.15: No, in both cases; the Archive's
example: ⟨a, b | (b²)^a = b³⟩ is non-Hopfian (Baumslag and Solitar, 1962), hence not U-embeddable
into finite groups, and G/G^(k) is also non-Hopfian for a suitable k,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted solubleOneRelatorGroupsLocallyEmbeddable_refuted :
    ¬ solubleOneRelatorGroupsLocallyEmbeddable

end MathlibExt.GroupTheory.OneRelatorLocallyEmbeddableFiniteKourovka3Problem15Wanted
