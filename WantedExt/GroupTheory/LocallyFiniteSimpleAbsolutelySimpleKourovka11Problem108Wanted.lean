/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Absolute simplicity of locally finite simple groups (Kourovka Notebook Problem 11.108)

Kourovka Notebook, Archive of Solved Problems, Problem 11.108 (R. Phillips): is every locally finite
simple group absolutely simple? A group `G` is absolutely simple if the only composition series of
`G` is `{1, G}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GroupTheory.LocallyFiniteSimpleAbsolutelySimpleKourovka11Problem108Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.108 (R.
Phillips). UnsolvedMath record UM-00700800 (`KOU-11.108`), dataset ulamai/UnsolvedMath v1.8.0.

Composition series are taken in Kurosh's sense: a chain of subgroups containing `1` and `G`, closed
under arbitrary unions and intersections, in which for every jump `A < B` (no member strictly
between) `A` is normal in `B` and `B / A` is simple. Every `g ≠ 1` determines a jump (the union of
the members not containing `g` below the intersection of those containing it), so the jump condition
is never vacuous.
-/

/-- `G` is locally finite: every finitely generated subgroup is finite. -/
def IsLocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ S : Finset G, (Subgroup.closure (S : Set G) : Set G).Finite

/-- `S` is a composition series of `G` in Kurosh's sense: a chain of subgroups containing `1` and
`G`, closed under arbitrary unions (suprema) and intersections (infima), such that for every jump
`A < B` of the chain (no member strictly between) `A` is normal in `B` and `B / A` is simple. -/
def IsCompositionSeries {G : Type*} [Group G] (S : Set (Subgroup G)) : Prop :=
  ⊥ ∈ S ∧ ⊤ ∈ S ∧ IsChain (· ≤ ·) S ∧ (∀ T ⊆ S, sSup T ∈ S) ∧ (∀ T ⊆ S, sInf T ∈ S) ∧
    ∀ A ∈ S, ∀ B ∈ S, A < B → (∀ C ∈ S, ¬ (A < C ∧ C < B)) →
      ∃ _ : (A.subgroupOf B).Normal, IsSimpleGroup (B ⧸ A.subgroupOf B)

/-- Kourovka 11.108 (R. Phillips): every locally finite simple group is absolutely simple: its only
composition series is `{1, G}`. -/
def locallyFiniteSimpleIsAbsolutelySimple : Prop :=
  ∀ (G : Type) [Group G], IsLocallyFinite G → IsSimpleGroup G →
    ∀ S : Set (Subgroup G), IsCompositionSeries S → S = {⊥, ⊤}

/--
Resolved false: the Kourovka Archive answers 11.108 "No, not every", citing Meierfrankenfeld (1995),
whose Section 6 constructs countable locally finite simple groups `G` that are not absolutely
simple, with an ascending series `M₁ ⊴ M₂ ⊴ ⋯` of proper subgroups whose union is `G`: some locally
finite simple group has a composition series other than `{1, G}`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.108 (R. Phillips); resolution: U.
Meierfrankenfeld, Non-finitary locally finite simple groups, in: Proc. Int. Conf. Finite and Locally
Finite Groups, Istanbul, 1994, Kluwer, 1995, 189-212, Section 6, countable locally finite simple
groups that are not absolutely simple; Kourovka Archive, Problem 11.108 ("No, not every"),
https://users.math.msu.edu/users/meierfra/Preprints/Nflfsg/nflfsg.pdf.
-/
public theorem_wanted locallyFiniteSimpleIsAbsolutelySimple_refuted :
    ¬ locallyFiniteSimpleIsAbsolutelySimple

end MathlibExt.GroupTheory.LocallyFiniteSimpleAbsolutelySimpleKourovka11Problem108Wanted
