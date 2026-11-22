/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Radical hereditary formations need not be composition formations (Kourovka Notebook Problem 12.7)

Kourovka Notebook, Archive of Solved Problems, Problem 12.7 (A. F. Vasil'ev): is every radical
hereditary formation of finite groups a composition formation?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.7 (A. F.
Vasil'ev). UnsolvedMath record UM-00700827 (`KOU-12.7`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. A formation contains the trivial group and is closed under quotients and
subdirect products; a radical class is a Fitting class (closed under normal subgroups and under
products of two normal members); hereditary means closed under all subgroups. A composition
formation (Shemetkov) is taken in its standard equivalent form, a solubly saturated (Baer-local)
formation: `G ⧸ Φ(R(G)) ∈ 𝔉` implies `G ∈ 𝔉`, with `R(G)` the soluble radical. The three names are
synonyms in E. N. Myslovets and A. F. Vasil'ev (arXiv:1603.04018, Section 2), whose definition
allows any soluble normal subgroup `N` in place of `R(G)`; this is equivalent for formations, since
`Φ(N) ≤ Φ(R(G))`.
-/

/-- A class of groups closed under isomorphism, given by a membership predicate on groups in
`Type`; only its finite members matter below. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- `G ⧸ N` lies in `X` (with `N` normal). -/
def QuotMem (X : GroupClass) {G : Type} [Group G] (N : Subgroup G) : Prop :=
  ∃ _ : N.Normal, X.mem (G ⧸ N)

/-- A formation of finite groups: it contains the trivial group, is closed under quotients, and
`G ⧸ N₁, G ⧸ N₂ ∈ X` implies `G ⧸ (N₁ ⊓ N₂) ∈ X`. -/
def IsFormation (X : GroupClass) : Prop :=
  X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- A radical (Fitting) class of finite groups: closed under normal subgroups and under products
of two normal subgroups belonging to the class. -/
def IsRadical (X : GroupClass) : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → X.mem G → X.mem N) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G), N₁.Normal → N₂.Normal →
    X.mem N₁ → X.mem N₂ → X.mem ↥(N₁ ⊔ N₂)

/-- A hereditary class of finite groups: closed under subgroups. -/
def IsHereditary (X : GroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), X.mem G → X.mem H

/-- `R` is the soluble radical of `G`: the largest soluble normal subgroup. -/
def IsSolubleRadical {G : Type} [Group G] (R : Subgroup G) : Prop :=
  R.Normal ∧ Group.IsSolvable R ∧ ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N ≤ R

/-- A composition (solubly saturated, Baer-local) formation: `G ⧸ Φ(R(G)) ∈ X` implies `G ∈ X`,
where `R(G)` is the soluble radical and `Φ` the Frattini subgroup. -/
def IsComposition (X : GroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R : Subgroup G), IsSolubleRadical R →
    QuotMem X ((frattini R).map R.subtype) → X.mem G

/-- Kourovka 12.7 (A. F. Vasil'ev): every radical hereditary formation of finite groups is a
composition formation. -/
def radicalHereditaryFormationIsComposition : Prop :=
  ∀ X : GroupClass, IsFormation X → IsRadical X → IsHereditary X → IsComposition X

/--
Resolved false: the Kourovka Archive answers 12.7 "No, it is not" (S. F. Kamornikov, 1994): some
radical hereditary formation of finite groups is not a composition formation. Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.7 (A. F. Vasil'ev); resolution: S.
F. Kamornikov, Math. Notes 55 (1994), no. 6, 586-588, Kourovka Archive, Problem 12.7: No, it is not.
-/
public theorem_wanted radicalHereditaryFormationIsComposition_refuted :
    ¬ radicalHereditaryFormationIsComposition

end MathlibExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted
