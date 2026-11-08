/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Formations of groups with all composition factors `T` (Kourovka Notebook Problem 12.97)

Kourovka Notebook, Archive of Solved Problems, Problem 12.97 (L. A. Shemetkov): let `𝔉` be the
formation of all finite groups all of whose composition factors are isomorphic to a fixed
non-abelian simple group `T`. Prove that `𝔉` is not a product of two non-trivial subformations.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleCompositionFactorFormationKourovka12Problem97Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.97 (L. A.
Shemetkov). UnsolvedMath record UM-00700914 (`KOU-12.97`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. `G ∈ 𝔉_T` means a subnormal series with all factors isomorphic to `T` (for
simple `T`, all composition factors isomorphic to `T`; the trivial group belongs). A formation
contains the trivial group and is closed under quotients and subdirect products; the product is
Gaschütz's `𝔐ℌ = {G | G^ℌ ∈ 𝔐}` with `G^ℌ` the `ℌ`-residual; subformations are contained in `𝔉_T`.
Non-trivial factors are proper subformations containing a nontrivial group: since `𝔉_T` is closed
under normal subgroups and extensions, `𝔉_T = 𝔉_T ℌ = 𝔐 𝔉_T` for all subformations `𝔐, ℌ`, so with
`𝔐 = 𝔉_T` or `ℌ = 𝔉_T` allowed the statement would be false.
-/

/-- A class of groups closed under isomorphism, given by a membership predicate on groups in
`Type`; only its finite members matter below. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- A formation of finite groups: it contains the trivial group, is closed under quotients, and
`G ⧸ N₁, G ⧸ N₂ ∈ X` implies `G ⧸ (N₁ ⊓ N₂) ∈ X`. -/
def IsFormation (X : GroupClass) : Prop :=
  X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- `X` contains a nontrivial finite group (`X` is not the trivial formation). -/
def NontrivialClass (X : GroupClass) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ X.mem G

/-- The `X`-residual of `G`: the intersection of the normal subgroups `N` with `G ⧸ N ∈ X`. -/
def residual (X : GroupClass) (G : Type) [Group G] : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : ∃ _ : N.Normal, X.mem (G ⧸ N)), N

/-- `G` lies in `𝔉_T`: it has a subnormal series all of whose factors are isomorphic to `T`; for
simple `T` these are the groups all of whose composition factors are isomorphic to `T`. -/
def AllCompositionFactorsIso (T : Type) [Group T] (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        Nonempty ((H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ)) ≃* T)

/-- `X` is a proper subclass of `𝔉_T`: some finite group of `𝔉_T` does not belong to `X`. -/
def IsProperIn (T : Type) [Group T] (X : GroupClass) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), AllCompositionFactorsIso T G ∧ ¬ X.mem G

/-- Kourovka 12.97 (L. A. Shemetkov): for a non-abelian finite simple group `T`, the formation
`𝔉_T` of finite groups all of whose composition factors are isomorphic to `T` is not the
(Gaschütz) product `𝔐ℌ = {G : G^ℌ ∈ 𝔐}` of two non-trivial proper subformations `𝔐, ℌ`. -/
def compositionFactorFormationIndecomposable : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    ∀ M H : GroupClass, IsFormation M → IsFormation H → NontrivialClass M →
      NontrivialClass H →
      (∀ (G : Type) [Group G] [Finite G], M.mem G → AllCompositionFactorsIso T G) →
      (∀ (G : Type) [Group G] [Finite G], H.mem G → AllCompositionFactorsIso T G) →
      IsProperIn T M → IsProperIn T H →
      ¬ ∀ (G : Type) [Group G] [Finite G], AllCompositionFactorsIso T G ↔ M.mem (residual H G)

/--
Resolved true: the Kourovka Archive records 12.97 as proved (O. V. Mel'nikov, 1996): `𝔉_T` is not
the product of two non-trivial proper subformations. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 12.97 (L. A. Shemetkov); resolution: O. V. Mel'nikov, Problems
in Algebra 9, Gomel', 1996, 42-47 (Russian), Kourovka Archive, Problem 12.97: it is proved.
-/
public theorem_wanted compositionFactorFormationIndecomposable_holds :
    compositionFactorFormationIndecomposable

end MathlibExt.GroupTheory.SimpleCompositionFactorFormationKourovka12Problem97Wanted
