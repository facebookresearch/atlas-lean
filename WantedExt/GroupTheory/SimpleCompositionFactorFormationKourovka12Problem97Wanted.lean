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

/-- **Isomorphism-closed classes of groups (Kourovka 12.97).** A class of groups is given by a
membership predicate on groups such that every group isomorphic to a member is again a member.
Only the finite members matter in the formulation of Kourovka Problem 12.97. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Formations of finite groups (Kourovka 12.97).** A class $X$ of groups is a formation when it
contains the trivial group, the quotient $G/N$ lies in $X$ for every finite group $G$ in $X$ and
every normal subgroup $N$ of $G$, and for every finite group $G$ with normal subgroups $N_1$ and
$N_2$ such that $G/N_1$ and $G/N_2$ lie in $X$, the quotient $G/(N_1 \cap N_2)$ lies in $X$. -/
def IsFormation (X : GroupClass) : Prop :=
  X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- **Classes containing a nontrivial finite group.** A class $X$ of groups is nontrivial when it
contains a nontrivial finite group; for a formation this means that $X$ is not the trivial
formation. -/
def NontrivialClass (X : GroupClass) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ X.mem G

/-- **The residual of a group with respect to a class (Kourovka 12.97).** For a class $X$ of groups
and a group $G$, the $X$-residual of $G$ is the intersection of all normal subgroups $N$ of $G$
such that the quotient $G/N$ lies in $X$. -/
def residual (X : GroupClass) (G : Type) [Group G] : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : ∃ _ : N.Normal, X.mem (G ⧸ N)), N

/-- **Groups with a subnormal series whose factors are all isomorphic to a given group.** For
groups $T$ and $G$, the group $G$ lies in the class $\mathfrak{F}_T$ when it has a subnormal series
$1 = H_0 \le H_1 \le \dots \le H_n = G$, each $H_i$ normal in $H_{i+1}$, all of whose factors
$H_{i+1}/H_i$ are isomorphic to $T$. For simple $T$ these are the groups all of whose composition
factors are isomorphic to $T$. -/
def AllCompositionFactorsIso (T : Type) [Group T] (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        Nonempty ((H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ)) ≃* T)

/-- `X` is a proper subclass of `𝔉_T`: some finite group of `𝔉_T` does not belong to `X`. -/
def IsProperIn (T : Type) [Group T] (X : GroupClass) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), AllCompositionFactorsIso T G ∧ ¬ X.mem G

/-- **Kourovka Problem 12.97 (Shemetkov).** For a group $T$, write $\mathfrak{F}_T$ for the class
of groups having a subnormal series all of whose factors are isomorphic to $T$. This is the
proposition that, for every finite non-abelian simple group $T$ and all formations $\mathfrak{M}$
and $\mathfrak{H}$ whose finite members lie in $\mathfrak{F}_T$, each containing a nontrivial
finite group and each missing some finite group of $\mathfrak{F}_T$, it is not the case that every
finite group $G$ satisfies: $G \in \mathfrak{F}_T$ if and only if the $\mathfrak{H}$-residual
$G^{\mathfrak{H}}$ of $G$ lies in $\mathfrak{M}$. In other words, $\mathfrak{F}_T$ is not the
Gaschütz product $\mathfrak{M}\mathfrak{H} = \{G : G^{\mathfrak{H}} \in \mathfrak{M}\}$ of two
nontrivial proper subformations. -/
def compositionFactorFormationIndecomposable : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    ∀ M H : GroupClass, IsFormation M → IsFormation H → NontrivialClass M →
      NontrivialClass H →
      (∀ (G : Type) [Group G] [Finite G], M.mem G → AllCompositionFactorsIso T G) →
      (∀ (G : Type) [Group G] [Finite G], H.mem G → AllCompositionFactorsIso T G) →
      IsProperIn T M → IsProperIn T H →
      ¬ ∀ (G : Type) [Group G] [Finite G], AllCompositionFactorsIso T G ↔ M.mem (residual H G)

/--
**Mel'nikov's theorem on Kourovka Problem 12.97.** Let $T$ be a finite non-abelian simple group,
and write $\mathfrak{F}_T$ for the class of groups having a subnormal series all of whose factors
are isomorphic to $T$. Let $\mathfrak{M}$ and $\mathfrak{H}$ be formations whose finite members
lie in $\mathfrak{F}_T$, each containing a nontrivial finite group and each missing some finite
group of $\mathfrak{F}_T$. Then it is not true that, for every finite group $G$, $G$ lies in
$\mathfrak{F}_T$ if and only if its $\mathfrak{H}$-residual $G^{\mathfrak{H}}$ lies in
$\mathfrak{M}$: the formation $\mathfrak{F}_T$ is not the Gaschütz product
$\mathfrak{M}\mathfrak{H}$ of two nontrivial proper subformations.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 12.97 (L. A. Shemetkov); resolution: O. V. Mel'nikov, Problems
in Algebra 9, Gomel', 1996, 42-47 (Russian), Kourovka Archive, Problem 12.97: it is proved.
-/
public theorem_wanted compositionFactorFormationIndecomposable_holds :
    compositionFactorFormationIndecomposable

end MathlibExt.GroupTheory.SimpleCompositionFactorFormationKourovka12Problem97Wanted
