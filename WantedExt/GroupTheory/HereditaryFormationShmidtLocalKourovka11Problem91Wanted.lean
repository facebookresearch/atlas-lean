/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hereditary formations with Shmidt minimal non-members (Kourovka Notebook Problem 11.91)

Kourovka Notebook, Archive of Solved Problems, Problem 11.91 (V. N. Semenchuk): prove that a
hereditary formation `𝔉` of finite soluble groups is local if every finite soluble non-simple
minimal non-`𝔉`-group is a Shmidt group (a non-nilpotent finite group all of whose proper subgroups
are nilpotent).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.HereditaryFormationShmidtLocalKourovka11Problem91Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.91 (V. N.
Semenchuk). UnsolvedMath record UM-00700783 (`KOU-11.91`), dataset ulamai/UnsolvedMath v1.8.0.

A class of groups is a predicate on groups in `Type`. A hereditary formation of finite soluble
groups is an isomorphism-closed class of finite soluble groups closed under subgroups, quotients and
subdirect products. "Local" is stated as saturated (`G / Φ(G) ∈ 𝔉` implies `G ∈ 𝔉`, `Φ` the Frattini
subgroup): by the Gaschütz-Lubeseder theorem a nonempty formation of finite soluble groups is local
iff it is saturated, so for nonempty `𝔉` the statement is the source's. The structure also admits
the empty class, which is saturated but not local; it fails the hypothesis, since the trivial group
is then a non-simple minimal non-member that is nilpotent, so both readings hold for it vacuously. A
minimal non-`𝔉`-group is a group outside `𝔉` all of whose proper subgroups lie in `𝔉`.
-/

/-- A class of groups: a predicate on groups in `Type`. -/
abbrev GroupClass : Type 1 := ∀ (G : Type) [Group G], Prop

/-- `F` is a hereditary formation of finite soluble groups: an isomorphism-closed class of finite
soluble groups closed under subgroups, homomorphic images and subdirect products (if `G / M` and
`G / N` lie in `F`, then so does `G / (M ⊓ N)`). -/
structure IsHereditarySolubleFormation (F : GroupClass) : Prop where
  finite_solvable : ∀ (G : Type) [Group G], F G → Finite G ∧ Group.IsSolvable G
  of_mulEquiv : ∀ (G H : Type) [Group G] [Group H], (G ≃* H) → F G → F H
  subgroup : ∀ (G : Type) [Group G] (H : Subgroup G), F G → F H
  quotient : ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], F G → F (G ⧸ N)
  subdirect : ∀ (G : Type) [Group G] [Finite G] (M N : Subgroup G) [M.Normal] [N.Normal],
    F (G ⧸ M) → F (G ⧸ N) → F (G ⧸ (M ⊓ N))

/-- `F` is saturated: a finite soluble group lies in `F` whenever its quotient by the Frattini
subgroup does. For formations of finite soluble groups, saturated is the same as local
(Gaschütz-Lubeseder theorem). -/
def IsSaturated (F : GroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → F (G ⧸ frattini G) → F G

/-- `G` is a minimal non-`F`-group: `G ∉ F`, while every proper subgroup of `G` lies in `F`. -/
def IsMinimalNon (F : GroupClass) (G : Type) [Group G] : Prop :=
  ¬ F G ∧ ∀ H : Subgroup G, H ≠ ⊤ → F H

/-- `G` is a Shmidt group: a finite non-nilpotent group all of whose proper subgroups are
nilpotent. -/
def IsShmidtGroup (G : Type) [Group G] : Prop :=
  Finite G ∧ ¬ Group.IsNilpotent G ∧ ∀ H : Subgroup G, H ≠ ⊤ → Group.IsNilpotent H

/-- Kourovka 11.91 (V. N. Semenchuk): a hereditary formation `F` of finite soluble groups is local
(equivalently saturated) if every finite soluble non-simple minimal non-`F`-group is a Shmidt
group. -/
def hereditaryFormationLocalOfShmidt : Prop :=
  ∀ F : GroupClass, IsHereditarySolubleFormation F →
    (∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → ¬ IsSimpleGroup G → IsMinimalNon F G →
      IsShmidtGroup G) →
    IsSaturated F

/--
Resolved true: the Kourovka Archive records 11.91 as proved (Skiba): a hereditary formation of
finite soluble groups whose finite soluble non-simple minimal non-members are all Shmidt groups is
local, equivalently (Gaschütz-Lubeseder) saturated. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 11.91 (V. N. Semenchuk); resolution: A. N. Skiba, Dokl. Akad.
Nauk Belorus. SSR 34, no. 11 (1990), 982-985 (Russian), Kourovka Archive, Problem 11.91: "This is
proved", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted hereditaryFormationLocalOfShmidt_holds : hereditaryFormationLocalOfShmidt

end MathlibExt.GroupTheory.HereditaryFormationShmidtLocalKourovka11Problem91Wanted
