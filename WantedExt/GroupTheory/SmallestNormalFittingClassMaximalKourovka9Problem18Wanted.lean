/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fitting classes maximal in the smallest normal Fitting class (Kourovka Notebook Problem 9.18)

Kourovka Notebook, Archive of Solved Problems, Problem 9.18 (H. Lausch): let `𝔖_*` be the smallest
normal Fitting class. Are there Fitting classes which are maximal in `𝔖_*` (with respect to
inclusion)?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SmallestNormalFittingClassMaximalKourovka9Problem18Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.18 (H.
Lausch). UnsolvedMath record UM-00700553 (`KOU-9.18`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of groups are the 12.96 entry's `GroupClass` (isomorphism-closed predicates on groups in
`Type`); only their finite members are used. The definitions are those of S. Reifferscheid, On the
theory of Fitting classes of finite soluble groups, Dissertation, Universität Tübingen, 2002, where
all groups are finite and soluble: a Fitting class is closed under subnormal subgroups and normal
products (Definition 1.2.1; the 12.96 entry's `IsFitting` states the equivalent closure under normal
subgroups and products of two normal subgroups); `U` is `X`-maximal in `G` if `U ∈ X` and no
`X`-subgroup of `G` properly contains `U` (Definition 1.2.3; `IsXMaximalIn`); following Blessenohl
and Gaschütz, a non-trivial Fitting class `X` is normal if the `X`-radical `G_X` is `X`-maximal in
`G` (equivalently, the `X`-injectors of `G` are normal) for every finite soluble group `G` (Chapter
3, introduction, and Definition 3.1.5); `𝔖_*` is the intersection of the Fitting classes `X` with
`X^* = 𝔖` (Section 1.2, after Theorem 1.2.9), and these are exactly the normal Fitting classes
(Theorem 3.1.3, citing Doerk-Hawkes X.3.7), so `𝔖_*` is the intersection of all normal Fitting
classes. A Fitting class maximal in `𝔖_*` is a Fitting class `X ⊊ 𝔖_*` with no Fitting class
strictly between `X` and `𝔖_*`.
-/

open MathlibExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96Wanted

/-- `X` is a Fitting class of finite soluble groups: a Fitting class of finite groups (`IsFitting`,
from the 12.96 entry: closed under normal subgroups and under products of two normal subgroups in
`X`) whose finite members are soluble. -/
def IsSolubleFittingClass (X : GroupClass) : Prop :=
  IsFitting X ∧ ∀ (G : Type) [Group G] [Finite G], X.mem G → Group.IsSolvable G

/-- `X` is a normal Fitting class (Blessenohl-Gaschütz): a Fitting class of finite soluble groups
with a non-trivial finite member such that in every finite soluble group `G` the `X`-radical `R`
(the normal subgroup in `X` that contains every normal subgroup in `X`) is `X`-maximal in `G`
(`IsXMaximalIn`, from the 12.96 entry). -/
def IsNormalFittingClass (X : GroupClass) : Prop :=
  IsSolubleFittingClass X ∧ (∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ X.mem G) ∧
    ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → ∀ R : Subgroup G, R.Normal → X.mem R →
      (∀ N : Subgroup G, N.Normal → X.mem N → N ≤ R) → IsXMaximalIn X R ⊤

/-- `G` lies in the smallest normal Fitting class `𝔖_*`, the intersection of all normal Fitting
classes (used for finite `G`). -/
def InSmallestNormalFittingClass (G : Type) [Group G] : Prop :=
  ∀ X : GroupClass, IsNormalFittingClass X → X.mem G

/-- Kourovka 9.18 (H. Lausch): some Fitting class `X` of finite soluble groups is maximal in `𝔖_*`:
the finite members of `X` lie in `𝔖_*`, some finite member of `𝔖_*` is not in `X`, and every
Fitting class `Y` of finite soluble groups with `X ⊆ Y ⊆ 𝔖_*` (on finite members) satisfies
`Y ⊆ X` or `𝔖_* ⊆ Y`. -/
def existsMaximalFittingSubclass : Prop :=
  ∃ X : GroupClass, IsSolubleFittingClass X ∧
    (∀ (G : Type) [Group G] [Finite G], X.mem G → InSmallestNormalFittingClass G) ∧
    (∃ (G : Type) (_ : Group G) (_ : Finite G), InSmallestNormalFittingClass G ∧ ¬ X.mem G) ∧
    ∀ Y : GroupClass, IsSolubleFittingClass Y →
      (∀ (G : Type) [Group G] [Finite G], X.mem G → Y.mem G) →
      (∀ (G : Type) [Group G] [Finite G], Y.mem G → InSmallestNormalFittingClass G) →
      (∀ (G : Type) [Group G] [Finite G], Y.mem G → X.mem G) ∨
        ∀ (G : Type) [Group G] [Finite G], InSmallestNormalFittingClass G → Y.mem G

/--
Resolved false: the Kourovka Archive answers 9.18 "No, there are no such classes", citing Vorob'ev:
no Fitting class is maximal in the smallest normal Fitting class `𝔖_*`. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.18 (H. Lausch); resolution: N. T.
Vorob'ev, Dokl. Akad. Nauk Belorus. SSR 35 (1991), no. 6, 485-487 (Russian), Kourovka Archive of
Solved Problems, Problem 9.18: No, there are no such classes, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted existsMaximalFittingSubclass_refuted : ¬ existsMaximalFittingSubclass

end MathlibExt.GroupTheory.SmallestNormalFittingClassMaximalKourovka9Problem18Wanted
