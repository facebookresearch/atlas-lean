/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Original formalization by Adam Kiezun, with contributions by Metamate
(consolidation commit `f204b2a6`, PR #9859); ported with attribution.
-/

/-
# Order-preserving automorphisms of linearly ordered groups (Kourovka Notebook Problem 1.50)

Kourovka Notebook, Archive of Solved Problems, Problem 1.50 (A. I. Kokorin): do the order-preserving
automorphisms of a linearly ordered group form an orderable group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import MathlibExt.GroupTheory.Orderability

@[expose] public section

namespace MathlibExt.GroupTheory.OrderAutomorphismsOrderableKourovka1Problem50Wanted

export MathlibExt.GroupTheory (IsBiInvariantOrder IsOrderable)

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.50 (A. I.
Kokorin). UnsolvedMath record UM-00700045 (`KOU-1.50`), dataset ulamai/UnsolvedMath v1.8.0.

"Orderable" is the Kokorin-Kopytov sense of the problem list (fully ordered): `G` admits a linear
order invariant under multiplication on both sides (`IsOrderable`). A linearly ordered group is a
group with a fixed bi-invariant linear order, given by its positive cone `P` (`a ≤ b ↔ a⁻¹ * b ∈
P`). An automorphism preserves the order exactly when it maps `P` onto `P`, so the order-preserving
automorphisms form the stabilizer of `P` in `MulAut G` (pointwise action).
-/

/-- `P` is the positive cone `{g | 1 ≤ g}` of a bi-invariant linear order of `G`, the order
`a ≤ b ↔ a⁻¹ * b ∈ P`. -/
def IsOrderCone {G : Type} [Group G] (P : Set G) : Prop :=
  (∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) ∧ (∀ a ∈ P, a⁻¹ ∈ P → a = 1) ∧ (∀ a : G, a ∈ P ∨ a⁻¹ ∈ P) ∧
    ∀ g : G, ∀ a ∈ P, g * a * g⁻¹ ∈ P

open Pointwise in
/-- Kourovka 1.50 (A. I. Kokorin): for every linearly ordered group `G`, with positive cone `P`,
the group of order-preserving automorphisms of `G` (the stabilizer of `P` in `MulAut G`) is
orderable. -/
def orderAutomorphismGroupIsOrderable : Prop :=
  ∀ (G : Type) [Group G] (P : Set G), IsOrderCone P →
    IsOrderable (MulAction.stabilizer (MulAut G) P)

/--
Resolved false: the Kourovka Archive answers 1.50 "Not always", citing Smirnov (1966): the
order-preserving automorphisms of some linearly ordered group form a group that is not orderable.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.50 (A. I.
Kokorin); resolution: D. M. Smirnov, Algebra i Logika 5 (1966), no. 6, 41-60 (Russian), Kourovka
Archive, Problem 1.50 (Not always).
-/
public theorem_wanted orderAutomorphismGroupIsOrderable_refuted :
    ¬ orderAutomorphismGroupIsOrderable

private example : ProofWanted.Stmt orderAutomorphismGroupIsOrderable_refuted ↔
    ¬ orderAutomorphismGroupIsOrderable :=
  Iff.rfl

end MathlibExt.GroupTheory.OrderAutomorphismsOrderableKourovka1Problem50Wanted
