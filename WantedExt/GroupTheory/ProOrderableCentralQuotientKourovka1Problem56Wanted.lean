/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pro-orderability modulo the centre (Kourovka Notebook Problem 1.56)

Kourovka Notebook, Archive of Solved Problems, Problem 1.56 (A. I. Kokorin): is a torsion-free group
pro-orderable (see Archive 1.35) if the factor-group by its centre is pro-orderable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.ProOrderableCentralQuotientKourovka1Problem56Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.56 (A. I.
Kokorin). UnsolvedMath record UM-00700051 (`KOU-1.56`), dataset ulamai/UnsolvedMath v1.8.0.

Archive 1.35 defines a group to be pro-orderable if every partial ordering of the group extends to a
linear ordering. Partial and linear orderings of a group are compatible with multiplication on both
sides and are given by their positive cones `P` (`1 ∈ P`, `P P ⊆ P`, `P ∩ P⁻¹ = 1`, `g P g⁻¹ ⊆ P`;
linear when also `P ∪ P⁻¹ = G`). Torsion-free means no element other than `1` has finite order.
-/

/-- `P` is the positive cone `{g | 1 ≤ g}` of a partial order of `G` invariant under multiplication
on both sides, the order `a ≤ b ↔ a⁻¹ * b ∈ P`. -/
def IsPartialOrderCone {G : Type} [Group G] (P : Set G) : Prop :=
  1 ∈ P ∧ (∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) ∧ (∀ a ∈ P, a⁻¹ ∈ P → a = 1) ∧
    ∀ g : G, ∀ a ∈ P, g * a * g⁻¹ ∈ P

/-- `G` is pro-orderable (Kourovka Archive 1.35): every bi-invariant partial order of `G` extends
to a bi-invariant linear order, a positive cone `Q ⊇ P` with `a ∈ Q ∨ a⁻¹ ∈ Q` for all `a`. -/
def IsProOrderable (G : Type) [Group G] : Prop :=
  ∀ P : Set G, IsPartialOrderCone P →
    ∃ Q : Set G, IsPartialOrderCone Q ∧ (∀ a : G, a ∈ Q ∨ a⁻¹ ∈ Q) ∧ P ⊆ Q

/-- Kourovka 1.56 (A. I. Kokorin): a torsion-free group whose quotient by its centre is
pro-orderable is pro-orderable. -/
def proOrderableModCentreImpliesProOrderable : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    IsProOrderable (G ⧸ Subgroup.center G) → IsProOrderable G

/--
Resolved false: the Kourovka Archive answers 1.56 "Not always", citing Kargapolov, Kokorin and
Kopytov (1965). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
1.56 (A. I. Kokorin); resolution: M. I. Kargapolov, A. I. Kokorin and V. M. Kopytov, Algebra i
Logika 4 (1965), no. 6, 21-27 (Russian), Kourovka Archive, Problem 1.56 (Not always).
-/
public theorem_wanted proOrderableModCentreImpliesProOrderable_refuted :
    ¬ proOrderableModCentreImpliesProOrderable

end MathlibExt.GroupTheory.ProOrderableCentralQuotientKourovka1Problem56Wanted
