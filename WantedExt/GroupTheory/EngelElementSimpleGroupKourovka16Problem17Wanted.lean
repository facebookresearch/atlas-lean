/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Engel elements in non-abelian simple groups (Kourovka Notebook Problem 16.17)

Kourovka Notebook, Archive of Solved Problems, Problem 16.17 (V. V. Bludov): is it true that a
non-abelian simple group cannot contain Engel elements other than the identity element?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.EngelElementSimpleGroupKourovka16Problem17Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.17 (V. V.
Bludov). UnsolvedMath record UM-00701209 (`KOU-16.17`), dataset ulamai/UnsolvedMath v1.8.0.

An Engel element is a (left) Engel element: `g` with `[h, g, …, g] = 1` for every `h`, the number of
`g`s depending on `h`, where `[x, g] = x⁻¹ g⁻¹ x g`. Simple is Mathlib's `IsSimpleGroup` and
non-abelian is required explicitly; groups are in `Type`.
-/

/-- `g` is an Engel element of `G`: for every `h` some iterated commutator `[h, g, …, g]` is
trivial, where `[x, g] = x⁻¹ g⁻¹ x g`. -/
def IsEngelElement {G : Type*} [Group G] (g : G) : Prop :=
  ∀ h : G, ∃ n : ℕ, (fun x => x⁻¹ * g⁻¹ * x * g)^[n] h = 1

/-- Kourovka 16.17 (V. V. Bludov): a non-abelian simple group contains no Engel element other than
the identity. -/
def simpleGroupNoNontrivialEngelElement : Prop :=
  ∀ (G : Type) [Group G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ g : G, IsEngelElement g → g = 1

/--
Resolved false: the Kourovka Archive answers 16.17 "No, it can" (Bludov): an involution is an Engel
element in any 2-group, so non-abelian simple 2-groups are counterexamples. Simple infinite 2-groups
exist by Archive 4.74(a), from the finitely generated infinite groups of exponent `2ⁿ` of Ivanov and
Lysënok and Zel'manov's solution of the restricted Burnside problem. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.17 (V. V. Bludov); resolution: V.
V. Bludov, letter of 30 March 2006, as recorded in the Kourovka Archive; infinite simple 2-groups:
Kourovka Archive, Problem 4.74(a) (S. V. Ivanov, Int. J. Algebra Comput. 4 (1994), 1-308; I. G.
Lysënok, Izv. Math. 60 (1996), 453-654; E. I. Zel'manov, Math. USSR-Sb. 72 (1992), 543-565),
Kourovka Archive, Problem 16.17 (No, it can: an involution is an Engel element in any 2-group, and
non-abelian simple 2-groups exist).
-/
public theorem_wanted simpleGroupNoNontrivialEngelElement_refuted :
    ¬ simpleGroupNoNontrivialEngelElement

end MathlibExt.GroupTheory.EngelElementSimpleGroupKourovka16Problem17Wanted
