/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple groups with a given set of character values at an element (Kourovka Notebook Problem 11.97)

Kourovka Notebook, Archive of Solved Problems, Problem 11.97 (S. P. Strunkov): are there only
finitely many finite simple groups with a given set of all different values of irreducible
characters on a single element?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Character

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleGroupCharacterValuesKourovka11Problem97Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.97 (S. P.
Strunkov). UnsolvedMath record UM-00700789 (`KOU-11.97`), dataset ulamai/UnsolvedMath v1.8.0.

The groups are finite non-abelian simple groups: the cyclic groups of prime order all have the
single value 1 at the identity, which would refute the statement for a trivial reason, and the
Archive's answer concerns `L_2(2^m)`. The set of values at `g` is `{χ(g) : χ irreducible}`, with
irreducible characters those of the simple objects of `FDRep ℂ G`. "Finitely many" up to isomorphism
is a bound on the order.
-/

/-- **Values of the irreducible characters at an element.** For an element $g$ of a group $G$, the
set of complex numbers $\chi(g)$, where $\chi$ ranges over the characters of the irreducible
finite-dimensional complex representations of $G$. -/
def irrCharValues {G : Type} [Group G] (g : G) : Set ℂ :=
  {z | ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character g = z}

/-- **Kourovka Problem 11.97 (simple groups with a given set of character values).** The
statement that for every finite set $S$ of complex numbers there is a bound $N$ such that every
finite non-abelian simple group $G$ having an element $g$ at which the set of values of the
irreducible complex characters of $G$ is exactly $S$ has order at most $N$. The problem is due to
S. P. Strunkov.

"Only finitely many such groups" up to isomorphism is stated as this bound on the order. -/
def finitelyManySimpleGivenCharacterValues : Prop :=
  ∀ S : Set ℂ, S.Finite → ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → (∃ g : G, irrCharValues g = S) → Nat.card G ≤ N

/--
**Kourovka Problem 11.97 has a negative answer.** There is a finite set $S$ of complex numbers
such that for every natural number $N$ there is a finite non-abelian simple group $G$ with more
than $N$ elements and an element $g \in G$ at which the set of values of the irreducible complex
characters of $G$ is exactly $S$.

The Kourovka Archive records (V. D. Mazurov) that every complex irreducible character of
$L_2(2^m)$, $m \ge 2$, takes a value in $\{0, 1, -1\}$ at an involution, so some subset of
$\{0, 1, -1\}$ is the set of values at an involution for infinitely many of these non-abelian
simple groups.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.97
(S. P. Strunkov); resolution: V. D. Mazurov, Kourovka Archive, Problem 11.97: "No; all complex
irreducible characters of the groups `L_2(2^m)`, `m ≥ 2`, take the values `0, ±1` on involutions",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted finitelyManySimpleGivenCharacterValues_refuted :
    ¬ finitelyManySimpleGivenCharacterValues

end MathlibExt.GroupTheory.SimpleGroupCharacterValuesKourovka11Problem97Wanted
