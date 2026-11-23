/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An infinite set of identities with no finite equivalent (Kourovka Notebook Problem 1.82)

Kourovka Notebook, Archive of Solved Problems, Problem 1.82 (A. L. Shmel'kin): two sets of
identities are equivalent if they determine the same variety of groups. Construct an infinite set of
identities which is not equivalent to any finite one.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.NonFinitelyBasedLawSetKourovka1Problem82Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.82 (A. L.
Shmel'kin). UnsolvedMath record UM-00700071 (`KOU-1.82`), dataset ulamai/UnsolvedMath v1.8.0.

"Construct" is formalized as existence. Identities are words in `x₀, x₁, …` (elements of `FreeGroup
ℕ`). A set `E` and a finite set `F` determine different varieties exactly when some group satisfies
all identities of one set but not all of the other; groups are taken in `Type`, which suffices
because a variety is determined by its relatively free group of countable rank. A set with no finite
equivalent is automatically infinite.
-/

/-- The group `H` satisfies the identity `w`, a word in the variables `x₀, x₁, …`: `w` evaluates to
`1` under every assignment of elements of `H` to the variables. -/
def SatisfiesLaw (H : Type*) [Group H] (w : FreeGroup ℕ) : Prop :=
  ∀ f : ℕ → H, FreeGroup.lift f w = 1

/-- Kourovka 1.82 (A. L. Shmel'kin): some set `E` of identities is not equivalent to any finite set
of identities: for every finite set `F` there is a group satisfying all identities of one of the two
sets but not all identities of the other, so `E` and `F` determine different varieties. -/
def existsNonFinitelyBasedLawSet : Prop :=
  ∃ E : Set (FreeGroup ℕ), ∀ F : Finset (FreeGroup ℕ), ∃ (H : Type) (_ : Group H),
    ¬ ((∀ w ∈ E, SatisfiesLaw H w) ↔ (∀ w ∈ F, SatisfiesLaw H w))

/--
Resolved true: the Kourovka Archive records "This was done", citing Adian (1970), who constructed
infinite systems of group identities not equivalent to any finite system. Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.82 (A. L. Shmel'kin); resolution:
S. I. Adian, Math. USSR-Izv. 4 (1970), 721-739, Kourovka Archive, Problem 1.82 ("This was done").
-/
public theorem_wanted existsNonFinitelyBasedLawSet_holds : existsNonFinitelyBasedLawSet

end MathlibExt.GroupTheory.NonFinitelyBasedLawSetKourovka1Problem82Wanted
