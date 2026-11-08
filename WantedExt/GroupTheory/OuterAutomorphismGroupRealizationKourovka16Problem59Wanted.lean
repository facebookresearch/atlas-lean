/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Every finite group as an outer automorphism group (Kourovka Notebook Problem 16.59)

Kourovka Notebook, Archive of Solved Problems, Problem 16.59 (D. MacHale): given a finite group `K`,
does there exist a finite group `G` such that `K ≅ Out G = Aut G / Inn G`? (It is known that an
infinite group `G` exists with this property.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Basic.Finite.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.OuterAutomorphismGroupRealizationKourovka16Problem59Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.59 (D.
MacHale). UnsolvedMath record UM-00701251 (`KOU-16.59`), dataset ulamai/UnsolvedMath v1.8.0.

`K ≅ Aut G / Inn G` is stated as a surjective homomorphism `Aut G → K` whose kernel is the group of
inner automorphisms (the range of `MulAut.conj`), equivalent by the first isomorphism theorem.
-/

/-- Kourovka 16.59 (D. MacHale): every finite group `K` is isomorphic to `Out(G) = Aut(G) / Inn(G)`
for some finite group `G`, stated as a surjective homomorphism `Aut(G) → K` with kernel the inner
automorphisms. -/
def everyFiniteGroupIsOuterAutomorphismGroup : Prop :=
  ∀ (K : Type) [Group K] [Finite K], ∃ (G : Type) (_ : Group G) (_ : Finite G)
    (φ : MulAut G →* K), Function.Surjective φ ∧ φ.ker = (MulAut.conj : G →* MulAut G).range

/--
Resolved true: the Kourovka Archive answers 16.59 "Yes, it does", citing Cornulier's MathOverflow
answer: for every finite group `K` there is a finite group `G` with `Out G ≅ K`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.59 (D. MacHale);
resolution: Y. Cornulier, answer to MathOverflow question 372480 (Is every finite group the outer
automorphism group of a finite group?), 2020, Kourovka Archive, Problem 16.59 (Yes, it does),
https://mathoverflow.net/questions/372480/is-every-finite-group-the-outer-automorphism-group-of-a-finite-group/372563.
-/
public theorem_wanted everyFiniteGroupIsOuterAutomorphismGroup_holds :
    everyFiniteGroupIsOuterAutomorphismGroup

end MathlibExt.GroupTheory.OuterAutomorphismGroupRealizationKourovka16Problem59Wanted
