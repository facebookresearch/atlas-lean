/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Outer automorphism groups of centreless metabelian groups (Kourovka Notebook Problem 11.26)

Kourovka Notebook, Archive of Solved Problems, Problem 11.26 (R. Göbel): does there exist a group
that is not isomorphic to the outer automorphism group of a metabelian group with trivial centre?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.OuterAutomorphismMetabelianKourovka11Problem26Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.26 (R.
Göbel). UnsolvedMath record UM-00700719 (`KOU-11.26`), dataset ulamai/UnsolvedMath v1.8.0.

`Out(M) ≅ G` is stated without forming the quotient: some surjective homomorphism `Aut(M) → G` has
kernel the inner automorphism group (the range of `MulAut.conj`). Metabelian is `derivedSeries M 2 =
⊥`. The groups `G` and `M` live in `Type`.
-/

/-- `Out(M) ≅ G`, stated without forming the quotient: some surjective homomorphism
`Aut(M) → G` has kernel exactly the inner automorphism group `Inn(M)`. -/
def OutIsoTo (M G : Type*) [Group M] [Group G] : Prop :=
  ∃ φ : MulAut M →* G, Function.Surjective φ ∧ φ.ker = (MulAut.conj (G := M)).range

/-- Kourovka 11.26 (R. Göbel): some group is not isomorphic to the outer automorphism group of any
metabelian group with trivial centre. -/
def groupNotOuterAutOfMetabelian : Prop :=
  ∃ (G : Type) (_ : Group G), ∀ (M : Type) [Group M], derivedSeries M 2 = ⊥ →
    Subgroup.center M = ⊥ → ¬ OutIsoTo M G

/--
Resolved false: Göbel and Paras prove that every group `G` is isomorphic to `Out M` for some
metabelian group `M` with trivial centre (countable `M` for finite or countable `G`, by a second
paper of the same authors); the Kourovka Archive answers 11.26 "No". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.26 (R. Göbel); resolution: R.
Göbel and A. Paras, J. Pure Appl. Algebra 149, no. 3 (2000), 251-266, Kourovka Archive, Problem
11.26: "No, given any group `G` there is a metabelian group `M` with trivial center such that `Out M
≅ G`", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted groupNotOuterAutOfMetabelian_refuted : ¬ groupNotOuterAutOfMetabelian

end MathlibExt.GroupTheory.OuterAutomorphismMetabelianKourovka11Problem26Wanted
