/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Inner twisted classes in centreless groups (Kourovka Notebook Problem 18.15)

Kourovka Notebook, Archive of Solved Problems, Problem 18.15 (V. G. Bardakov, M. V. Neshchadim, T.
R. Nasybullov): for `φ ∈ Aut G` let `[e]_φ = {g⁻¹ g^φ | g ∈ G}`. Is it true that if a group `G` has
trivial centre, then there is an inner automorphism `φ` such that `[e]_φ` is not a subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Center

@[expose] public section

namespace MathlibExt.GroupTheory.TrivialCentreTwistedClassKourovka18Problem15Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.15 (V. G.
Bardakov, M. V. Neshchadim, T. R. Nasybullov). UnsolvedMath record UM-00701444 (`KOU-18.15`),
dataset ulamai/UnsolvedMath v1.8.0.

`G` is required to be nontrivial: the trivial group has trivial centre and `[e]_φ = {1}`, so without
this hypothesis the claim fails for a degenerate reason. Inner automorphisms are `MulAut.conj a`;
the set of inner automorphisms does not depend on the conjugation convention. Adding the hypothesis
makes the refuted claim weaker, so its refutation is the stronger statement.
-/

/-- The `φ`-twisted conjugacy class of the identity, `[e]_φ = {g⁻¹ φ(g) | g ∈ G}`. -/
def twistedUnitClass {G : Type} [Group G] (φ : G ≃* G) : Set G :=
  Set.range fun g : G => g⁻¹ * φ g

/-- Kourovka 18.15 (V. G. Bardakov, M. V. Neshchadim, T. R. Nasybullov): every nontrivial group `G`
with trivial centre has an inner automorphism `φ` (conjugation by some `a ∈ G`) such that `[e]_φ`
is not a subgroup of `G`. -/
def trivialCentreHasInnerTwistedClassNotSubgroup : Prop :=
  ∀ (G : Type) [Group G], Nontrivial G → Subgroup.center G = ⊥ →
    ∃ a : G, ¬ ∃ H : Subgroup G, (H : Set G) = twistedUnitClass (MulAut.conj a)

/--
Resolved false: the Kourovka Archive answers 18.15 "No, not always", citing V. V. Bludov's Example 2
in Gonçalves-Nasybullov (2019): a group with trivial centre in which `[e]_φ` is a subgroup for every
inner automorphism `φ`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 18.15 (V. G. Bardakov, M. V. Neshchadim, T. R. Nasybullov); resolution: V. V. Bludov,
Example 2 in D. Gonçalves and T. Nasybullov, On groups where the twisted conjugacy class of the unit
element is a subgroup, Comm. Algebra 47 (2019), no. 3, 930-944, Kourovka Archive, Problem 18.15: No,
not always; see Bludov's Example 2, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted trivialCentreHasInnerTwistedClassNotSubgroup_refuted :
    ¬ trivialCentreHasInnerTwistedClassNotSubgroup

end MathlibExt.GroupTheory.TrivialCentreTwistedClassKourovka18Problem15Wanted
