/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Permutation characters and primitivity (Kourovka Notebook Problem 6.6)

Kourovka Notebook, Archive of Solved Problems, Problem 6.6 (H. Wielandt): let P, Q be permutation
representations of a finite group G with the same character. Suppose P(G) is a primitive permutation
group. Is Q(G) necessarily primitive? The answer is known to be affirmative if G is soluble.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.GroupAction.Primitive

@[expose] public section

namespace MathlibExt.GroupTheory.PermutationCharacterPrimitivityKourovka6Problem6Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.6 (H.
Wielandt). UnsolvedMath record UM-00700353 (`KOU-6.6`), dataset ulamai/UnsolvedMath v1.8.0.

Permutation representations are actions of `G` on finite types; equal characters means equal numbers
of fixed points of every `g`. `P(G)` is primitive exactly when the action is primitive, Mathlib's
`MulAction.IsPreprimitive` (transitive with only trivial blocks).
-/

/-- Kourovka 6.6 (H. Wielandt): if two actions of a finite group `G` on finite sets have the same
permutation character (equal numbers of fixed points of every `g`) and the first is primitive, then
so is the second. -/
def samePermutationCharacterPreservesPrimitivity : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Y : Type) [Finite X] [Finite Y] [MulAction G X]
    [MulAction G Y],
    (∀ g : G, Nat.card (MulAction.fixedBy X g) = Nat.card (MulAction.fixedBy Y g)) →
    MulAction.IsPreprimitive G X → MulAction.IsPreprimitive G Y

/--
Resolved false: the Kourovka Archive answers 6.6 "No, not necessarily (mod CFSG)", citing Guralnick
and Saxl (1992): some finite group has two actions on finite sets with the same permutation
character, one primitive and the other not. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 6.6 (H. Wielandt); resolution: R. M. Guralnick and J. Saxl, Primitive
permutation characters, in: Groups, Combinatorics and Geometry (Durham, 1990), London Math. Soc.
Lecture Note Ser. 165, Cambridge Univ. Press, 1992, 364-367, zbMATH review Zbl 0828.20006: an
example of subgroups H, K of a finite group G with 1_H^G = 1_K^G, H maximal and K not maximal,
answering Wielandt's question; Kourovka Archive, Problem 6.6: No, not necessarily (mod CFSG)
(Guralnick, Saxl), https://doi.org/10.1017/CBO9780511629259.032.
-/
public theorem_wanted samePermutationCharacterPreservesPrimitivity_refuted :
    ¬ samePermutationCharacterPreservesPrimitivity

end MathlibExt.GroupTheory.PermutationCharacterPrimitivityKourovka6Problem6Wanted
