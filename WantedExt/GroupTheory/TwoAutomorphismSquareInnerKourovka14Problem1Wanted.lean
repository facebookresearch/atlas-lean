/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Squares of 2-automorphisms centralizing a Sylow 2-subgroup (Kourovka Notebook Problem 14.1)

Kourovka Notebook, Archive of Solved Problems, Problem 14.1 (R. Zh. Aleev): let `G` be a finite
group with no nontrivial normal subgroup of odd order and `φ` a 2-automorphism of `G` centralizing a
Sylow 2-subgroup. Is `φ²` inner?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.TwoAutomorphismSquareInnerKourovka14Problem1Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.1 (R. Zh.
Aleev). UnsolvedMath record UM-00700986 (`KOU-14.1`), dataset ulamai/UnsolvedMath v1.8.0.

A 2-automorphism is an automorphism whose order is a power of `2`; "centralizing a Sylow 2-subgroup
`S`" means `φ` fixes every element of `S`. "No nontrivial normal subgroup of odd order" is `O(G) =
1`.
-/

/-- Kourovka 14.1 (R. Zh. Aleev): if a finite group `G` has no nontrivial normal subgroup of odd
order and `φ` is an automorphism of `G` of `2`-power order centralizing a Sylow `2`-subgroup of
`G`, then `φ²` is inner. -/
def twoAutomorphismCentralizingSylowSquareInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥) →
    ∀ φ : MulAut G, (∃ k : ℕ, orderOf φ = 2 ^ k) →
      (∃ S : Sylow 2 G, ∀ s ∈ (S : Subgroup G), φ s = s) → ∃ g : G, φ ^ 2 = MulAut.conj g

/--
Resolved true: the Kourovka Archive answers 14.1 "Yes, it is true", citing Glauberman: if `O(G) = 1`
and a 2-automorphism `φ` of the finite group `G` centralizes a Sylow 2-subgroup, then `φ²` is inner.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.1 (R. Zh.
Aleev); resolution: G. Glauberman, Math. Z. 107 (1968), 1-20, Kourovka Archive, Problem 14.1
(answer: Yes, it is true).
-/
public theorem_wanted twoAutomorphismCentralizingSylowSquareInner_holds :
    twoAutomorphismCentralizingSylowSquareInner

end MathlibExt.GroupTheory.TwoAutomorphismSquareInnerKourovka14Problem1Wanted
