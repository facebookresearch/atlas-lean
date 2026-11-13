/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Automorphism groups of class-two groups of prime exponent (Kourovka Notebook Problem 4.38)

Kourovka Notebook, Archive of Solved Problems, Problem 4.38 (V. D. Mazurov): classify the
composition factors of automorphism groups of finite (nilpotent of class `2`) groups of prime
exponent.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent
public import WantedExt.GroupTheory.UpperCompositionFactorsKourovka11Problem57Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismGroupCompositionFactorsKourovka4Problem38Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.38 (V. D.
Mazurov). UnsolvedMath record UM-00700246 (`KOU-4.38`), dataset ulamai/UnsolvedMath v1.8.0.

The answer recorded in the Archive, "any finite simple group can be such a composition factor", is
stated: every finite simple group `S` is a composition factor of `Aut(G)` for some finite group `G`
of prime exponent `p` (`g^p = 1`) and nilpotency class exactly `2` (`γ₃(G) = 1 ≠ γ₂(G)`, Mathlib's
`lowerCentralSeries` indexed from `γ₁ = ⊤`). A composition factor of a finite group `Q` is a simple
homomorphic image of a subnormal subgroup of `Q` (`IsCompositionFactor` of the Kourovka 11.57 entry,
reused here); the prime may depend on `S`.
-/

open MathlibExt.GroupTheory.UpperCompositionFactorsKourovka11Problem57Wanted

/-- Kourovka 4.38 (V. D. Mazurov), the answer to "classify the composition factors of the
automorphism groups of finite groups of prime exponent and nilpotency class `2`": every finite
simple group `S` is a composition factor of `Aut(G)` for some finite group `G` of prime exponent
`p` and nilpotency class exactly `2` (`γ₃(G) = 1 ≠ γ₂(G)`). -/
def everySimpleGroupCompositionFactorOfAutClassTwo : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    ∃ (p : ℕ) (G : Type) (_ : Group G) (_ : Finite G), p.Prime ∧ (∀ g : G, g ^ p = 1) ∧
      (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥ ∧ (⊤ : Subgroup G).lowerCentralSeries 1 ≠ ⊥ ∧
      IsCompositionFactor S (MulAut G)

/--
Resolved true: Beletskiĭ shows that every finite simple group is a composition factor of the
automorphism group of some finite nilpotent group of class `2` and prime exponent; the Kourovka
Archive answers 4.38 "Any finite simple group can be such a composition factor". Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.38 (V. D. Mazurov);
resolution: P. M. Beletskiĭ, The automorphism groups of finite class-two nilpotent groups with prime
exponent, Russian Math. Surveys 35 (1980), no. 6, 85-86, Kourovka Archive of Solved Problems,
Problem 4.38: Any finite simple group can be such a composition factor,
https://doi.org/10.1070/RM1980v035n06ABEH001977.
-/
public theorem_wanted everySimpleGroupCompositionFactorOfAutClassTwo_holds :
    everySimpleGroupCompositionFactorOfAutClassTwo

end MathlibExt.GroupTheory.AutomorphismGroupCompositionFactorsKourovka4Problem38Wanted
