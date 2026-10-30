/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# No rank analogue of the Shepherd-Leedham-Green-McKay theorem (Kourovka Notebook Problem 16.103)

Kourovka Notebook, Archive of Solved Problems, Problem 16.103 (E. I. Khukhro): suppose that `P` is a
`2`-generator finite `p`-group whose lower central quotients `γᵢ(P)/γᵢ₊₁(P)` are cyclic for all `i ≥
2`. Is it true that `P` contains a normal subgroup `N` of nilpotency class at most `2` such that the
rank of `P/N` is bounded in terms of `p` only?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.RankAnalogueMaximalClassKourovka16Problem103Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.103 (E. I.
Khukhro). UnsolvedMath record UM-00701294 (`KOU-16.103`), dataset ulamai/UnsolvedMath v1.8.0.

The rank of a finite group is the largest minimal number of generators of a subgroup; with the
minimal number of generators of `P/N` itself the question would be trivial, `P/N` being
`2`-generated. The source asks for a bound in terms of `p` only, i.e. a bound `r(p)` for each prime.
The target asks for one prime `p` with a bound `r` (the strongest true form, existential when
refuted, as in WantedExt/Sources/UnsolvedMath.md), so its refutation asserts that no prime has such
a bound: stronger than the source's negative answer, which needs one prime, and what Khukhro proves
(his Section 4 construction fixes an arbitrary prime `p` and, for every `r` and `l`, gives such a
group with no normal subgroup of derived length at most `l` and quotient of rank at most `r`; the
examples are unbounded for any fixed prime, Introduction). Class at most `2` is `γ₃(N) = 1`; `(⊤ :
Subgroup P).lowerCentralSeries j` is `γ_{j+1}(P)`.
-/

/-- The minimal number of generators of a subgroup `H`. -/
noncomputable def minGenerators {G : Type*} [Group G] (H : Subgroup G) : ℕ :=
  sInf {n | ∃ s : Finset G, s.card = n ∧ Subgroup.closure (s : Set G) = H}

/-- The rank of a finite group: the largest minimal number of generators of its subgroups. -/
noncomputable def groupRank (G : Type*) [Group G] : ℕ :=
  sSup (Set.range (minGenerators (G := G)))

/-- The lower central factors `γᵢ(P)/γᵢ₊₁(P)` are cyclic for all `i ≥ 2`; Mathlib's
`(⊤ : Subgroup P).lowerCentralSeries j` is `γ_{j+1}(P)`. -/
def HasCyclicLowerCentralFactorsFromSecond (P : Type*) [Group P] : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∃ g ∈ (⊤ : Subgroup P).lowerCentralSeries j,
    ∀ x ∈ (⊤ : Subgroup P).lowerCentralSeries j,
      ∃ k : ℤ, x * (g ^ k)⁻¹ ∈ (⊤ : Subgroup P).lowerCentralSeries (j + 1)

/-- Kourovka 16.103 (E. I. Khukhro), for some prime `p`: there is `r` such that every `2`-generator
finite `p`-group `P` with cyclic lower central factors `γᵢ(P)/γᵢ₊₁(P)` for all `i ≥ 2` has a normal
subgroup `N` of nilpotency class at most `2` with `P/N` of rank at most `r`. -/
def rankAnalogueMaximalClass : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ r : ℕ, ∀ (P : Type) [Group P] [Finite P], IsPGroup p P →
    (∃ x y : P, Subgroup.closure ({x, y} : Set P) = ⊤) → HasCyclicLowerCentralFactorsFromSecond P →
      ∃ N : Subgroup P, ∃ _ : N.Normal, N.lowerCentralSeries 2 = ⊥ ∧ groupRank (P ⧸ N) ≤ r

/--
Resolved false: for every fixed prime `p`, Khukhro constructs `2`-generator finite `p`-groups with
cyclic lower central factors from the second on that have no normal subgroup of bounded derived
length (in particular none of class at most `2`) with quotient of bounded rank; the Kourovka Archive
answers 16.103 "No". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 16.103 (E. I. Khukhro); resolution: E. I. Khukhro, Counterexamples to a rank analogue of the
Shepherd-Leedham-Green-McKay theorem on finite p-groups of maximal class, Siberian Math. J. 54
(2013), no. 1, 174-184, Theorem (no functions r(p), l(p) give every such group a normal subgroup of
derived length at most l(p) with quotient of rank at most r(p)), with examples for every fixed prime
(Section 4); Kourovka Archive, Problem 16.103 (answer: No),
https://eprints.maths.manchester.ac.uk/1937/1/.
-/
public theorem_wanted rankAnalogueMaximalClass_refuted : ¬ rankAnalogueMaximalClass

end MathlibExt.GroupTheory.RankAnalogueMaximalClassKourovka16Problem103Wanted
