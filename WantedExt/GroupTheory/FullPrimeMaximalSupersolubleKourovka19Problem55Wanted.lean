/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Supersoluble maximal subgroups of full prime spectrum (Kourovka Notebook Problem 19.55)

Kourovka Notebook, Archive of Solved Problems, Problem 19.55 (V. S. Monakhov): suppose that in a
finite group `G` every maximal subgroup `M` with `π(M) = π(G)` is supersoluble. (a) What are the
non-abelian composition factors of `G`? (b) Determine the exact upper bounds for the nilpotency
length, the rank, and the `p`-length of `G` if `G` is soluble.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.FullPrimeMaximalSupersolubleKourovka19Problem55Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.55 (V. S.
Monakhov). UnsolvedMath record UM-00701603 (`KOU-19.55`), dataset ulamai/UnsolvedMath v1.8.0.

Supersoluble: a normal series with cyclic factors, written with generators `g₀, …, g_{n-1}` whose
initial segments generate normal subgroups. A composition factor `S` of `G` is a simple group onto
which some subnormal subgroup of `G` maps (`IsCompositionFactor`). The nilpotency length is the
Fitting height (least length of a normal series with nilpotent factors). The rank of a soluble group
is read as the largest rank of its chief factors (Huppert's rank; a chief factor of a finite soluble
group is an elementary abelian `p`-group of order `p ^ k`, of rank `k`); in Moretó's groups `G_n =
V₁ ⋯ V_n` (proof of Theorem B) the minimal normal subgroup `V_n` is such a chief factor and its rank
tends to infinity. A chief factor of rank `k` is a section that needs `k` generators, so the target
also gives unbounded Prüfer rank (the largest number of generators a subgroup needs). `p`-length at
most `1` means normal subgroups `N ≤ M` with `N` a `p'`-group, `M / N` a `p`-group and `G / M` a
`p'`-group. The four targets give the answers: (a) every non-abelian simple group occurs; (b) the
Fitting height and the rank are unbounded and the `p`-length is at most `1`. `IsChiefFactor`,
`IsCompositionFactor` and `FittingHeightLE` are the shared definitions in
`WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- `G` is supersoluble: for some elements `g₀, …, g_{n-1}` every subgroup `Gᵢ = ⟨g_j : j < i⟩`
(`i ≤ n`) is normal in `G` and `G_n = G`, so `1 = G₀ ≤ ⋯ ≤ G_n = G` is a normal series with cyclic
factors `G_{i+1} / G_i = ⟨G_i, g_i⟩ / G_i`. -/
def IsSupersoluble (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), (∀ i : ℕ, i ≤ n → (Subgroup.closure (g '' {j | j.val < i})).Normal) ∧
    Subgroup.closure (Set.range g) = ⊤

/-- Monakhov's condition: every maximal subgroup `M` of `G` with `π(M) = π(G)` is supersoluble. -/
def MaximalFullPrimeSupersoluble (G : Type*) [Group G] : Prop :=
  ∀ M : Subgroup G, IsCoatom M → (Nat.card M).primeFactors = (Nat.card G).primeFactors →
    IsSupersoluble M

/-- `G` has a chief factor of rank greater than `r`: a chief factor `A / B` of order `p ^ k` with
`p` prime and `r < k` (a chief factor of a finite soluble group is an elementary abelian `p`-group,
of rank `k` when its order is `p ^ k`). -/
def HasChiefFactorRankGT (G : Type*) [Group G] (r : ℕ) : Prop :=
  ∃ A B : Subgroup G, IsChiefFactor A B ∧ ∃ p k : ℕ, p.Prime ∧ B.relIndex A = p ^ k ∧ r < k

/-- `G` has `p`-length at most `1`: there are normal subgroups `N ≤ M` of `G` with `N` a
`p'`-group, `M / N` a `p`-group and `G / M` a `p'`-group. -/
def PLengthLEOne (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∃ N M : Subgroup G, N.Normal ∧ M.Normal ∧ N ≤ M ∧ ¬ p ∣ Nat.card N ∧
    (∃ k : ℕ, N.relIndex M = p ^ k) ∧ ¬ p ∣ M.index

/-- Kourovka 19.55(a) (V. S. Monakhov), answer: every finite non-abelian simple group `S` is a
composition factor of some finite group satisfying Monakhov's condition. -/
def everyNonabelianSimpleGroupOccurs : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∃ (G : Type) (_ : Group G) (_ : Finite G), MaximalFullPrimeSupersoluble G ∧
      IsCompositionFactor S G

/-- Kourovka 19.55(b) (V. S. Monakhov), answer for the nilpotency length: soluble groups satisfying
Monakhov's condition have unbounded Fitting height. -/
def fittingHeightUnbounded : Prop :=
  ∀ h : ℕ, ∃ (G : Type) (_ : Group G) (_ : Finite G), Group.IsSolvable G ∧
    MaximalFullPrimeSupersoluble G ∧ ¬ FittingHeightLE G h

/-- Kourovka 19.55(b) (V. S. Monakhov), answer for the rank: soluble groups satisfying Monakhov's
condition have unbounded rank, that is, chief factors of unbounded rank. -/
def rankUnbounded : Prop :=
  ∀ r : ℕ, ∃ (G : Type) (_ : Group G) (_ : Finite G), Group.IsSolvable G ∧
    MaximalFullPrimeSupersoluble G ∧ HasChiefFactorRankGT G r

/-- Kourovka 19.55(b) (V. S. Monakhov), answer for the `p`-length: a finite soluble group satisfying
Monakhov's condition has `p`-length at most `1` for every prime `p`. -/
def pLengthAtMostOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → MaximalFullPrimeSupersoluble G →
    ∀ p : ℕ, p.Prime → PLengthLEOne G p

/--
Resolved true: Moretó (Theorem A) shows that every non-abelian finite simple group `S` is a
composition factor of a finite group with the property (a wreath product `S ≀ A_p`); the Kourovka
Archive records this answer to 19.55(a). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 19.55 (V. S. Monakhov); resolution: A. Moretó, Finite groups whose maximal
subgroups of order divisible by all the primes are supersolvable, Monatsh. Math. 195 (2021), no. 3,
497-500 (arXiv:2010.04808), Theorem A (every nonabelian simple group occurs as a composition
factor), Theorem B (solvable examples of arbitrarily large nilpotency length and rank) and Theorem C
(the p-length is 1 for every prime divisor p of |G|); Kourovka Archive, Problem 19.55,
https://arxiv.org/abs/2010.04808.
-/
public theorem_wanted everyNonabelianSimpleGroupOccurs_holds : everyNonabelianSimpleGroupOccurs

/--
Resolved true: Moretó (Theorem B) constructs soluble groups with the property of every nilpotency
length `n` (iterated semidirect products `V₁ ⋯ Vₙ`); the Kourovka Archive records "there is not any
bound for the nilpotency length". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 19.55 (V. S. Monakhov); resolution: A. Moretó, Finite groups whose maximal
subgroups of order divisible by all the primes are supersolvable, Monatsh. Math. 195 (2021), no. 3,
497-500 (arXiv:2010.04808), Theorem A (every nonabelian simple group occurs as a composition
factor), Theorem B (solvable examples of arbitrarily large nilpotency length and rank) and Theorem C
(the p-length is 1 for every prime divisor p of |G|); Kourovka Archive, Problem 19.55,
https://arxiv.org/abs/2010.04808.
-/
public theorem_wanted fittingHeightUnbounded_holds : fittingHeightUnbounded

/--
Resolved true: in Moretó's groups `G_n = V₁ ⋯ V_n` (Theorem B and its proof) the minimal normal
subgroup `V_n`, an elementary abelian chief factor, has rank tending to infinity; the Kourovka
Archive records "there is not any bound for ... the rank". Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 19.55 (V. S. Monakhov); resolution: A. Moretó, Finite
groups whose maximal subgroups of order divisible by all the primes are supersolvable, Monatsh.
Math. 195 (2021), no. 3, 497-500 (arXiv:2010.04808), Theorem A (every nonabelian simple group occurs
as a composition factor), Theorem B (solvable examples of arbitrarily large nilpotency length and
rank) and Theorem C (the p-length is 1 for every prime divisor p of |G|); Kourovka Archive, Problem
19.55, https://arxiv.org/abs/2010.04808.
-/
public theorem_wanted rankUnbounded_holds : rankUnbounded

/--
Resolved true: Moretó (Theorem C) proves that a soluble group with the property has `p`-length `1`
for every prime divisor `p` of `|G|` (and `0` for the other primes); the Kourovka Archive records
"the `p`-length is at most 1 for every prime `p`". Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 19.55 (V. S. Monakhov); resolution: A. Moretó, Finite groups
whose maximal subgroups of order divisible by all the primes are supersolvable, Monatsh. Math. 195
(2021), no. 3, 497-500 (arXiv:2010.04808), Theorem A (every nonabelian simple group occurs as a
composition factor), Theorem B (solvable examples of arbitrarily large nilpotency length and rank)
and Theorem C (the p-length is 1 for every prime divisor p of |G|); Kourovka Archive, Problem 19.55,
https://arxiv.org/abs/2010.04808.
-/
public theorem_wanted pLengthAtMostOne_holds : pLengthAtMostOne

end MathlibExt.GroupTheory.FullPrimeMaximalSupersolubleKourovka19Problem55Wanted
