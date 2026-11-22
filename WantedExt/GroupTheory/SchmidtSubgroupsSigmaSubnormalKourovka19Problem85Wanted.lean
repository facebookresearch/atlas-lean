/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# σ-subnormal Schmidt subgroups (Kourovka Notebook Problem 19.85)

Kourovka Notebook, Archive of Solved Problems, Problem 19.85 (A. N. Skiba): suppose that every
Schmidt subgroup of a finite group `G` is `σ`-subnormal in `G` (see Archive 19.84). Is it true that
then there is a normal `σ`-nilpotent subgroup `N ≤ G` such that `G / N` is cyclic?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.KourovkaNotebookShared
public import WantedExt.GroupTheory.SchmidtSubgroupsPrimeSubnormalKourovka18Problem30Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SchmidtSubgroupsSigmaSubnormalKourovka19Problem85Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.85 (A. N.
Skiba). UnsolvedMath record UM-00701633 (`KOU-19.85`), dataset ulamai/UnsolvedMath v1.8.0.

A partition `σ` of the primes is a family `σ : I → Set ℕ` of nonempty, pairwise disjoint sets of
primes covering all primes; a positive integer (a finite group) is `σ`-primary when its prime
divisors (those of its order) lie in one block `σᵢ`. `σ`-subnormality is the chain condition of the
Archive text of 19.84, with the quotient `Aᵢ₊₁ / (Aᵢ)_{Aᵢ₊₁}` replaced by its order, the index of
the normal core. A Schmidt subgroup is a non-nilpotent subgroup all of whose proper subgroups are
nilpotent (`IsSchmidtSubgroup` of the Kourovka 18.30 entry, reused here); a finite group is
`σ`-nilpotent when it is a direct product of `σ`-primary groups (an internal direct product of
finitely many normal `σ`-primary subgroups). `G / N` cyclic is written as `G = ⋃ₖ gᵏ N` for some
`g`. Every partition `σ` is quantified. The `σ`-definitions are the shared ones in
`WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared
open MathlibExt.GroupTheory.SchmidtSubgroupsPrimeSubnormalKourovka18Problem30Wanted
  (IsSchmidtSubgroup)

/-- **Claim of Kourovka Problem 19.85.** The statement that for every partition $\sigma$ of the set
of all primes into nonempty pairwise disjoint blocks and every finite group $G$ in which every
Schmidt subgroup is $\sigma$-subnormal, $G$ has a normal $\sigma$-nilpotent subgroup $N$ such that
$G / N$ is cyclic: there is $g \in G$ such that every $x \in G$ satisfies $x g^{-k} \in N$ for some
integer $k$. The problem is due to A. N. Skiba. -/
def schmidtSigmaSubnormalCyclicQuotient : Prop :=
  ∀ (I : Type) (σ : I → Set ℕ), IsPrimePartition σ → ∀ (G : Type) [Group G] [Finite G],
    (∀ S : Subgroup G, IsSchmidtSubgroup S → IsSigmaSubnormal σ S) →
    ∃ N : Subgroup G, N.Normal ∧ IsSigmaNilpotent σ N ∧
      ∃ g : G, ∀ x : G, ∃ k : ℤ, x * (g ^ k)⁻¹ ∈ N

/--
**Finite groups with $\sigma$-subnormal Schmidt subgroups are $\sigma$-nilpotent-by-cyclic.** Let
$\sigma$ be a partition of the set of all primes into nonempty pairwise disjoint blocks, and let $G$
be a finite group in which every Schmidt subgroup is $\sigma$-subnormal. Then $G$ has a normal
$\sigma$-nilpotent subgroup $N$ such that $G / N$ is cyclic: there is $g \in G$ such that every
$x \in G$ satisfies $x g^{-k} \in N$ for some integer $k$. This answers Kourovka Notebook
Problem 19.85 in the affirmative.

Yi and Kamornikov prove that $G / F_\sigma(G)$ is cyclic, where $F_\sigma(G)$ is the largest normal
$\sigma$-nilpotent subgroup of $G$; for nilpotent $G$ one takes $N = G$. The case of the partition
of the primes into single primes was known before.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.85 (A. N.
Skiba); resolution: X. Yi and S. F. Kamornikov, Finite groups with σ-subnormal Schmidt subgroups,
J. Algebra 560 (2020), 181-191, main result, quoted as Lemma 8 (reference [11]) in A.
Ballester-Bolinches, S. F. Kamornikov and X. Yi, Finite groups with σ-subnormal Schmidt subgroups,
Bull. Malays. Math. Sci. Soc. (2022): if every Schmidt subgroup of a non-nilpotent group G is
σ-subnormal, then G / F_σ(G) is cyclic, F_σ(G) the largest normal σ-nilpotent subgroup; Kourovka
Archive, Problem 19.85: Yes, it is true, https://doi.org/10.1007/s40840-022-01369-y.
-/
public theorem_wanted schmidtSigmaSubnormalCyclicQuotient_holds :
    schmidtSigmaSubnormalCyclicQuotient

end MathlibExt.GroupTheory.SchmidtSubgroupsSigmaSubnormalKourovka19Problem85Wanted
