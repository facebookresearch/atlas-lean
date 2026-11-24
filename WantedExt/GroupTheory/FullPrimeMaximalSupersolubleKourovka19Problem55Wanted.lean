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

/-- **Supersoluble group (generator form).** A group $G$ is supersoluble when there are a natural
number $n$ and elements $g_0, \dots, g_{n-1}$ of $G$ that generate $G$ such that, for every
$i \le n$, the subgroup $G_i = \langle g_j : j < i \rangle$ is normal in $G$.

Then $1 = G_0 \le \dots \le G_n = G$ is a normal series with cyclic factors
$G_{i+1} / G_i = \langle G_i, g_i \rangle / G_i$. -/
def IsSupersoluble (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), (∀ i : ℕ, i ≤ n → (Subgroup.closure (g '' {j | j.val < i})).Normal) ∧
    Subgroup.closure (Set.range g) = ⊤

/-- **Monakhov's condition.** A group $G$ satisfies Monakhov's condition when every maximal
subgroup $M$ of $G$ with $\pi(M) = \pi(G)$ is supersoluble, where $\pi(X)$ is the set of prime
factors of the order of $X$ if $X$ is finite, and is empty if $X$ is infinite. -/
def MaximalFullPrimeSupersoluble (G : Type*) [Group G] : Prop :=
  ∀ M : Subgroup G, IsCoatom M → (Nat.card M).primeFactors = (Nat.card G).primeFactors →
    IsSupersoluble M

/-- **Chief factor of rank above a bound.** A group $G$ has a chief factor of rank greater than a
natural number $r$ when there are a chief factor $A / B$ of $G$, a prime $p$ and a natural number
$k > r$ such that the index $[A : B]$ equals $p^k$.

A chief factor of a finite soluble group is an elementary abelian $p$-group, of rank $k$ when its
order is $p^k$. -/
def HasChiefFactorRankGT (G : Type*) [Group G] (r : ℕ) : Prop :=
  ∃ A B : Subgroup G, IsChiefFactor A B ∧ ∃ p k : ℕ, p.Prime ∧ B.relIndex A = p ^ k ∧ r < k

/-- **Groups of p-length at most one.** For a natural number $p$, a group $G$ has $p$-length at
most $1$ when there are normal subgroups $N \le M$ of $G$ such that $N$ is finite of order not
divisible by $p$, the index $[M : N]$ equals $p^k$ for some natural number $k$ (an infinite index
counting as $0$), and the index $[G : M]$ is finite and not divisible by $p$.

For finite $G$ and prime $p$ this says that $N$ is a $p'$-group, $M / N$ is a $p$-group and $G / M$
is a $p'$-group. -/
def PLengthLEOne (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∃ N M : Subgroup G, N.Normal ∧ M.Normal ∧ N ≤ M ∧ ¬ p ∣ Nat.card N ∧
    (∃ k : ℕ, N.relIndex M = p ^ k) ∧ ¬ p ∣ M.index

/-- **Kourovka 19.55(a) (Monakhov): every non-abelian simple group occurs.** The proposition that
for every finite non-abelian simple group $S$ there is a finite group $G$ such that $S$ is a
composition factor of $G$ and every maximal subgroup $M$ of $G$ with $\pi(M) = \pi(G)$ is
supersoluble, where $\pi(X)$ is the set of primes dividing the order of $X$. -/
def everyNonabelianSimpleGroupOccurs : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∃ (G : Type) (_ : Group G) (_ : Finite G), MaximalFullPrimeSupersoluble G ∧
      IsCompositionFactor S G

/-- **Kourovka 19.55(b) (Monakhov): unbounded Fitting height.** The proposition that for every
natural number $h$ there is a finite soluble group $G$ whose Fitting height is greater than $h$ and
in which every maximal subgroup $M$ with $\pi(M) = \pi(G)$ is supersoluble, where $\pi(X)$ is the
set of primes dividing the order of $X$. -/
def fittingHeightUnbounded : Prop :=
  ∀ h : ℕ, ∃ (G : Type) (_ : Group G) (_ : Finite G), Group.IsSolvable G ∧
    MaximalFullPrimeSupersoluble G ∧ ¬ FittingHeightLE G h

/-- **Unbounded chief-factor rank under Monakhov's condition (the claim).** The statement that for
every natural number $r$ there is a finite soluble group $G$ satisfying Monakhov's condition
(every maximal subgroup $M$ of $G$ with $\pi(M) = \pi(G)$ is supersoluble, where $\pi(X)$ is the
set of prime divisors of $|X|$) that has a chief factor $A/B$ of order $p^k$ for some prime $p$
and some $k > r$. This is the answer to Kourovka 19.55(b) for the rank. -/
def rankUnbounded : Prop :=
  ∀ r : ℕ, ∃ (G : Type) (_ : Group G) (_ : Finite G), Group.IsSolvable G ∧
    MaximalFullPrimeSupersoluble G ∧ HasChiefFactorRankGT G r

/-- **Kourovka 19.55(b) (Monakhov): p-length at most one.** The proposition that for every finite
soluble group $G$ in which every maximal subgroup $H$ with $\pi(H) = \pi(G)$ is supersoluble,
where $\pi(X)$ is the set of primes dividing the order of $X$, and for every prime $p$, the group
$G$ has $p$-length at most $1$: there are normal subgroups $N \le M$ of $G$ such that $p$ does not
divide $|N|$, the index $[M : N]$ is a power of $p$, and $p$ does not divide $[G : M]$. -/
def pLengthAtMostOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → MaximalFullPrimeSupersoluble G →
    ∀ p : ℕ, p.Prime → PLengthLEOne G p

/--
**Moretó: every non-abelian simple group occurs in Kourovka 19.55(a).** For every finite
non-abelian simple group $S$ there is a finite group $G$ such that $S$ is a composition factor of
$G$ and every maximal subgroup $M$ of $G$ with $\pi(M) = \pi(G)$ is supersoluble, where $\pi(X)$ is
the set of primes dividing the order of $X$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.55 (V. S.
Monakhov); resolution: A. Moretó, Finite groups whose maximal subgroups of order divisible by all
the primes are supersolvable, Monatsh. Math. 195 (2021), no. 3, 497-500 (arXiv:2010.04808),
Theorem A (every nonabelian simple group occurs as a composition factor), Theorem B (solvable
examples of arbitrarily large nilpotency length and rank) and Theorem C (the p-length is 1 for every
prime divisor p of |G|); Kourovka Archive, Problem 19.55, https://arxiv.org/abs/2010.04808.
-/
public theorem_wanted everyNonabelianSimpleGroupOccurs_holds : everyNonabelianSimpleGroupOccurs

/--
**Moretó: soluble groups in Kourovka 19.55 have unbounded Fitting height.** For every natural
number $h$ there is a finite soluble group $G$ whose Fitting height is greater than $h$ and in
which every maximal subgroup $M$ with $\pi(M) = \pi(G)$ is supersoluble, where $\pi(X)$ is the set
of primes dividing the order of $X$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.55 (V. S.
Monakhov); resolution: A. Moretó, Finite groups whose maximal subgroups of order divisible by all
the primes are supersolvable, Monatsh. Math. 195 (2021), no. 3, 497-500 (arXiv:2010.04808),
Theorem A (every nonabelian simple group occurs as a composition factor), Theorem B (solvable
examples of arbitrarily large nilpotency length and rank) and Theorem C (the p-length is 1 for every
prime divisor p of |G|); Kourovka Archive, Problem 19.55, https://arxiv.org/abs/2010.04808.
-/
public theorem_wanted fittingHeightUnbounded_holds : fittingHeightUnbounded

/--
**Unbounded chief-factor rank under Monakhov's condition.** For every natural number $r$ there is
a finite soluble group $G$ such that every maximal subgroup $M$ of $G$ with $\pi(M) = \pi(G)$ is
supersoluble, where $\pi(X)$ is the set of prime divisors of $|X|$, and $G$ has a chief factor
$A/B$ (normal subgroups $B < A$ of $G$ with no normal subgroup of $G$ strictly between them) of
order $p^k$ for some prime $p$ and some $k > r$.

Moretó's groups $G_n = V_1 \cdots V_n$ (Theorem B and its proof) are such examples: their minimal
normal subgroup $V_n$, an elementary abelian chief factor, has rank tending to infinity; the
Kourovka Archive records "there is not any bound for ... the rank".

Source: E. I. Khukhro and V. D. Mazurov
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
**Moretó: soluble groups in Kourovka 19.55 have p-length at most one.** Let $G$ be a finite
soluble group in which every maximal subgroup $H$ with $\pi(H) = \pi(G)$ is supersoluble, where
$\pi(X)$ is the set of primes dividing the order of $X$. Then for every prime $p$ the group $G$ has
$p$-length at most $1$: there are normal subgroups $N \le M$ of $G$ such that $p$ does not divide
$|N|$, the index $[M : N]$ is a power of $p$, and $p$ does not divide $[G : M]$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.55 (V. S.
Monakhov); resolution: A. Moretó, Finite groups whose maximal subgroups of order divisible by all
the primes are supersolvable, Monatsh. Math. 195 (2021), no. 3, 497-500 (arXiv:2010.04808),
Theorem A (every nonabelian simple group occurs as a composition factor), Theorem B (solvable
examples of arbitrarily large nilpotency length and rank) and Theorem C (the p-length is 1 for every
prime divisor p of |G|); Kourovka Archive, Problem 19.55, https://arxiv.org/abs/2010.04808.
-/
public theorem_wanted pLengthAtMostOne_holds : pLengthAtMostOne

end MathlibExt.GroupTheory.FullPrimeMaximalSupersolubleKourovka19Problem55Wanted
