/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sequences of the stable matching problem

Statements from Matvey Borodin, Aidan Duncan, Boyan Litchev, Jiahe Liu,
Veronika Moroz, Matthew Qian, Rohith Raghavan, Garima Rastogi, Michael Voigt,
and Tanya Khovanova, "Sequences of the Stable Matching Problem", *Journal of
Integer Sequences* 27 (2024), Article 24.2.2 (arXiv:2201.00645).

A preference profile for `n` men and `n` women is a pair `P` of families of
permutations: `P.1 i r` is the woman man `i` ranks at position `r` and
`P.2 j r` is the man woman `j` ranks at position `r`. Positions are zero-based,
so the paper's ranking `r + 1` (with `1` the favorite and `n` the least
favorite) is position `r` here. A matching is a permutation `μ` of `Fin n`:
man `i` is married to woman `μ i`.

The men-proposing Gale–Shapley algorithm is encoded by the number of women
each man has proposed to after `t` rounds (`gsProposals`). In that state a man
is provisionally engaged (`GSEngaged`) exactly when he has proposed at least
once and the woman he proposed to last ranks him above every man who has
proposed to her so far; this is the woman's held suitor in the paper's
description, since each woman keeps the best suitor proposed so far. In each
round every unengaged man proposes to his next choice, and the number of
rounds is the first `t` after which every man is engaged
(`galeShapleyRounds`).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Rat.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Matching.GaleShapley

set_option autoImplicit false

namespace MetaMathlibExt

namespace StableMatchingSequences

@[expose] public section

open Finset Nat

/-- **Preference profile for $n$ men and $n$ women.** For a natural number $n$, number $n$ men and
$n$ women by $0, \dots, n - 1$. A preference profile $P = (M, W)$ for them consists of a
permutation $M_i$ of $\{0, \dots, n - 1\}$ for each man $i$ and a permutation $W_j$ of
$\{0, \dots, n - 1\}$ for each woman $j$: $M_i(r)$ is the woman man $i$ ranks at zero-based
position $r$, and $W_j(r)$ is the man woman $j$ ranks at position $r$.

Source: Borodin, Duncan, Litchev, Liu, Moroz, Qian, Raghavan, Rastogi, Voigt,
and Khovanova, *Sequences of the Stable Matching Problem*, Journal of Integer
Sequences 27 (2024), Article 24.2.2, Section 2. -/
abbrev PreferenceProfile (n : ℕ) : Type :=
  (Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n))

variable {n : ℕ}

/-- **Rank of a woman for a man.** For a preference profile of $n$ men and $n$ women, the rank of
woman $j$ for man $i$ is the zero-based position $r \in \{0, \dots, n-1\}$ at which $i$ ranks
$j$, so his favorite has rank $0$ and his least favorite has rank $n - 1$.

The paper's one-based ranking is this rank plus one.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
def manRank (P : PreferenceProfile n) (i j : Fin n) : ℕ :=
  ((P.1 i).symm j : ℕ)

/-- **A woman's rank of a man.** For a preference profile for $n$ men and $n$ women, the rank
that woman $j$ gives man $i$ is the zero-based position at which she ranks him, that is, the
paper's ranking minus one.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
def womanRank (P : PreferenceProfile n) (j i : Fin n) : ℕ :=
  ((P.2 j).symm i : ℕ)

/-- **Soulmate pair.** For a preference profile of $n$ men and $n$ women, man $i$ and woman $j$
are soulmates when each ranks the other first: $j$ is the first choice of $i$ and $i$ is the
first choice of $j$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2.1. -/
def IsSoulmatePair (P : PreferenceProfile n) (i j : Fin n) : Prop :=
  manRank P i j = 0 ∧ womanRank P j i = 0

/-- **Number of soulmate pairs.** The number of soulmate pairs of a preference profile $P$ for
$n$ men and $n$ women is the number of pairs $(i, j)$ of a man $i$ and a woman $j$ that are
soulmates in $P$, that is, each ranks the other first.

This is the paper's $k$ in $F(k, n)$, the number of profiles with exactly $k$ soulmate pairs.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 4. -/
noncomputable def soulmatePairCount (P : PreferenceProfile n) : ℕ :=
  Nat.card {ij : Fin n × Fin n // IsSoulmatePair P ij.1 ij.2}

/-- **Men's preferences induced by rankings.** For a preference profile of $n$ men and $n$
women, each man $i$ gets the strict total order on the women in which $i$ prefers woman $a$ to
woman $b$ exactly when he ranks $a$ at an earlier position than $b$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
def manPrefs (P : PreferenceProfile n) :
    MathlibExt.Combinatorics.Matching.GaleShapley.MPrefs (Fin n) (Fin n) := fun i =>
  { lt := fun a b => manRank P i a < manRank P i b
    irrefl := fun a => lt_irrefl _
    trans := fun h1 h2 => lt_trans h1 h2
    total := fun {a b} hab => by
      rcases lt_trichotomy (manRank P i a) (manRank P i b) with h | h | h
      · exact Or.inl h
      · exact absurd ((P.1 i).symm.injective (Fin.ext h)) hab
      · exact Or.inr h }

/-- **Women's preference orders of a profile.** For a preference profile $P$ for $n$ men and $n$
women, each woman $j$ gets the strict total order on the men in which man $a$ comes before
(is preferred to) man $b$ exactly when woman $j$ ranks $a$ at an earlier position than $b$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
def womanPrefs (P : PreferenceProfile n) :
    MathlibExt.Combinatorics.Matching.GaleShapley.WPrefs (Fin n) (Fin n) := fun j =>
  { lt := fun a b => womanRank P j a < womanRank P j b
    irrefl := fun a => lt_irrefl _
    trans := fun h1 h2 => lt_trans h1 h2
    total := fun {a b} hab => by
      rcases lt_trichotomy (womanRank P j a) (womanRank P j b) with h | h | h
      · exact Or.inl h
      · exact absurd ((P.2 j).symm.injective (Fin.ext h)) hab
      · exact Or.inr h }

/-- **Stable matching.** For a preference profile of $n$ men and $n$ women, a matching $\mu$, in
which man $i$ marries woman $\mu(i)$, is stable when no man and woman both strictly prefer each
other to their own spouses. Equivalently, $\mu$ is a stable perfect matching for the strict
preferences induced by the men's and the women's rankings.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
abbrev IsStableMatching (P : PreferenceProfile n) (μ : Equiv.Perm (Fin n)) : Prop :=
  MathlibExt.Combinatorics.Matching.GaleShapley.IsStable (manPrefs P) (womanPrefs P) μ

/-- **Stability in terms of ranks.** For a preference profile of $n$ men and $n$ women, a
matching $\mu$, in which man $i$ marries woman $\mu(i)$, is stable if and only if there are no
man $i$ and woman $j$ such that $i$ ranks $j$ strictly above his wife $\mu(i)$ and $j$ ranks $i$
strictly above her husband $\mu^{-1}(j)$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
theorem isStableMatching_iff (P : PreferenceProfile n) (μ : Equiv.Perm (Fin n)) :
    IsStableMatching P μ ↔ ∀ i j : Fin n,
      ¬ (manRank P i j < manRank P i (μ i) ∧ womanRank P j i < womanRank P j (μ.symm j)) :=
  Iff.rfl

/-- **Hell-couple.** Let $P$ be a preference profile of $n$ men and $n$ women, and let $\mu$
be a matching in which man $i$ marries woman $\mu(i)$. Man $i$ and his wife $\mu(i)$ form a
hell-couple when each ranks the other last: $i$ ranks $\mu(i)$ in his last position and
$\mu(i)$ ranks $i$ in her last position.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 6.1. -/
def IsHellCouple (P : PreferenceProfile n) (μ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  manRank P i (μ i) = n - 1 ∧ womanRank P (μ i) i = n - 1

/-- **Number of Latin squares.** For $n \in \mathbb{N}$, $L_n$ is the number of Latin squares of
order $n$: families $(M_0, \dots, M_{n-1})$ of permutations of $\{0, \dots, n-1\}$ (the rows)
such that for every position $r$ the entries $M_0(r), \dots, M_{n-1}(r)$ (column $r$) are
pairwise distinct.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 4.2 (OEIS A002860). -/
noncomputable def latinSquareCount (n : ℕ) : ℕ :=
  Nat.card {M : Fin n → Equiv.Perm (Fin n) // ∀ r : Fin n, Function.Injective fun i => M i r}

/-- **Provisional engagement in the Gale–Shapley algorithm.** Let $P$ be a preference profile for
$n$ men and $n$ women, with positions in each ranking numbered $0, \dots, n - 1$, and consider
the state of the men-proposing Gale–Shapley algorithm in which each man $i'$ has proposed to the
women at the positions $r' < p(i')$ of his ranking. Man $i$ is provisionally engaged in this
state if $1 \le p(i) \le n$ and the woman $w$ at his position $p(i) - 1$ (the last woman he
proposed to) ranks him weakly above every man who has proposed to her: her position for $i$ is
at most her position for every man $i'$ who has $w$ at some position $r' < p(i')$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2 (description of the
Gale–Shapley algorithm). -/
def GSEngaged (P : PreferenceProfile n) (p : Fin n → ℕ) (i : Fin n) : Prop :=
  ∃ r : Fin n, r.val + 1 = p i ∧
    ∀ i' r' : Fin n, r'.val < p i' → P.1 i' r' = P.1 i r →
      womanRank P (P.1 i r) i ≤ womanRank P (P.1 i r) i'

open Classical in
/-- **Proposal counts in the Gale–Shapley algorithm.** Let $P$ be a preference profile for $n$ men
and $n$ women. The number $p_t(i)$ of women man $i$ has proposed to after $t$ rounds of the
men-proposing Gale–Shapley algorithm on $P$ is defined by $p_0(i) = 0$ and, for every $t$,
$p_{t+1}(i) = p_t(i)$ if man $i$ is provisionally engaged in the state $p_t$ and
$p_{t+1}(i) = p_t(i) + 1$ otherwise: in each round every man who is not provisionally engaged
proposes to his next choice.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
noncomputable def gsProposals (P : PreferenceProfile n) : ℕ → Fin n → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun i =>
      if GSEngaged P (gsProposals P t) i then gsProposals P t i else gsProposals P t i + 1

/-- **Number of Gale–Shapley rounds.** For a preference profile $P$ for $n$ men and $n$ women,
the number of rounds of the men-proposing Gale–Shapley algorithm on $P$ is the least $t$ such
that every man is provisionally engaged after $t$ rounds (or $0$ if there is no such $t$).

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
noncomputable def galeShapleyRounds (P : PreferenceProfile n) : ℕ :=
  sInf {t : ℕ | ∀ i : Fin n, GSEngaged P (gsProposals P t) i}

/-- **No proposals before the first round.** For every preference profile, after zero rounds of
the men-proposing Gale–Shapley algorithm every man has made zero proposals.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
theorem gsProposals_zero (P : PreferenceProfile n) : gsProposals P 0 = fun _ => 0 := rfl

open Classical in
/-- **One round of the Gale–Shapley algorithm.** Let $P$ be a preference profile for $n$ men and
$n$ women and let $t$ be a natural number. After $t + 1$ rounds of the men-proposing
Gale–Shapley algorithm on $P$, a man who is provisionally engaged after $t$ rounds has made as
many proposals as after $t$ rounds, and every other man has made one proposal more than after
$t$ rounds.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
theorem gsProposals_succ (P : PreferenceProfile n) (t : ℕ) (i : Fin n) :
    gsProposals P (t + 1) i =
      if GSEngaged P (gsProposals P t) i then gsProposals P t i
      else gsProposals P t i + 1 := rfl

/-- **Gale–Shapley rounds with no participants.** For the preference profile with no men and no
women, the men-proposing Gale–Shapley algorithm takes zero rounds.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
theorem galeShapleyRounds_of_zero (P : PreferenceProfile 0) : galeShapleyRounds P = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl fun i => i.elim0)

/-- **A profile has at most $n$ soulmate pairs.** Every preference profile for $n$ men and $n$
women has at most $n$ soulmate pairs, since a man's soulmate is his first choice.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 4. -/
theorem soulmatePairCount_le (P : PreferenceProfile n) : soulmatePairCount P ≤ n := by
  have h : Function.Injective
      (fun x : {ij : Fin n × Fin n // IsSoulmatePair P ij.1 ij.2} => x.1.1) := by
    rintro ⟨⟨i, j⟩, hj, -⟩ ⟨⟨i', j'⟩, hj', -⟩ (rfl : i = i')
    have : (P.1 i).symm j = (P.1 i).symm j' := Fin.ext (hj.trans hj'.symm)
    simp [(P.1 i).symm.injective this]
  simpa [soulmatePairCount] using Nat.card_le_card_of_injective _ h

/-- **Latin squares of order zero.** There is exactly one Latin square of order $0$, that is,
$L_0 = 1$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 4.2 (OEIS A002860). -/
theorem latinSquareCount_zero : latinSquareCount 0 = 1 := by
  rw [latinSquareCount, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
    ⟨⟨fun i => i.elim0, fun r => r.elim0⟩⟩⟩

/-- **Gale–Shapley rounds when all men have the same preferences.** Let $P$ be a preference
profile for $n$ men and $n$ women in which all men rank the women in the same order. Then the
men-proposing Gale–Shapley algorithm on $P$ ends in exactly $n$ rounds.

Source: Borodin, Duncan, Litchev, Liu, Moroz, Qian, Raghavan, Rastogi, Voigt,
and Khovanova, *Sequences of the Stable Matching Problem*, Journal of Integer
Sequences 27 (2024), Article 24.2.2, Proposition 1
(`jis-2024-24.2.2-prop-1`). -/
public theorem_wanted galeShapleyRounds_of_same_taste (P : PreferenceProfile n)
    (h : ∀ i i' : Fin n, P.1 i = P.1 i') :
    galeShapleyRounds P = n

/-- **When the Gale–Shapley algorithm ends in one round.** Let $n \ge 1$ and let $P$ be a
preference profile for $n$ men and $n$ women. The men-proposing Gale–Shapley algorithm on $P$ ends
in exactly one round if and only if every woman is the first choice of exactly one man.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 2
(`jis-2024-24.2.2-prop-2`). -/
public theorem_wanted galeShapleyRounds_eq_one_iff (P : PreferenceProfile n) (hn : 0 < n) :
    galeShapleyRounds P = 1 ↔ ∀ j : Fin n, ∃! i : Fin n, P.1 i ⟨0, hn⟩ = j

/-- **Counting disjoint preference profiles.** Call a preference profile for $n$ men and $n$ women
disjoint if for every pair of positions $(r, s)$ there is exactly one man–woman pair in which the
man ranks the woman at position $r$ and the woman ranks the man at position $s$. For every natural
number $n$, the number of disjoint profiles is at most $(n^2)!$ and is divisible by $(n!)^2$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 3
(`jis-2024-24.2.2-prop-3`). -/
public theorem_wanted disjoint_profiles_card_le_and_dvd (n : ℕ) :
    Nat.card {P : PreferenceProfile n //
        Function.Bijective fun ij : Fin n × Fin n => ((P.1 ij.1).symm ij.2, (P.2 ij.2).symm ij.1)} ≤
        (n ^ 2)! ∧
      (n ! ) ^ 2 ∣ Nat.card {P : PreferenceProfile n //
        Function.Bijective fun ij : Fin n × Fin n => ((P.1 ij.1).symm ij.2, (P.2 ij.2).symm ij.1)}

/-- **Outsiders without soulmate pairs.** Let $n$ and $k$ be natural numbers, where $n - k$ is
read as $0$ when $k > n$. Consider the $n - k$ men $k, \dots, n - 1$ and the $n - k$ women
$k, \dots, n - 1$ among $n$ men and $n$ women numbered from $0$, where each of these men ranks all
$n$ women and each of these women ranks all $n$ men. The number of ways to choose these rankings
so that no man and woman among them each rank the other first is
$$\sum_{i=0}^{n-k} (-1)^i \binom{n-k}{i}^2 ((n-1)!)^{2i}\, i!\, (n!)^{2(n-k-i)}.$$

This number is the paper's $S(k, n)$: the preferences of the remaining $k$ men and $k$ women are
ignored.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Lemma 4
(`jis-2024-24.2.2-lem-4`). -/
public theorem_wanted outside_no_soulmates_card (n k : ℕ) :
    (Nat.card {MW : (Fin (n - k) → Equiv.Perm (Fin n)) × (Fin (n - k) → Equiv.Perm (Fin n)) //
        ∀ a b : Fin (n - k),
          ¬ (((MW.1 a).symm ⟨k + b.val, by have := b.isLt; omega⟩ : ℕ) = 0 ∧
            ((MW.2 b).symm ⟨k + a.val, by have := a.isLt; omega⟩ : ℕ) = 0)} : ℤ) =
      ∑ i ∈ range (n - k + 1),
        (-1 : ℤ) ^ i * ((n - k).choose i : ℤ) ^ 2 * ((n - 1)! : ℤ) ^ (2 * i) * (i ! : ℤ) *
          (n ! : ℤ) ^ (2 * n - 2 * k - 2 * i)

/-- **Number of profiles with exactly $k$ soulmate pairs.** For natural numbers $n$ and $k$, the
number $F(k, n)$ of preference profiles for $n$ men and $n$ women with exactly $k$ soulmate pairs
is
$$
\binom{n}{k}^2 k!\, ((n-1)!)^{2k}
\sum_{i=0}^{n-k} (-1)^i \binom{n-k}{i}^2 ((n-1)!)^{2i}\, i!\, (n!)^{2(n-k-i)}.
$$
When $k > n$ both sides are $0$.

The sum is the paper's $S(k, n)$ of Lemma 4, which counts the preferences of the people outside
the $k$ soulmate couples that create no further soulmate pair.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Theorem 6
(`jis-2024-24.2.2-thm-6`). -/
public theorem_wanted soulmate_profiles_card (n k : ℕ) :
    (Nat.card {P : PreferenceProfile n // soulmatePairCount P = k} : ℤ) =
      (n.choose k : ℤ) ^ 2 * (k ! : ℤ) * ((n - 1)! : ℤ) ^ (2 * k) *
        ∑ i ∈ range (n - k + 1),
          (-1 : ℤ) ^ i * ((n - k).choose i : ℤ) ^ 2 * ((n - 1)! : ℤ) ^ (2 * i) * (i ! : ℤ) *
            (n ! : ℤ) ^ (2 * n - 2 * k - 2 * i)

/-- **Profiles with $n - 1$ soulmate pairs.** Let $P$ be a preference profile for $n$ men and $n$
women with exactly $n - 1$ soulmate pairs (read as $0$ when $n = 0$). Then $P$ has exactly one
stable matching. Moreover, for every stable matching $\mu$ of $P$ and every man $i$ who has no
soulmate, the men-proposing Gale–Shapley algorithm on $P$ ends after $r + 1$ rounds, where $r$ is
the zero-based position at which man $i$ ranks his wife $\mu(i)$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 7
(`jis-2024-24.2.2-prop-7`). -/
public theorem_wanted unique_stable_matching_of_soulmatePairCount_eq_pred
    (P : PreferenceProfile n) (h : soulmatePairCount P = n - 1) :
    (∃! μ : Equiv.Perm (Fin n), IsStableMatching P μ) ∧
      ∀ μ : Equiv.Perm (Fin n), IsStableMatching P μ →
        ∀ i : Fin n, (∀ j : Fin n, ¬ IsSoulmatePair P i j) →
          galeShapleyRounds P = manRank P i (μ i) + 1

/-- **Profiles with Latin-square men's preferences, counted by soulmate pairs.** For all
$n, k \in \mathbb{N}$, the number of preference profiles of $n$ men and $n$ women in which, for
every position $r$, different men rank different women at position $r$ (the men's rankings form
a Latin square), and which have exactly $k$ soulmate pairs, is
$$L_n \binom{n}{k} (n-1)^{n-k} ((n-1)!)^n,$$
where $L_n$ is the number of Latin squares of order $n$.

Here $n - 1$ and $n - k$ are truncated subtractions in $\mathbb{N}$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Theorem 8
(`jis-2024-24.2.2-thm-8`). -/
public theorem_wanted men_latin_soulmate_profiles_card (n k : ℕ) :
    Nat.card {P : PreferenceProfile n //
        (∀ r : Fin n, Function.Injective fun i => P.1 i r) ∧ soulmatePairCount P = k} =
      latinSquareCount n * n.choose k * (n - 1) ^ (n - k) * ((n - 1)!) ^ n

/-- **Mutually Latin profiles with $k$ soulmate pairs.** Let $n$ and $k$ be natural numbers and
let $L_n$ be the number of Latin squares of order $n$. Call the men's preferences of a preference
profile for $n$ men and $n$ women Latin when, for every position $r$, distinct men rank distinct
women at position $r$, and likewise for the women's preferences. The number of preference
profiles whose men's and women's preferences are both Latin and that have exactly $k$ soulmate
pairs is
$$\frac{L_n^2}{n!} \binom{n}{k} \sum_{i=0}^{n-k} \frac{(-1)^i (n-k)!}{i!}.$$
When $k > n$ the binomial coefficient vanishes and both sides are $0$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Theorem 9
(`jis-2024-24.2.2-thm-9`). -/
public theorem_wanted mutually_latin_soulmate_profiles_card (n k : ℕ) :
    (Nat.card {P : PreferenceProfile n //
        (∀ r : Fin n, Function.Injective fun i => P.1 i r) ∧
          (∀ r : Fin n, Function.Injective fun j => P.2 j r) ∧ soulmatePairCount P = k} : ℚ) =
      (latinSquareCount n : ℚ) ^ 2 / (n ! : ℚ) * (n.choose k : ℚ) *
        ∑ i ∈ range (n - k + 1), (-1 : ℚ) ^ i * ((n - k)! : ℚ) / (i ! : ℚ)

/-- **At most one hell-couple in a stable matching.** Let $P$ be a preference profile of $n$
men and $n$ women, and let $\mu$ be a stable matching for $P$, in which man $i$ marries woman
$\mu(i)$. Then at most one man $i$ forms a hell-couple with his wife $\mu(i)$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 12
(`jis-2024-24.2.2-prop-12`). -/
public theorem_wanted hellCouple_subsingleton (P : PreferenceProfile n)
    (μ : Equiv.Perm (Fin n)) (hμ : IsStableMatching P μ) :
    {i : Fin n | IsHellCouple P μ i}.Subsingleton

/-- **A hell-couple belongs to every stable matching.** Let $P$ be a preference profile for $n$
men and $n$ women and let $\mu$ and $\nu$ be stable matchings for $P$. If man $i$ and his wife
$\mu(i)$ form a hell-couple in $\mu$ (each ranks the other last), then $\nu(i) = \mu(i)$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 13
(`jis-2024-24.2.2-prop-13`). -/
public theorem_wanted hellCouple_mem_all_stable (P : PreferenceProfile n)
    (μ ν : Equiv.Perm (Fin n)) (hμ : IsStableMatching P μ) (hν : IsStableMatching P ν)
    (i : Fin n) (hi : IsHellCouple P μ i) :
    ν i = μ i

/-- **Profiles with a pair of outcasts.** In a preference profile for $n$ men and $n$ women, a man
$i$ and a woman $j$ form a pair of outcasts when every man other than $i$ ranks $j$ last and every
woman other than $j$ ranks $i$ last. The number of preference profiles with at least one pair of
outcasts is $14$ if $n = 2$ and $n^4 ((n-1)!)^{2n}$ if $n \ne 2$ (this is $0$ for $n = 0$).

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 14
(`jis-2024-24.2.2-prop-14`). -/
public theorem_wanted outcast_profiles_card (n : ℕ) :
    Nat.card {P : PreferenceProfile n // ∃ i j : Fin n,
        (∀ i' : Fin n, i' ≠ i → manRank P i' j = n - 1) ∧
          (∀ j' : Fin n, j' ≠ j → womanRank P j' i = n - 1)} =
      if n = 2 then 14 else n ^ 4 * ((n - 1)!) ^ (2 * n)

end

end StableMatchingSequences

end MetaMathlibExt
