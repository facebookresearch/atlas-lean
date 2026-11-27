/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.GaleShapleyOneRound
public import MathlibExt.Combinatorics.Enumerative.StableMatchingHellCouples
public import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences
public import MathlibExt.Combinatorics.Enumerative.StableMatchingSoulmates

set_option autoImplicit false

namespace MetaMathlibExt

namespace StableMatchingSequences

@[expose] public section

open Finset Nat

variable {n : ℕ}

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
