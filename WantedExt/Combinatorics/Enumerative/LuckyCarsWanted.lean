/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lucky cars and lucky spots in parking functions

Statements from Steve Butler, Kimberly Hadaway, Victoria
Lenius, Preston Martens, and Marshall Moats, "Lucky Cars and
Lucky Spots in Parking Functions", *Journal of Integer
Sequences* 29 (2026), Article 26.1.1
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex>).

Parking functions are MathlibExt's
`MetaMathlibExt.IsParkingFunction n f` for
`f : Fin n → Fin n` (zero-based: car `i` and spot `j` below
are the paper's `(i+1)`-st car and `(j+1)`-st spot). The
greedy parking outcome is `parkSpots`: cars arrive in order
and each takes the least free spot at or after its preference
(`nextFreeSpot`, defaulting to the preference itself when no
spot is free, which does not occur for parking functions). Car
`i` is *lucky* when it parks in its preferred spot
(`IsLuckyCar`), spot `j` is lucky when some car preferring it
parks there, and `q n i j`, `qInc n i j`, `qDec n i j` are the
paper's `q_n(i+1, j+1)`, `q_n^i(i+1, j+1)`, `q_n^d(i+1, j+1)`:
the numbers of (all, weakly increasing, weakly decreasing)
parking functions in which car `i` prefers spot `j` and is
lucky. Counts with possibly negative exponents are stated in
`ℚ` with `zpow`.

Two records are already proved in MathlibExt and are not
restated: Proposition 8 (Pollak's partial count) is
`MetaMathlibExt.pollak_partial_parking_functions_card`, and
Corollary 19 (expected lucky spots, weakly increasing case)
is
`MetaMathlibExt.expected_lucky_spots_weakly_increasing_parking_functions`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.LuckyCarCountByCar
public import MathlibExt.Combinatorics.Enumerative.LuckyCarFactorialMoments
public import MathlibExt.Combinatorics.Enumerative.LuckyCarPrescriptions
public import MathlibExt.Combinatorics.Enumerative.LuckyCars
public import MathlibExt.Combinatorics.Enumerative.LuckyCarsIncreasing

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt Polynomial

/-- **Boundary values of lucky-car counts (Lemma 9).** Let $n \ge 1$, number the cars and spots
$0, \dots, n-1$, and let $q_n(i, j)$ be the number of parking functions of length $n$ in which
car $i$ prefers spot $j$ and is lucky. Then for all $i, j \in \{0, \dots, n-1\}$, with powers
taken in $\mathbb{Q}$ (the integer exponents may be negative),
$$q_n(n-1, j) = \binom{n-1}{j} (j+1)^{j-1} (n-j)^{n-j-2},$$
$$q_n(0, j) = \sum_{k=j+1}^{n} \binom{n-1}{k-1} k^{k-2} (n-k+1)^{n-k-1},$$
$$q_n(i, n-1) = n^{n-2},$$
$$q_n(i, 0) = (n+1)^{n-i-2}\, n^{i-1}\, (2n-i).$$

In the one-based indexing of the source, car $i$ and spot $j$ here are car $i+1$ and spot $j+1$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 9. -/
theorem_wanted q_boundary_values (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin n) :
    (q n ⟨n - 1, by omega⟩ j : ℚ) =
        Nat.choose (n - 1) j.val * ((j.val + 1 : ℚ)) ^ ((j.val : ℤ) - 1) *
          ((n - j.val : ℚ)) ^ ((n : ℤ) - j.val - 2) ∧
      (q n ⟨0, hn⟩ j : ℚ) =
        ∑ k ∈ Finset.Icc (j.val + 1) n,
          Nat.choose (n - 1) (k - 1) * ((k : ℚ)) ^ ((k : ℤ) - 2) *
            ((n - k + 1 : ℚ)) ^ ((n : ℤ) - k - 1) ∧
      (q n i ⟨n - 1, by omega⟩ : ℚ) = ((n : ℚ)) ^ ((n : ℤ) - 2) ∧
      (q n i ⟨0, hn⟩ : ℚ) =
        ((n + 1 : ℚ)) ^ ((n : ℤ) - i.val - 2) *
          ((n : ℚ)) ^ ((i.val : ℤ) - 1) * (2 * n - i.val)

/-- **Number of parking functions in which the second spot is lucky.** Number cars and spots
$0, \dots, n-1$, and let $q_n(i, j)$ be the number of parking functions of length $n$ in which
car $i$ prefers spot $j$ and parks there. Then for every $n \ge 2$, in $\mathbb{Q}$,
$$\sum_{i=0}^{n-1} q_n(i, 1) = \frac{3}{4}(n + 1)^{n-1} - \frac{1}{4}(n - 1)^{n-1}.$$
Since at most one car parks in spot $1$, the left side is the number of parking functions of
length $n$ in which the second spot is lucky, that is, the car parking there preferred it.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 12. -/
theorem_wanted sum_q_second_spot (n : ℕ) (hn : 2 ≤ n) :
    (∑ i : Fin n, (q n i ⟨1, hn⟩ : ℚ)) =
      3 / 4 * ((n + 1 : ℚ)) ^ (n - 1) -
        1 / 4 * ((n : ℚ) - 1) ^ (n - 1)

/-- **Decreasing lucky-car counts (Lemma 22).** Number the cars and spots $0, \dots, n-1$, and let
$q^{\mathrm{dec}}_n(i, j)$ be the number of weakly decreasing parking functions of length $n$ in
which car $i$ prefers spot $j$ and is lucky. For all $i, j \in \{0, \dots, n-1\}$, if $i + j < n$
then
$$q^{\mathrm{dec}}_n(i, j) = \frac{(n-i-j)^2}{(n-i)(n-j)} \binom{n-i+j-1}{j} \binom{n-j+i-1}{i},$$
and $q^{\mathrm{dec}}_n(i, j) = 0$ otherwise.

In the one-based indexing of the source the condition reads $i + j \le n + 1$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 22. -/
theorem_wanted qDec_eq (n : ℕ) (i j : Fin n) :
    (qDec n i j : ℚ) =
      if i.val + j.val < n then
        ((n - i.val - j.val : ℚ)) ^ 2 /
            ((n - i.val) * (n - j.val)) *
          Nat.choose (n - i.val + j.val - 1) j.val *
          Nat.choose (n - j.val + i.val - 1) i.val
      else 0

/-- **Lucky spots of weakly decreasing parking functions as a sum.** Number the cars and spots
$0, \dots, n-1$. For cars $i$ and spots $j$, let $q^d_n(i, j)$ be the number of weakly decreasing
parking functions $f$ of length $n$ (that is, $f(0) \ge f(1) \ge \dots \ge f(n-1)$) with
$f(i) = j$ in which car $i$ is lucky. Then for every spot $j$,
$$\sum_{i=0}^{n-1} q^d_n(i, j) = \sum_{i=1}^{n-j} \frac{(n-i-j+1)^2}{(n+1-i)(n-j)}
\binom{n-i+j}{j} \binom{n-j+i-2}{i-1}.$$

The left side counts the weakly decreasing parking functions in which spot $j$ is lucky, that
is, taken by a car that prefers it.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Corollary 23. -/
theorem_wanted card_dec_lucky_spot_eq_sum (n : ℕ) (j : Fin n) :
    (∑ i : Fin n, (qDec n i j : ℚ)) =
      ∑ i ∈ Finset.Icc 1 (n - j.val),
        ((n : ℚ) - i - j.val + 1) ^ 2 /
            ((n + 1 - i) * (n - j.val)) *
          Nat.choose (n - i + j.val) j.val *
          Nat.choose (n - j.val + i - 2) (i - 1)

/-- **Lucky spots of weakly decreasing parking functions as a Catalan convolution.** Number the
cars and spots $0, \dots, n-1$. For cars $i$ and spots $j$, let $q^d_n(i, j)$ be the number of
weakly decreasing parking functions $f$ of length $n$ (that is, $f(0) \ge f(1) \ge \dots \ge
f(n-1)$) with $f(i) = j$ in which car $i$ is lucky. Then for every spot $j$,
$$\sum_{i=0}^{n-1} q^d_n(i, j) = \sum_{k=0}^{n-j-1} C_{n-1-k} \, C_k,$$
where $C_m$ is the $m$-th Catalan number.

The left side counts the weakly decreasing parking functions in which spot $j$ is lucky, that
is, taken by a car that prefers it.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 24. -/
theorem_wanted card_dec_lucky_spot_eq_sum_catalan (n : ℕ)
    (j : Fin n) :
    (∑ i : Fin n, (qDec n i j : ℚ)) =
      ∑ k ∈ Finset.range (n - j.val),
        ((catalan (n - 1 - k) * catalan k : ℕ) : ℚ)

/-- **Expected number of lucky cars in weakly decreasing parking functions.** For $n \ge 1$, the
sum of the numbers of lucky cars over all weakly decreasing parking functions $f$ of length $n$
(those with $f(0) \ge f(1) \ge \dots \ge f(n-1)$), divided by the Catalan number $C_n$, equals
$\frac{n+1}{2}$.

There are $C_n$ weakly decreasing parking functions of length $n$, so this is the expected number
of lucky cars, which equals the expected number of lucky spots.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 25. -/
theorem_wanted expected_lucky_dec (n : ℕ) (hn : 1 ≤ n) :
    ((∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin n =>
        IsParkingFunction n f ∧ Antitone f),
      (luckyCount f : ℚ)) / (catalan n : ℚ)) =
      ((n : ℚ) + 1) / 2

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
