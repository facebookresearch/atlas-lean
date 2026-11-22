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
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt Polynomial

/-- **Next free spot.** Number the $n$ spots $0, \dots, n-1$. Given a set $S$ of occupied
spots and a spot $a$, the next free spot is the least spot $s \ge a$ with $s \notin S$; when
every spot $s \ge a$ is occupied, it is $a$ itself. -/
def nextFreeSpot {n : ℕ} (occ : Finset (Fin n)) (a : Fin n) : Fin n :=
  if h : (Finset.univ.filter (fun s : Fin n => a ≤ s ∧ s ∉ occ)).Nonempty then
    (Finset.univ.filter (fun s : Fin n => a ≤ s ∧ s ∉ occ)).min' h
  else a

/-- **Greedy parking from an occupied set.** Number the $n$ spots $0, \dots, n-1$. Given a list
$a_1, \dots, a_m$ of preferred spots and a set $S$ of occupied spots, cars $1, \dots, m$ arrive in
order and car $k$ takes the least spot at or after $a_k$ that is neither in $S$ nor taken by cars
$1, \dots, k-1$ (or $a_k$ itself if there is none). The result is the list of spots taken, in
arrival order. -/
def parkSpotsFrom {n : ℕ} : List (Fin n) → Finset (Fin n) → List (Fin n)
  | [], _ => []
  | a :: rest, occ =>
      nextFreeSpot occ a ::
        parkSpotsFrom rest (insert (nextFreeSpot occ a) occ)

/-- **Greedy parking outcome.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the
preferred spot of each of $n$ cars. Starting from an empty lot with spots $0, \dots, n-1$, cars
$0, 1, \dots, n-1$ arrive in order, and each takes the least free spot at or after its preference
(or its preference itself if there is none). The outcome sends each car $i$ to the spot it takes. -/
def parkSpots {n : ℕ} (f : Fin n → Fin n) : Fin n → Fin n :=
  fun i => (parkSpotsFrom (List.ofFn f) ∅).getD i.val i

/-- **Lucky car under greedy parking.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the
preferred spot of each of $n$ cars. Cars $0, 1, \dots, n-1$ arrive in order, and each takes the
least spot at or after its preference not taken by an earlier car, or its preferred spot itself
when there is no such spot. Car $i$ is lucky if the spot it takes is its preferred spot $f(i)$.

For a parking function a free spot always exists. -/
def IsLuckyCar {n : ℕ} (f : Fin n → Fin n) (i : Fin n) : Prop :=
  parkSpots f i = f i

/-- **Number of lucky cars.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the preferred
spot of each of $n$ cars, and let cars $0, 1, \dots, n-1$ arrive in order, each taking the least
spot at or after its preference not taken by an earlier car, or its preferred spot itself when
there is no such spot. The number of lucky cars of $f$ is the number of cars $i$ whose spot is
$f(i)$. -/
def luckyCount {n : ℕ} (f : Fin n → Fin n) : ℕ :=
  (Finset.univ.filter (fun i => decide (parkSpots f i = f i))).card

/-- **Lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q_n(i, j)$ is the number of parking functions
$f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky, that is,
parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q_n(i+1, j+1)$. -/
noncomputable def q (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ f i = j ∧ IsLuckyCar f i }

/-- **Increasing lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{inc}}_n(i, j)$ is the number of weakly increasing parking
functions $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky,
that is, parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q^i_n(i+1, j+1)$. -/
noncomputable def qInc (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ Monotone f ∧ f i = j ∧
      IsLuckyCar f i }

/-- **Decreasing lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{dec}}_n(i, j)$ is the number of weakly decreasing parking
functions $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky,
that is, parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q^d_n(i+1, j+1)$. -/
noncomputable def qDec (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ Antitone f ∧ f i = j ∧
      IsLuckyCar f i }

/-- **Lucky-car polynomial.** For $n \in \mathbb{N}$, $f_n \in \mathbb{Q}[x]$ is the polynomial
$$f_n(x) = \frac{1}{n+1} \prod_{i=0}^{n-1} \bigl((n+1-i)\,x + i\bigr).$$

Equivalently, $f_n(x) = \frac{1}{n+1} \prod_{i=1}^{n} \bigl((n+2-i)\,x + (i-1)\bigr)$. -/
noncomputable def luckyGenPoly (n : ℕ) : Polynomial ℚ :=
  C (1 / (n + 1 : ℚ)) *
    ∏ i : Fin n, (C ((n + 1 - i.val : ℕ) : ℚ) * X + C (i.val : ℚ))

/-- **Parking functions with prescribed lucky and unlucky cars.** Number the cars and spots
$0, \dots, n-1$, and let $L$ and $U$ be disjoint sets of cars. The number of parking functions
of length $n$ in which every car in $L$ is lucky and no car in $U$ is lucky equals
$$\prod_{i \in L} (n + 1 - i) \cdot \prod_{i \in U} i \cdot (n + 1)^{n - |L| - |U| - 1},$$
where the power is taken in $\mathbb{Q}$, so the exponent may be negative.

In the paper's numbering of cars from $1$, the factors are $n + 2 - i$ and $i - 1$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 4. -/
theorem_wanted card_parking_lucky_on (n : ℕ) (L U : Finset (Fin n))
    (hLU : Disjoint L U) :
    (Nat.card { f : Fin n → Fin n // IsParkingFunction n f ∧
        (∀ i ∈ L, IsLuckyCar f i) ∧
          (∀ i ∈ U, ¬ IsLuckyCar f i) } : ℚ) =
      (∏ i ∈ L, ((n + 1 - i.val : ℕ) : ℚ)) *
        (∏ i ∈ U, (i.val : ℚ)) *
        ((n + 1 : ℚ)) ^ ((n : ℤ) - L.card - U.card - 1)

/-- **Generating polynomial of lucky cars.** For $n \in \mathbb{N}$ and $0 \le k \le n$, let $c_k$
be the number of parking functions of length $n$ with exactly $k$ lucky cars. Then in
$\mathbb{Q}[x]$,
$$\frac{1}{n+1} \prod_{i=0}^{n-1} \bigl((n+1-i)x + i\bigr) = \sum_{k=0}^{n} c_k x^k.$$

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Corollary 5. -/
theorem_wanted luckyGenPoly_eq_sum (n : ℕ) :
    luckyGenPoly n =
      ∑ k ∈ Finset.range (n + 1),
        C ((Nat.card { f : Fin n → Fin n //
          IsParkingFunction n f ∧ luckyCount f = k } : ℕ) : ℚ) *
          X ^ k

/-- **Factorial moments of the number of lucky cars.** Let $n \ge 1$ and $\ell \in \mathbb{N}$, let
$X(f)$ be the number of lucky cars of a parking function $f$ of length $n$, and let
$P_n(x) = \frac{1}{n+1} \prod_{i=0}^{n-1} \bigl((n+1-i)x + i\bigr) \in \mathbb{Q}[x]$. Then
$$\frac{1}{(n+1)^{n-1}} \sum_f X(f)\bigl(X(f)-1\bigr)\cdots\bigl(X(f)-\ell+1\bigr) =
\frac{P_n^{(\ell)}(1)}{(n+1)^{n-1}},$$
where $f$ runs over the parking functions of length $n$ and $P_n^{(\ell)}$ is the $\ell$-th
derivative of $P_n$. Since there are $(n+1)^{n-1}$ parking functions of length $n$, the left side
is the $\ell$-th falling-factorial moment of $X$ for a uniformly random parking function.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Proposition 6. -/
theorem_wanted expected_descFactorial_luckyCount (n ℓ : ℕ)
    (hn : 1 ≤ n) :
    ((∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin n =>
        IsParkingFunction n f),
      ((luckyCount f).descFactorial ℓ : ℚ)) /
        (n + 1 : ℚ) ^ (n - 1) =
      (Polynomial.derivative^[ℓ] (luckyGenPoly n)).eval 1 /
        (n + 1 : ℚ) ^ (n - 1))

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

/-- **Number of parking functions in which a given car is lucky.** Number cars and spots
$0, \dots, n-1$, and let $q_n(i, j)$ be the number of parking functions of length $n$ in which
car $i$ prefers spot $j$ and parks there. Then for every $n$ and every car $i < n$,
$$\sum_{j=0}^{n-1} q_n(i, j) = (n + 1 - i)(n + 1)^{n-2},$$
an identity in $\mathbb{Q}$ (for $n = 1$ the exponent is $-1$). The left side is the number of
parking functions of length $n$ in which car $i$ is lucky; in the paper's one-based numbering
the count for the $i$-th car is $(n + 2 - i)(n + 1)^{n-2}$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Corollary 10. -/
theorem_wanted sum_q_eq (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, (q n i j : ℚ)) =
      (n + 1 - i.val : ℚ) * ((n + 1 : ℚ)) ^ ((n : ℤ) - 2)

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

/-- **Increasing lucky-car counts (Lemma 18).** Number the cars and spots $0, \dots, n-1$, let
$q^{\mathrm{inc}}_n(i, j)$ be the number of weakly increasing parking functions of length $n$ in
which car $i$ prefers spot $j$ and is lucky, and let $C_m$ be the $m$-th Catalan number. For all
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{inc}}_n(i, j) = C_i \, C_{n-i}$ if $i = j$, and
$q^{\mathrm{inc}}_n(i, j) = 0$ otherwise.

In the one-based indexing of the source the diagonal value reads $C_{i-1} C_{n-i+1}$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 18. -/
theorem_wanted qInc_eq (n : ℕ) (i j : Fin n) :
    qInc n i j =
      if i = j then catalan i.val * catalan (n - i.val)
      else 0

/-- **Ballot paths.** For $k, \ell \in \mathbb{N}$, a ballot path to $(k, \ell)$ is a word of length
$k + \ell$ in up steps and right steps with exactly $\ell$ up steps such that every prefix has at
least as many up steps as right steps; equivalently, a lattice path from $(0,0)$ to $(k, \ell)$
with unit up and right steps that stays on or above the line $y = x$. -/
def BallotPath (k ℓ : ℕ) : Type :=
  { w : List Bool // w.length = k + ℓ ∧ w.count true = ℓ ∧
    ∀ m : ℕ, m ≤ w.length →
      (w.take m).count false ≤ (w.take m).count true }

/-- **Number of ballot paths.** For natural numbers $k \le \ell$, the number of lattice paths
from $(0,0)$ to $(k, \ell)$ with unit up and right steps that stay on or above the line $y = x$
is $\frac{\ell - k + 1}{\ell + 1} \binom{k + \ell}{k}$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 21. -/
theorem_wanted card_ballotPath (k ℓ : ℕ) (h : k ≤ ℓ) :
    (Nat.card (BallotPath k ℓ) : ℚ) =
      ((ℓ - k + 1 : ℚ) / (ℓ + 1)) * Nat.choose (k + ℓ) k

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
