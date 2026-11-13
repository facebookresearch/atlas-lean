/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Order.Lattice.Nat

/-!
# Four-digit Kaprekar dynamics in odd bases (Chen, Ono, Schwartz, Thakur)

Cycle-length and cycle-count statements from E. Chen, K. Ono, R. E. Schwartz and
D. Thakur, *Four-Digit Kaprekar Dynamics in Odd Bases*, Journal of Integer Sequences
29 (2026), Article 26.4.7.

The Kaprekar routine on a four-digit base-`B` string with sorted digits
`a₁ ≥ a₂ ≥ a₃ ≥ a₄` depends only on the difference pair `(d₁, d₂) = (a₁ - a₄, a₂ - a₃)`;
the paper works on the state space `X_B = {(d₁, d₂) : 1 ≤ d₁ < B, 0 ≤ d₂ ≤ d₁}` (constant
strings omitted) and counts terminal cycles of the induced map `K_B` there. A terminal
cycle of length `L` is a periodic orbit of `K_B` in `X_B` of minimal period `L`, so the
number of such cycles is the number of points of minimal period `L` divided by `L`.

The structural classification (Theorem 1, with Lemma 11, Lemma 14 and Proposition 16)
is already proved as `MetaMathlibExt.four_digit_kaprekar_structural_classification` in
`MathlibExt/NumberTheory/Digits/KaprekarStructuralClassification.lean`, whose
`let`-bound map `kaprekar` is the same formula as `kaprekarFourDigitStep` below.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The four-digit Kaprekar map in difference coordinates.** For a base $B$ and a pair of
natural numbers $(d_1, d_2)$, the map $K_B$ forms the list of four digits
$[d_1 - 1, B - 1, B - 1, B - d_1]$ if $d_2 = 0$ and $[d_1, d_2 - 1, B - d_2 - 1, B - d_1]$ if
$d_2 > 0$, sorts it decreasingly as $a_1 \ge a_2 \ge a_3 \ge a_4$, and sets
$K_B(d_1, d_2) = (a_1 - a_4, a_2 - a_3)$. Subtraction of natural numbers is truncated at $0$;
for $1 \le d_1 < B$ and $0 \le d_2 \le d_1$ no truncation occurs.

For such $(d_1, d_2)$ the list holds the digits of the Kaprekar difference (largest minus
smallest arrangement) of any four-digit base-$B$ string with difference coordinates
$(d_1, d_2)$, as in paper displays (5) and (6).

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Section 2.1. -/
public def kaprekarFourDigitStep (B : ℕ) (d : ℕ × ℕ) : ℕ × ℕ :=
  match List.insertionSort (· ≥ ·)
    (if d.2 = 0 then [d.1 - 1, B - 1, B - 1, B - d.1]
      else [d.1, d.2 - 1, B - d.2 - 1, B - d.1]) with
  | [a, b, c, e] => (a - e, b - c)
  | _ => (0, 0)

/-- **Sample values of the four-digit Kaprekar map.** The four-digit Kaprekar map satisfies
$K_{11}(5, 1) = (9, 1)$, $K_{11}(6, 0) = (5, 5)$ and $K_{11}(5, 5) = (2, 0)$ in base $11$, and
$K_7(3, 1) = (5, 1)$, $K_7(5, 1) = (5, 3)$ and $K_7(5, 3) = (3, 1)$ in base $7$.

In particular $(3, 1) \mapsto (5, 1) \mapsto (5, 3) \mapsto (3, 1)$ is a terminal cycle of $K_7$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Examples 7, 12 and 18. -/
public theorem kaprekarFourDigitStep_examples :
    kaprekarFourDigitStep 11 (5, 1) = (9, 1) ∧ kaprekarFourDigitStep 11 (6, 0) = (5, 5) ∧
      kaprekarFourDigitStep 11 (5, 5) = (2, 0) ∧ kaprekarFourDigitStep 7 (3, 1) = (5, 1) ∧
      kaprekarFourDigitStep 7 (5, 1) = (5, 3) ∧ kaprekarFourDigitStep 7 (5, 3) = (3, 1) := by
  simp [kaprekarFourDigitStep, List.insertionSort_cons, List.orderedInsert_cons]

/-- **The four-digit Kaprekar state space.** For a base $B$, the state space $X_B$ is the finite
set of pairs of natural numbers $(d_1, d_2)$ with $1 \le d_1 < B$ and $0 \le d_2 \le d_1$.

A nonconstant four-digit base-$B$ string with sorted digits $a_1 \ge a_2 \ge a_3 \ge a_4$ has
difference coordinates $(d_1, d_2) = (a_1 - a_4, a_2 - a_3)$, a point of $X_B$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
display (2). -/
public def kaprekarFourDigitStates (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range B ×ˢ Finset.range B).filter fun d => 1 ≤ d.1 ∧ d.2 ≤ d.1

/-- **Sizes of the Kaprekar state spaces in bases 3 and 7.** The four-digit Kaprekar state spaces
satisfy $|X_3| = 5$ and $|X_7| = 27$.

Both values agree with the general count $|X_B| = (B - 1)(B + 2)/2$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
display (2) and the proof of Corollary 27. -/
public theorem kaprekarFourDigitStates_card_examples :
    (kaprekarFourDigitStates 3).card = 5 ∧ (kaprekarFourDigitStates 7).card = 27 := by
  decide

/-- **Projective order of 2.** For a natural number $n$, the projective order of $2$ modulo $n$ is
the least $m > 0$ with $2^m \equiv 1$ or $2^m \equiv -1 \pmod{n}$,
$$\lambda(n) = \min \{m > 0 : 2^m \equiv \pm 1 \pmod{n}\},$$
and $\lambda(n) = 0$ when no such $m$ exists, which happens exactly when $n$ is even (including
$n = 0$, where congruence modulo $0$ is equality of integers). For odd $n$ these are the terms of
OEIS A003558, which lists $\lambda(2k + 1)$ at index $k$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Definition 19, display (13). -/
public noncomputable def projectiveOrderTwo (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ((2 : ZMod n) ^ m = 1 ∨ (2 : ZMod n) ^ m = -1)}

/-- **Characterization of the projective order of 2.** Let $n$ and $m$ be natural numbers with
$m > 0$. Suppose that $2^m \equiv 1$ or $2^m \equiv -1 \pmod{n}$, and that for every $k$ with
$0 < k < m$ neither $2^k \equiv 1$ nor $2^k \equiv -1 \pmod{n}$. Then the projective order of $2$
modulo $n$ is $\lambda(n) = m$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Definition 19, display (13). -/
public theorem projectiveOrderTwo_eq_of {n m : ℕ} (hm : 0 < m)
    (h : (2 : ZMod n) ^ m = 1 ∨ (2 : ZMod n) ^ m = -1)
    (hmin : ∀ k < m, 0 < k → (2 : ZMod n) ^ k ≠ 1 ∧ (2 : ZMod n) ^ k ≠ -1) :
    projectiveOrderTwo n = m := by
  unfold projectiveOrderTwo
  refine le_antisymm (Nat.sInf_le ⟨hm, h⟩) (le_csInf ⟨m, hm, h⟩ ?_)
  rintro k ⟨hk, hk2⟩
  by_contra hlt
  have hne := hmin k (lt_of_not_ge hlt) hk
  rcases hk2 with h' | h'
  · exact hne.1 h'
  · exact hne.2 h'

/-- **Values of the projective order of 2.** Writing $\lambda(n)$ for the projective order of $2$
modulo $n$, we have $\lambda(7) = 3$, $\lambda(9) = 3$, $\lambda(11) = 5$ and $\lambda(17) = 4$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Examples 7-10 and 23. -/
public theorem projectiveOrderTwo_examples :
    projectiveOrderTwo 7 = 3 ∧ projectiveOrderTwo 9 = 3 ∧ projectiveOrderTwo 11 = 5 ∧
      projectiveOrderTwo 17 = 4 :=
  ⟨projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide)⟩

/-- **Cycle lengths of doubling on pairs of projective classes.** Let $B > 3$ be odd. For
$x \in \mathbb{Z}/B\mathbb{Z}$ write $[x] = \{x, -x\}$ and $2C = \{2c : c \in C\}$ for a subset
$C$ of $\mathbb{Z}/B\mathbb{Z}$, and let $D$ be the doubling map sending a set $T$ of subsets of
$\mathbb{Z}/B\mathbb{Z}$ to $\{2C : C \in T\}$. If $S = \{[r], [s]\}$ for nonzero
$r, s \in \mathbb{Z}/B\mathbb{Z}$ with $[r] \ne [s]$, then $S$ is a periodic point of $D$ and
its minimal period is at most $\lambda(B)$, the projective order of $2$ modulo $B$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Lemma 20
(`jis-2026-26.4.7-lem-20`). -/
public theorem_wanted projective_doubling_minimalPeriod_le_projectiveOrderTwo (B : ℕ)
    (hB : Odd B) (hB3 : 3 < B) (S : Finset (Finset (ZMod B)))
    (hS : S.card = 2 ∧ ∀ C ∈ S, ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x}) :
    0 < Function.minimalPeriod
        (fun T : Finset (Finset (ZMod B)) => T.image fun C => C.image (· * 2)) S ∧
      Function.minimalPeriod
        (fun T : Finset (Finset (ZMod B)) => T.image fun C => C.image (· * 2)) S ≤
        projectiveOrderTwo B

/-- **Projective order of 2 is at most half the totient.** For every odd natural number $B > 3$,
the projective order of $2$ modulo $B$ satisfies $\lambda(B) \le \lfloor \varphi(B)/2 \rfloor$,
where $\varphi$ is Euler's totient function.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Lemma 21
(quoting Kay and Downes-Ward, Theorem 2) (`jis-2026-26.4.7-lem-21`). -/
public theorem_wanted projectiveOrderTwo_le_totient_div_two (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    projectiveOrderTwo B ≤ B.totient / 2

/-- **Long Kaprekar cycles force a prime base.** Let $B > 3$ be odd, let $K_B$ be the four-digit
Kaprekar map and $X_B$ its state space. Every point of $X_B$ that is periodic for $K_B$ has
minimal period at most $(B - 1)/2$, and if some point of $X_B$ has minimal period exactly
$(B - 1)/2$ under $K_B$, then $B$ is prime.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 22 (`jis-2026-26.4.7-cor-22`). -/
public theorem_wanted kaprekar_minimalPeriod_le_and_prime_of_eq (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    (∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
      Function.minimalPeriod (kaprekarFourDigitStep B) d ≤ (B - 1) / 2) ∧
      ((∃ d ∈ kaprekarFourDigitStates B,
          Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) → B.Prime)

/-- **Maximal Kaprekar cycle length in odd bases.** Let $B > 3$ be odd, let $K_B$ be the
four-digit Kaprekar map and $X_B$ its state space, and let $\lambda(B)$ be the projective order
of $2$ modulo $B$. Every point of $X_B$ that is periodic for $K_B$ has minimal period at most
$(B - 1)/2$. Moreover, some point of $X_B$ has minimal period exactly $(B - 1)/2$ under $K_B$
if and only if $B \ge 7$, $B$ is prime and $\lambda(B) = (B - 1)/2$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 3 (`jis-2026-26.4.7-cor-3`). -/
public theorem_wanted kaprekar_minimalPeriod_le_and_eq_iff (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    (∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
      Function.minimalPeriod (kaprekarFourDigitStep B) d ≤ (B - 1) / 2) ∧
      ((∃ d ∈ kaprekarFourDigitStates B,
          Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) ↔
        7 ≤ B ∧ B.Prime ∧ projectiveOrderTwo B = (B - 1) / 2)

/-- **Number of Kaprekar cycles of maximal length.** Let $B > 3$ be odd, let $K_B$ be the
four-digit Kaprekar map and $X_B$ its state space, and put $q = (B - 1)/2$. If some point of
$X_B$ has minimal period $q$ under $K_B$, then exactly $q \lfloor (q - 1)/2 \rfloor$ points of
$X_B$ have minimal period $q$ under $K_B$.

Equivalently, $K_B$ then has exactly $\lfloor (q - 1)/2 \rfloor$ terminal cycles of length $q$
on $X_B$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 5 (`jis-2026-26.4.7-cor-5`). -/
public theorem_wanted kaprekar_card_maximal_cycles (B : ℕ) (hB : Odd B) (hB3 : 3 < B)
    (heq : ∃ d ∈ kaprekarFourDigitStates B,
      Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) :
    ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2).card =
      (B - 1) / 2 * (((B - 1) / 2 - 1) / 2)

/-- **Explicit count of Kaprekar cycles of each length.** Let $B > 3$ be odd and $L \ge 1$, let
$K_B$ be the four-digit Kaprekar map and $X_B$ its state space, let $\varphi$ be Euler's totient
function, and let $\lambda(n)$ denote the projective order of $2$ modulo $n$. For $a \ge 1$ put
$$\mu_B(a) = \sum_{n \mid B,\ n > 1,\ \lambda(n) = a}
\left\lfloor \frac{\varphi(n)}{2a} \right\rfloor$$
and
$$N_B(L) = \mu_B(L) \left\lfloor \frac{L - 1}{2} \right\rfloor + \mu_B(2L) +
\binom{\mu_B(L)}{2} L + \sum_{a, b \mid L,\ a < b,\ \operatorname{lcm}(a, b) = L}
\mu_B(a)\, \mu_B(b) \gcd(a, b),$$
where $n$ ranges over positive divisors of $B$ and $a, b$ in the last sum range over positive
divisors of $L$. Then exactly $L \cdot N_B(L)$ points of $X_B$ have minimal period $L$ under
$K_B$.

Here $N_B(L)$ is the number of terminal cycles of length $L$ of $K_B$ on $X_B$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Theorem 24, with `μ_B` from display (14) (`jis-2026-26.4.7-thm-24`). -/
public theorem_wanted kaprekar_card_minimalPeriod_eq (B : ℕ) (hB : Odd B) (hB3 : 3 < B)
    (L : ℕ) (hL : 0 < L) :
    let μ : ℕ → ℕ := fun a =>
      ∑ n ∈ B.divisors with 1 < n ∧ projectiveOrderTwo n = a, n.totient / (2 * a)
    ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = L).card =
      L * (μ L * ((L - 1) / 2) + μ (2 * L) + (μ L).choose 2 * L +
        ∑ p ∈ (L.divisors ×ˢ L.divisors).filter (fun p => p.1 < p.2 ∧ Nat.lcm p.1 p.2 = L),
          μ p.1 * μ p.2 * Nat.gcd p.1 p.2)

/-- **At least two Kaprekar cycles whose length is the projective order of 2.** Let $\lambda(B)$
denote the projective order of $2$ modulo $B$. For every odd base $B > 17$, at least $2\lambda(B)$
points of the state space $X_B$ have minimal period exactly $\lambda(B)$ under the four-digit
Kaprekar map $K_B$.

Each terminal cycle of $K_B$ of length $\lambda(B)$ consists of $\lambda(B)$ such points, so this
says that $K_B$ has at least two terminal cycles of length $\lambda(B)$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 27 (i) (`jis-2026-26.4.7-cor-27`). -/
public theorem_wanted two_mul_projectiveOrderTwo_le_card_kaprekar_cycles (B : ℕ)
    (hB : Odd B) (hB3 : 17 < B) :
    2 * projectiveOrderTwo B ≤
      ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = projectiveOrderTwo B).card

/-- **Odd bases with a unique Kaprekar cycle.** Let $B \ge 3$ be odd, let $K_B$ be the
four-digit Kaprekar map and $X_B$ its state space. There is a point $c \in X_B$, periodic for
$K_B$, whose forward orbit $\{K_B^k(c) : k \ge 0\}$ contains every point of $X_B$ that is
periodic for $K_B$, if and only if $B \in \{3, 5, 7\}$.

That is, $K_B$ has a unique terminal cycle on $X_B$ exactly when $B$ is $3$, $5$ or $7$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 27 (ii) (`jis-2026-26.4.7-cor-27`). -/
public theorem_wanted kaprekar_unique_cycle_iff (B : ℕ) (hB : Odd B) (hB3 : 3 ≤ B) :
    (∃ c ∈ kaprekarFourDigitStates B, c ∈ Function.periodicPts (kaprekarFourDigitStep B) ∧
      ∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
        ∃ k, (kaprekarFourDigitStep B)^[k] c = d) ↔
      B = 3 ∨ B = 5 ∨ B = 7

end

end MetaMathlibExt
