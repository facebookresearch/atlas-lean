/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.Radical.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Longest arithmetic progressions in the reduced residue systems `R_m(n)`

For integers `m` and `n > 1`, Phothila, Thoket and Kanasri study the reduced residue system
`R_m(n) = {a ∈ ℤ | m + 1 ≤ a ≤ m + n, gcd(a, n) = 1}` modulo `n`, the length `f_m(n)` of the
longest arithmetic progressions contained in it, the length `f_m(d, n)` of the longest ones
with common difference `d`, and `g(n) = f_{-⌈n/2⌉}(n)` for the system of absolute least
reduced residues. Throughout, `gpf(n)` is written `n.primeFactors.sup id` (the largest prime
factor of `n` for `n > 1`) and `rad(n)` is `UniqueFactorizationMonoid.radical n`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

@[expose] public section

open UniqueFactorizationMonoid

/-- **The reduced residue system $R_m(n)$.** For an integer $m$ and a natural number $n$, the
reduced residue system $R_m(n)$ modulo $n$ is the finite set
$R_m(n) = \{a \in \mathbb{Z} : m + 1 \le a \le m + n,\ \gcd(a, n) = 1\}$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public def reducedResidueWindow (m : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.Icc (m + 1) (m + n)).filter fun a => Int.gcd a n = 1

/-- **Longest progression with a given common difference.** For an integer $m$ and natural numbers
$n$ and $d$, let $R_m(n)$ be the set of integers $a$ with $m + 1 \le a \le m + n$ and
$\gcd(a, n) = 1$. Then $f_m(d, n)$ is the supremum of the natural numbers $s$ for which some
integer $b$ has $b + i d \in R_m(n)$ for every natural number $i < s$. For $d > 0$ every such $s$
is at most $n$, so $f_m(d, n)$ is the length of the longest arithmetic progression with common
difference $d$ contained in $R_m(n)$; the paper uses it only for $d > 0$, and for $d = 0$ the
definition gives $0$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 2. -/
public noncomputable def longestAPLengthWithDiff (m : ℤ) (n d : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ b : ℤ, ∀ i < s, b + i * d ∈ reducedResidueWindow m n}

/-- **Length of the longest arithmetic progression in a reduced residue system.** For an
integer $m$ and a natural number $n$, let $R_m(n)$ be the reduced residue system of the
integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$. Then $f_m(n)$ is the largest
natural number $s$ for which there are an integer $b$ and a positive integer $d$ such that
$b, b + d, \dots, b + (s - 1)d$ all lie in $R_m(n)$. So it is the length of the longest
arithmetic progression with positive common difference contained in $R_m(n)$, where a single
term counts as a progression of length $1$, and $f_m(n) = 0$ when $R_m(n)$ is empty.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public noncomputable def longestAPLength (m : ℤ) (n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ b : ℤ, ∃ d : ℕ, 0 < d ∧ ∀ i < s, b + i * d ∈ reducedResidueWindow m n}

/-- **Longest progression in the absolute least reduced residues.** For a natural number $n$,
let $R(n)$ be the set of integers $a$ with $1 - \lceil n/2 \rceil \le a \le n - \lceil n/2 \rceil$
and $\gcd(a, n) = 1$, the system of absolute least reduced residues modulo $n$. Then $g(n)$ is
the largest $s \ge 0$ for which there are an integer $b$ and a positive integer $d$ with
$b + i d \in R(n)$ for every $0 \le i < s$: the length of the longest arithmetic progression
with positive common difference contained in $R(n)$. Equivalently,
$g(n) = f_{-\lceil n/2 \rceil}(n)$, where $f_m(n)$ is the same length for the set
$R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public noncomputable def absLeastAPLength (n : ℕ) : ℕ :=
  longestAPLength (-⌈(n : ℚ) / 2⌉) n

/-- **Length bound for progressions in a reduced residue window.** Let $m$ be an integer and $n$
a natural number, and let $R_m(n)$ be the set of integers $a$ with $m + 1 \le a \le m + n$ and
$\gcd(a, n) = 1$. If $b$ is an integer, $d$ a positive integer and $s$ a natural number such
that $b + i d \in R_m(n)$ for every $0 \le i < s$, then $s \le n$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6 (`R_m(n) ⊆ [m + 1, m + n]`). -/
public theorem apLength_le {m b : ℤ} {n d s : ℕ} (hd : 0 < d)
    (h : ∀ i < s, b + i * d ∈ reducedResidueWindow m n) : s ≤ n := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact Nat.zero_le _
  have h0 := h 0 hs
  have h1 := h (s - 1) (by omega)
  simp only [reducedResidueWindow, Finset.mem_filter, Finset.mem_Icc] at h0 h1
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hs' : ((s - 1 : ℕ) : ℤ) ≤ ((s - 1 : ℕ) : ℤ) * d :=
    le_mul_of_one_le_right (by positivity) hd'
  have : ((s - 1 : ℕ) : ℤ) ≤ n - 1 := by
    have := h0.1.1; have := h1.1.2; push_cast at *; linarith
  omega

/-- **The longest progression length is at most the modulus.** For every integer $m$ and natural
number $n$, $f_m(n) \le n$, where $f_m(n)$ is the length of the longest arithmetic progression
with positive common difference contained in the set $R_m(n)$ of integers $a$ with
$m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6 (`R_m(n)` has at most `n`
elements). -/
public theorem longestAPLength_le (m : ℤ) (n : ℕ) : longestAPLength m n ≤ n :=
  csSup_le' fun _ ⟨_, _, hd, h⟩ => apLength_le hd h

/-- **The reduced residue system $R_{-3}(5)$.** The reduced residue system $R_{-3}(5)$ of the
integers $a$ with $-2 \le a \le 2$ and $\gcd(a, 5) = 1$ is $\{-2, -1, 1, 2\}$: an integer $a$
lies in $R_{-3}(5)$ if and only if $a$ is one of $-2$, $-1$, $1$, $2$.

Since $\lceil 5/2 \rceil = 3$, this is the system $R(5) = R_{-\lceil 5/2 \rceil}(5)$ of absolute
least reduced residues modulo $5$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Example 1(i). -/
public theorem mem_reducedResidueWindow_neg_three_five (a : ℤ) :
    a ∈ reducedResidueWindow (-3) 5 ↔ a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 := by
  simp only [reducedResidueWindow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    norm_num at h1 h2
    interval_cases a <;> simp_all
  · rintro (rfl | rfl | rfl | rfl) <;> decide

/-- **Longest progressions of absolute least residues modulo 5.** The length $g(5)$ of the
longest arithmetic progression in the absolute least reduced residue system modulo $5$ is $2$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Example 1(i). -/
public theorem absLeastAPLength_five : absLeastAPLength 5 = 2 := by
  have hc : (-⌈((5 : ℕ) : ℚ) / 2⌉ : ℤ) = -3 := by
    rw [neg_inj, Int.ceil_eq_iff]; norm_num
  unfold absLeastAPLength longestAPLength
  rw [hc]
  apply le_antisymm
  · apply csSup_le'
    rintro s ⟨b, d, hd, h⟩
    by_contra hs
    have h0 := (mem_reducedResidueWindow_neg_three_five _).1 (h 0 (by omega))
    have h1 := (mem_reducedResidueWindow_neg_three_five _).1 (h 1 (by omega))
    have h2 := (mem_reducedResidueWindow_neg_three_five _).1 (h 2 (by omega))
    push_cast at h0 h1 h2
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    omega
  · refine le_csSup ⟨5, fun s ⟨b, d, hd, h⟩ => apLength_le hd h⟩ ⟨-2, 1, one_pos, ?_⟩
    intro i hi
    rw [mem_reducedResidueWindow_neg_three_five]
    interval_cases i <;> norm_num

/-- **Prime bound for progressions with a fixed difference.** Let $m$ be an integer, $n > 1$ and
$d > 0$ natural numbers, and $p$ a prime that divides $n$ but not $d$. Then $f_m(d, n) \le p - 1$,
where $f_m(d, n)$ is the length of the longest arithmetic progression with common difference $d$
contained in the set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Lemma 1(i) (`integers-2026-A6-lem-1`). -/
public theorem_wanted longestAPLengthWithDiff_le_prime_sub_one (m : ℤ) {n d p : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hp : p.Prime) (hpn : p ∣ n) (hpd : ¬ p ∣ d) :
    longestAPLengthWithDiff m n d ≤ p - 1

/-- **Squarefree bound for progressions with a fixed difference.** Let $m$ be an integer, $n > 1$
a squarefree natural number with largest prime factor $\operatorname{gpf}(n)$, and $d > 0$ a
natural number. Then $f_m(d, n) \le \operatorname{gpf}(n) - 1$, where $f_m(d, n)$ is the length of
the longest arithmetic progression with common difference $d$ contained in the set $R_m(n)$ of
integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Lemma 1(ii) (`integers-2026-A6-lem-1`). -/
public theorem_wanted longestAPLengthWithDiff_le_gpf_sub_one_of_squarefree (m : ℤ) {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hsq : Squarefree n) :
    longestAPLengthWithDiff m n d ≤ n.primeFactors.sup id - 1

/-- **Longest progressions of absolute least residues: primes congruent to 1 mod 4.** For a
prime $p \equiv 1 \pmod 4$, the length $g(p)$ of the longest arithmetic progression in the
absolute least reduced residue system modulo $p$ is $(p - 1)/2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 1) : absLeastAPLength p = (p - 1) / 2

/-- **Longest progressions of absolute least residues: primes congruent to 3 mod 4.** For a
prime $p \equiv 3 \pmod 4$, the length $g(p)$ of the longest arithmetic progression in the
absolute least reduced residue system modulo $p$ is $(p + 1)/2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_of_mod_four_eq_three {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 3) : absLeastAPLength p = (p + 1) / 2

/-- **Longest progressions of absolute least residues: prime powers.** Let $p$ be a prime and
$r \ge 1$, with $r \ge 2$ when $p$ is odd. Then the length $g(p^r)$ of the longest arithmetic
progression in the absolute least reduced residue system modulo $p^r$ is $p^{r-1}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (h : p = 2 ∨ 2 ≤ r) : absLeastAPLength (p ^ r) = p ^ (r - 1)

/-- **Longest progressions of absolute least residues: odd squarefree composite moduli.** Let
$n > 1$ be an odd squarefree natural number that is not prime, let $P$ be its largest prime
factor and $d = n / P$, and let $g(n)$ be the length of the longest arithmetic progression in the
absolute least reduced residue system modulo $n$. Then
$g(n) = \lfloor P - (P + 1)/(2d) \rfloor$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_odd_squarefree {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hsq : Squarefree n) (hnp : ¬ n.Prime) :
    (absLeastAPLength n : ℤ) =
      ⌊((n.primeFactors.sup id : ℕ) : ℚ) -
        ((n.primeFactors.sup id : ℕ) + 1) / (2 * ((n / n.primeFactors.sup id : ℕ) : ℚ))⌋

/-- **Longest progressions of absolute least residues: twice an odd prime.** For an odd prime
$p$, the length $g(2p)$ of the longest arithmetic progression in the absolute least reduced
residue system modulo $2p$ is $p - 1$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_two_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    absLeastAPLength (2 * p) = p - 1

/-- **Longest progressions of absolute least residues: neither squarefree nor prime power.** Let
$n > 1$ be a natural number that is neither squarefree nor a prime power, let
$\operatorname{rad}(n)$ be the product of the distinct primes dividing $n$ and $P$ the largest
prime factor of $n$, and let $g(n)$ be the length of the longest arithmetic progression in the
absolute least reduced residue system modulo $n$. Then
$g(n) = \max(n / \operatorname{rad}(n), P - 1)$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_of_not_squarefree_of_not_isPrimePow {n : ℕ} (hn : 1 < n)
    (hsq : ¬ Squarefree n) (hpp : ¬ IsPrimePow n) :
    absLeastAPLength n = max (n / radical n) (n.primeFactors.sup id - 1)

/-- **Longest progressions of absolute least residues: even squarefree, three or more primes.**
Let $n$ be an even squarefree natural number with at least three prime factors, let $P$ be its
largest prime factor and $d = n / P$, and let $g(n)$ be the length of the longest arithmetic
progression in the absolute least reduced residue system modulo $n$. Then
$\lfloor P - 2P/d \rfloor \le g(n) \le P - 1$, and if $d \ge 2P$ then $g(n) = P - 1$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_even_squarefree_bounds {n : ℕ} (heven : Even n)
    (hsq : Squarefree n) (h3 : 3 ≤ n.primeFactors.card) :
    (⌊((n.primeFactors.sup id : ℕ) : ℚ) -
        2 * (n.primeFactors.sup id : ℕ) / ((n / n.primeFactors.sup id : ℕ) : ℚ)⌋ ≤
        (absLeastAPLength n : ℤ) ∧
      absLeastAPLength n ≤ n.primeFactors.sup id - 1) ∧
    (2 * n.primeFactors.sup id ≤ n / n.primeFactors.sup id →
      absLeastAPLength n = n.primeFactors.sup id - 1)

/-- **Maximum longest progression length over all reduced residue windows.** Let $n > 1$ be a
natural number, $\operatorname{rad}(n)$ the product of its distinct prime factors and
$\operatorname{gpf}(n)$ its largest prime factor. For an integer $m$ let $f_m(n)$ be the length of
the longest arithmetic progression with positive common difference contained in the set $R_m(n)$
of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$. Then the largest value of
$f_m(n)$ over all integers $m$ is $\max(n / \operatorname{rad}(n), \operatorname{gpf}(n) - 1)$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 2 (`integers-2026-A6-thm-2`). -/
public theorem_wanted isGreatest_longestAPLength {n : ℕ} (hn : 1 < n) :
    IsGreatest (Set.range fun m : ℤ => longestAPLength m n)
      (max (n / radical n) (n.primeFactors.sup id - 1))

/-- **Minimum longest progression length modulo a prime $p \equiv 1 \pmod 4$.** Let $p$ be a prime
with $p \equiv 1 \pmod 4$. For an integer $m$ let $f_m(p)$ be the length of the longest arithmetic
progression with positive common difference contained in the set $R_m(p)$ of integers $a$ with
$m + 1 \le a \le m + p$ and $\gcd(a, p) = 1$. Then the least value of $f_m(p)$ over all integers
$m$ is $(p - 1) / 2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted isLeast_longestAPLength_prime_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 1) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m p) ((p - 1) / 2)

/-- **Minimum longest progression length modulo a prime $p \equiv 3 \pmod 4$.** Let $p$ be a prime
with $p \equiv 3 \pmod 4$. For an integer $m$ let $f_m(p)$ be the length of the longest arithmetic
progression with positive common difference contained in the set $R_m(p)$ of integers $a$ with
$m + 1 \le a \le m + p$ and $\gcd(a, p) = 1$. Then the least value of $f_m(p)$ over all integers
$m$ is $(p + 1) / 2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted isLeast_longestAPLength_prime_of_mod_four_eq_three {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 3) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m p) ((p + 1) / 2)

/-- **Minimum longest progression length modulo a prime power.** Let $p$ be a prime and $r > 1$ a
natural number. For an integer $m$ let $f_m(p^r)$ be the length of the longest arithmetic
progression with positive common difference contained in the set $R_m(p^r)$ of integers $a$ with
$m + 1 \le a \le m + p^r$ and $\gcd(a, p^r) = 1$. Then the least value of $f_m(p^r)$ over all
integers $m$ is $p^{r-1}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted isLeast_longestAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 < r) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m (p ^ r)) (p ^ (r - 1))

/-- **Minimum longest progression length when $n$ is neither squarefree nor a prime power.** Let
$n > 1$ be a natural number that is neither squarefree nor a prime power, $\operatorname{rad}(n)$
the product of its distinct prime factors and $\operatorname{gpf}(n)$ its largest prime factor.
For an integer $m$ let $f_m(n)$ be the length of the longest arithmetic progression with positive
common difference contained in the set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and
$\gcd(a, n) = 1$. Then $f_m(n) \ge n / \operatorname{rad}(n)$ for every integer $m$, and
$f_m(n) \le \max(n / \operatorname{rad}(n), \operatorname{gpf}(n) - 1)$ for some integer $m$.
If moreover $\operatorname{gpf}(n) - 1 \le n / \operatorname{rad}(n)$, then the least value of
$f_m(n)$ over all integers $m$ is $n / \operatorname{rad}(n)$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted longestAPLength_min_of_not_squarefree_of_not_isPrimePow {n : ℕ}
    (hn : 1 < n) (hsq : ¬ Squarefree n) (hpp : ¬ IsPrimePow n) :
    ((∀ m : ℤ, n / radical n ≤ longestAPLength m n) ∧
      ∃ m : ℤ, longestAPLength m n ≤ max (n / radical n) (n.primeFactors.sup id - 1)) ∧
    (n.primeFactors.sup id - 1 ≤ n / radical n →
      IsLeast (Set.range fun m : ℤ => longestAPLength m n) (n / radical n))

/-- **Average longest progression length for non-squarefree moduli.** Let $n > 1$ be a natural
number that is not squarefree, $\operatorname{rad}(n)$ the product of its distinct prime factors
and $\operatorname{gpf}(n)$ its largest prime factor, and suppose that
$\operatorname{gpf}(n) - 1 \le n / \operatorname{rad}(n)$. For an integer $m$ let $f_m(n)$ be the
length of the longest arithmetic progression with positive common difference contained in the
set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$. Then
$\frac{1}{n} \sum_{m=0}^{n-1} f_m(n) = \frac{n}{\operatorname{rad}(n)}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Corollary 1 (`integers-2026-A6-cor-1`). -/
public theorem_wanted average_longestAPLength_of_not_squarefree {n : ℕ} (hn : 1 < n)
    (hsq : ¬ Squarefree n) (h : n.primeFactors.sup id - 1 ≤ n / radical n) :
    (1 / (n : ℚ)) * ∑ m ∈ Finset.range n, (longestAPLength m n : ℚ) = (n : ℚ) / radical n

end

end MetaMathlibExt
