/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Palindromes in arithmetic progressions (statements)

Statement-only targets from Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon
Napp Phunphayap and Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in
Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8 (TeX
source read).

Conventions. For `m ≥ 1` with base-`b` expansion `m = (a_k ⋯ a_0)_b`, the digit `a_i` is
`(Nat.digits b m).getD i 0` (Mathlib's little-endian digit list) and `k` is
`(Nat.digits b m).length - 1`. A positive `n` is a `b`-adic palindrome when
`(Nat.digits b n).Palindrome`. `A_b(m, q, r)` is `palindromeAPCount b m q r` and
`A_b(m) = A_b(m, 1, 0)`; `C_b(m)` is `palindromicHalfCopy b m`; `N_b(k, q, r, x, y)` is
`digitSumCongruenceCount b k q r x y`. Iverson brackets `[P]` are written `if P then 1 else 0`.
-/

namespace MetaMathlibExt

open Int

@[expose] public section

/-- **Two floor-function identities.** For every real number $x$, the sum
$\lfloor x \rfloor + \lfloor -x \rfloor$ equals $0$ if $x$ is an integer and $-1$ otherwise.
For all real numbers $x$ and $y$, $\lfloor x + y \rfloor = \lfloor x \rfloor + \lfloor y \rfloor$ if
$(x - \lfloor x \rfloor) + (y - \lfloor y \rfloor) < 1$, and
$\lfloor x + y \rfloor = \lfloor x \rfloor + \lfloor y \rfloor + 1$ otherwise.

These are parts (iii) and (v) of the cited lemma; its remaining parts are not restated here.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Lemma 6
(`jis-2024-24.4.8-lem-6`). -/
public theorem_wanted floor_add_floor_neg_and_floor_add_eq :
    (∀ x : ℝ, (∃ n : ℤ, x = n) → ⌊x⌋ + ⌊-x⌋ = 0) ∧
      (∀ x : ℝ, (¬ ∃ n : ℤ, x = n) → ⌊x⌋ + ⌊-x⌋ = -1) ∧
      ∀ x y : ℝ, ⌊x + y⌋ =
        if fract x + fract y < 1 then ⌊x⌋ + ⌊y⌋ else ⌊x⌋ + ⌊y⌋ + 1

/-- **Palindromes in an arithmetic progression.** For natural numbers $b$, $m$, $q$ and $r$,
$A_b(m, q, r)$ is the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and
$n \equiv r \pmod q$, where a natural number is a base-$b$ palindrome when its string of base-$b$
digits reads the same in both directions.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Section 1. -/
public def palindromeAPCount (b m q r : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter fun n => (Nat.digits b n).Palindrome ∧ n ≡ r [MOD q]).card

/-- **Palindromic half copy.** For natural numbers $b$ and $m \ge 1$, write
$m = (a_k a_{k-1} \cdots a_0)_b$ for the base-$b$ digits of $m$. The palindromic half copy of $m$
is $C_b(m) = \sum_{j=0}^{k} a_{\max(j, k - j)} b^j$: the $b$-adic palindrome with the same number
of digits as $m$ whose upper digits $a_k, \dots, a_{\lceil k/2 \rceil}$ are those of $m$ and whose
lower digits mirror them. For $m = 0$, which has no digits, $C_b(0) = 0$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 1. -/
public def palindromicHalfCopy (b m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (Nat.digits b m).length,
    (Nat.digits b m).getD (max j ((Nat.digits b m).length - 1 - j)) 0 * b ^ j

/-- **Digit-sum congruence count.** For natural numbers $b$, $k$, $q$, $x$, $y$ and an integer $r$,
$N_b(k, q, r, x, y)$ is the number of tuples $(x_1, \dots, x_k)$ of natural numbers with
$x \le x_1 < y$ and $x_i < b$ for $2 \le i \le k$ such that $x_1 + \dots + x_k \equiv r \pmod q$.
The count is meant for $k \ge 1$; for $k = 0$ it is defined to equal its value for $k = 1$, the
number of natural numbers $x_1$ with $x \le x_1 < y$ and $x_1 \equiv r \pmod q$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 3. -/
public def digitSumCongruenceCount (b k q : ℕ) (r : ℤ) (x y : ℕ) : ℕ :=
  ((Finset.Ico x y ×ˢ Fintype.piFinset fun _ : Fin (k - 1) => Finset.range b).filter
    fun p => ((p.1 + ∑ i, p.2 i : ℕ) : ℤ) ≡ r [ZMOD q]).card

/-- **Two small palindrome counts.** Write $A_b(m, q, r)$ for the number of base-$b$ palindromes
$n$ with $1 \le n \le m$ and $n \equiv r \pmod q$. Then $A_{10}(100, 1, 0) = 18$, the palindromes
being $1, \dots, 9$ and $11, 22, \dots, 99$, and $A_2(9, 2, 1) = 5$, the odd base-$2$ palindromes
up to $9$ being $1$, $3 = (11)_2$, $5 = (101)_2$, $7 = (111)_2$ and $9 = (1001)_2$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Section 1. -/
public theorem palindromeAPCount_small :
    palindromeAPCount 10 100 1 0 = 18 ∧ palindromeAPCount 2 9 2 1 = 5 := by
  decide +kernel

/-- **Palindromic half copies of $5570$ in bases $5$ and $8$.** Write $C_b(m)$ for the
palindromic half copy of $m$ in base $b$. For $m = 5570 = (134240)_5 = (12702)_8$,
$C_5(m) = (134431)_5 = 5616$ and $C_8(m) = (12721)_8 = 5585$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 1 (example). -/
public theorem palindromicHalfCopy_example :
    palindromicHalfCopy 5 5570 = 5616 ∧ palindromicHalfCopy 8 5570 = 5585 := by
  decide +kernel

/-- **A small value of the digit-sum congruence count.** In the notation $N_b(k, q, r, x, y)$
of the digit-sum congruence count, $N_3(2, 2, 0, 0, 3) = 5$: exactly five pairs $(x_1, x_2)$ of
natural numbers with $x_1, x_2 < 3$ have even sum.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 3. -/
public theorem digitSumCongruenceCount_small : digitSumCongruenceCount 3 2 2 0 0 3 = 5 := by
  decide +kernel

/-- **Counting digit tuples by their sum modulo a divisor of the base minus one.** Let $a$, $b$,
$k$ and $q$ be natural numbers, all at least $1$, with $b \equiv 1 \pmod q$, and let $r$ be an
integer. For natural numbers $x$ and $y$ write $N_b(k, q, r, x, y)$ for the number of tuples
$(x_1, \dots, x_k)$ of natural numbers with $x \le x_1 < y$, $x_i < b$ for $2 \le i \le k$, and
$x_1 + \dots + x_k \equiv r \pmod q$. Write $[P]$ for $1$ if $P$ holds and $0$ otherwise,
$\lfloor a/q \rfloor$ for the integer part of $a/q$, and $r \bmod q$ and $a \bmod q$ for the least
nonnegative residues modulo $q$. Then, as rational numbers,

$$N_b(k, q, r, 0, b) = \frac{b^k - 1}{q} + [r \equiv 0 \pmod q],$$

$$N_b(k, q, r, 1, b) = \frac{b^k - b^{k-1}}{q},$$

$$N_b(k, q, r, 0, a) = \frac{a (b^{k-1} - 1)}{q} + \lfloor a/q \rfloor + [r \bmod q < a \bmod q],$$

$$N_b(k, q, r, 1, a) = \frac{(a - 1)(b^{k-1} - 1)}{q} + \lfloor a/q \rfloor +
[r \bmod q < a \bmod q] - [r \equiv 0 \pmod q].$$

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Lemma 5. -/
public theorem_wanted digitSumCongruenceCount_of_modEq_one {a b k q : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hk : 1 ≤ k) (hq : 1 ≤ q) (hbq : b ≡ 1 [MOD q]) (r : ℤ) :
    (digitSumCongruenceCount b k q r 0 b : ℚ) =
        ((b : ℚ) ^ k - 1) / q + (if r ≡ 0 [ZMOD q] then 1 else 0) ∧
      (digitSumCongruenceCount b k q r 1 b : ℚ) = ((b : ℚ) ^ k - (b : ℚ) ^ (k - 1)) / q ∧
      (digitSumCongruenceCount b k q r 0 a : ℚ) =
        (a : ℚ) * ((b : ℚ) ^ (k - 1) - 1) / q + ((a / q : ℕ) : ℚ) +
          (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) ∧
      (digitSumCongruenceCount b k q r 1 a : ℚ) =
        ((a : ℚ) - 1) * ((b : ℚ) ^ (k - 1) - 1) / q + ((a / q : ℕ) : ℚ) +
          (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) - (if r ≡ 0 [ZMOD q] then 1 else 0)

/-- **Palindromes in residue classes modulo a divisor of the base.** Let $b \ge 2$, $m \ge 1$ and
$q \ge 1$ be natural numbers with $q \mid b$. Write $m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$,
with leading digit $a_k$. Write $A_b(m, q, r)$ for the number of base-$b$ palindromes $n$ with
$1 \le n \le m$ and $n \equiv r \pmod q$, $C_b(m)$ for the palindromic half copy of $m$, and
$[P]$ for $1$ if $P$ holds and $0$ otherwise. Put

$$\alpha = \frac{b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2}{b - 1}, \quad
S = \sum_{i=1}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i}, \quad
\delta = [C_b(m) \le m].$$

Then, as rational numbers,

$$A_b(m, q, 0) = \left(\frac{b}{q} - 1\right) \alpha +
\left\lfloor \frac{a_k - 1}{q} \right\rfloor b^{\lfloor k/2 \rfloor} +
[a_k \equiv 0 \pmod q] (S + \delta),$$

and for every natural number $r$ with $r \bmod q > 0$,

$$A_b(m, q, r) = \frac{b \alpha}{q} +
\left\lceil \frac{a_k - (r \bmod q)}{q} \right\rceil b^{\lfloor k/2 \rfloor} +
[a_k \equiv r \pmod q] (S + \delta).$$

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Theorem 7. -/
public theorem_wanted palindromeAPCount_of_dvd_base {b m q : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hq : 1 ≤ q) (hqb : q ∣ b) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let α : ℚ := ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)
    let S : ℚ := ∑ i ∈ Finset.Icc 1 (k / 2), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i)
    let δ : ℚ := if palindromicHalfCopy b m ≤ m then 1 else 0
    (palindromeAPCount b m q 0 : ℚ) =
        ((b : ℚ) / q - 1) * α + (((a k - 1) / q : ℕ) : ℚ) * (b : ℚ) ^ (k / 2) +
          (if a k ≡ 0 [MOD q] then 1 else 0) * (S + δ) ∧
      ∀ r : ℕ, 0 < r % q →
        (palindromeAPCount b m q r : ℚ) =
          (b : ℚ) * α / q + (⌈((a k : ℚ) - ((r % q : ℕ) : ℚ)) / q⌉ : ℚ) * (b : ℚ) ^ (k / 2) +
            (if a k ≡ r [MOD q] then 1 else 0) * (S + δ)

/-- **Counting palindromes up to $m$ and by parity.** Let $b \ge 2$ and $m \ge 1$, and write
$m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$, with leading digit $a_k \ne 0$. For natural numbers
$q$ and $r$, let $A_b(m, q, r)$ be the number of $b$-adic palindromes $n$ with $1 \le n \le m$
and $n \equiv r \pmod q$, and let $C_b(m)$ be the palindromic half copy of $m$. Put $\delta = 1$
if $C_b(m) \le m$ and $\delta = 0$ otherwise. Then
$A_b(m, 1, 0) = b^{\lceil k/2 \rceil} +
\sum_{i=0}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i} + \delta - 2$.
If moreover $b$ is even, let
$\alpha = (b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2)/(b - 1)$ and
$S = \sum_{i=1}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i}$, let $\varepsilon_0 = 1$
if $a_k$ is even and $\varepsilon_0 = 0$ otherwise, and let $\varepsilon_1 = 1 - \varepsilon_0$.
Then $A_b(m, 2, 0) = (b/2 - 1)\alpha + \lfloor (a_k - 1)/2 \rfloor b^{\lfloor k/2 \rfloor} +
\varepsilon_0 (S + \delta)$ and
$A_b(m, 2, 1) = b\alpha/2 + \lceil (a_k - 1)/2 \rceil b^{\lfloor k/2 \rfloor} +
\varepsilon_1 (S + \delta)$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 8. -/
public theorem_wanted palindromeCount_closed_form {b m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let α : ℚ := ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)
    let S : ℚ := ∑ i ∈ Finset.Icc 1 (k / 2), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i)
    let δ : ℚ := if palindromicHalfCopy b m ≤ m then 1 else 0
    (palindromeAPCount b m 1 0 : ℚ) =
        (b : ℚ) ^ ((k + 1) / 2) +
          ∑ i ∈ Finset.range (k / 2 + 1), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i) + δ - 2 ∧
      (Even b →
        (palindromeAPCount b m 2 0 : ℚ) =
            ((b : ℚ) / 2 - 1) * α + (((a k - 1) / 2 : ℕ) : ℚ) * (b : ℚ) ^ (k / 2) +
              (if Even (a k) then 1 else 0) * (S + δ) ∧
          (palindromeAPCount b m 2 1 : ℚ) =
            (b : ℚ) * α / 2 + (⌈((a k : ℚ) - 1) / 2⌉ : ℚ) * (b : ℚ) ^ (k / 2) +
              (if Odd (a k) then 1 else 0) * (S + δ))

/-- **Palindromes in residue classes modulo a divisor of the base minus one.** Let $b \ge 2$,
$m \ge 1$ and $q \ge 1$ be natural numbers with $b \equiv 1 \pmod q$, and let $r$ be a natural
number with $r < q$. Write $m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$. Write $A_b(m, q, r)$ for
the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r \pmod q$, $C_b(m)$
for the palindromic half copy of $m$, $[P]$ for $1$ if $P$ holds and $0$ otherwise, and
$t \bmod d$ for the least nonnegative residue of an integer $t$ modulo a positive integer $d$.
For $j \ge 0$ define integers $s_j$ and $r_j$ as follows. If $q$ is even and $2j \ne k$, let
$s_j = a_{k-j} \bmod (q/2)$ and
$r_j = \bigl(\lfloor r/2 \rfloor - \sum_{i=0}^{j-1} a_{k-i}\bigr) \bmod (q/2)$. If $q$ is odd
and $2j \ne k$, let $s_j = a_{k-j} \bmod q$ and
$r_j = \bigl(\frac{q+1}{2} r - \sum_{i=0}^{j-1} a_{k-i}\bigr) \bmod q$. If $2j = k$, let
$s_j = a_{k-j} \bmod q$ and $r_j = \bigl(r - 2 \sum_{i=0}^{k/2-1} a_{k-i}\bigr) \bmod q$. Put
$\delta = [C_b(m) \le m] \, [r_{\lfloor k/2 \rfloor} = s_{\lfloor k/2 \rfloor}]$ and

$$m_1^* = \sum_{j=0}^{\lfloor (k-1)/2 \rfloor}
\left( \frac{2 a_{k-j} b^{\lfloor (k-1)/2 \rfloor - j} - 2 s_j}{q} + [r_j < s_j] \right),$$

$$m_2^* = \sum_{j=0}^{\lfloor k/2 \rfloor - 1}
\frac{a_{k-j} (b - 1) b^{\lfloor k/2 \rfloor - j - 1}}{q},$$

$$m_3^* = \sum_{j=0}^{\lfloor k/2 \rfloor - 1}
\left( \frac{a_{k-j} (b + 1) b^{\lfloor k/2 \rfloor - j - 1} - 2 s_j}{q} + [r_j < s_j] \right).$$

Then, as rational numbers, if $q$ is odd,

$$A_b(m, q, r) = \frac{b^{\lfloor (k+1)/2 \rfloor} - 1}{q} +
\sum_{j=0}^{\lfloor k/2 \rfloor} \left( \left\lfloor \frac{a_{k-j} b^{\lfloor k/2 \rfloor - j}}{q}
\right\rfloor + [r_j < s_j] \right) - [r = 0] + \delta,$$

and if $q$ is even, $A_b(m, q, r)$ equals $(b - 1) b^{(k-1)/2}/q$ when $k$ and $r$ are odd,
$((b + 1) b^{(k-1)/2} - 2)/q + m_1^* - [r = 0] + \delta$ when $k$ is odd and $r$ is even,
$\lfloor a_{k/2}/q \rfloor + m_2^* + [r_{k/2} < s_{k/2}] + \delta$ when $k$ is even and $r$ is
odd, and $2(b^{k/2} - 1)/q + \lfloor a_{k/2}/q \rfloor + m_3^* - [r = 0] +
[r_{k/2} < s_{k/2}] + \delta$ when $k$ and $r$ are both even.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Theorem 9. -/
public theorem_wanted palindromeAPCount_of_modEq_one {b m q r : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hq : 1 ≤ q) (hr : r < q) (hbq : b ≡ 1 [MOD q]) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let rr : ℕ → ℤ := fun j =>
      if 2 * j = k then ((r : ℤ) - 2 * ∑ i ∈ Finset.range (k / 2), (a (k - i) : ℤ)) % q
      else if Even q then (((r / 2 : ℕ) : ℤ) - ∑ i ∈ Finset.range j, (a (k - i) : ℤ)) % (q / 2 : ℕ)
      else ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ Finset.range j, (a (k - i) : ℤ)) % q
    let ss : ℕ → ℤ := fun j =>
      if Even q ∧ 2 * j ≠ k then ((a (k - j) % (q / 2) : ℕ) : ℤ) else ((a (k - j) % q : ℕ) : ℤ)
    let δ : ℚ :=
      (if palindromicHalfCopy b m ≤ m then 1 else 0) * (if rr (k / 2) = ss (k / 2) then 1 else 0)
    let m₁ : ℚ := ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
      ((2 * (a (k - j) : ℚ) * (b : ℚ) ^ ((k - 1) / 2 - j) - 2 * (ss j : ℚ)) / q +
        (if rr j < ss j then 1 else 0))
    let m₂ : ℚ := ∑ j ∈ Finset.range (k / 2),
      (a (k - j) : ℚ) * ((b : ℚ) - 1) * (b : ℚ) ^ (k / 2 - j - 1) / q
    let m₃ : ℚ := ∑ j ∈ Finset.range (k / 2),
      (((a (k - j) : ℚ) * ((b : ℚ) + 1) * (b : ℚ) ^ (k / 2 - j - 1) - 2 * (ss j : ℚ)) / q +
        (if rr j < ss j then 1 else 0))
    (Odd q →
      (palindromeAPCount b m q r : ℚ) =
        ((b : ℚ) ^ ((k + 1) / 2) - 1) / q +
          ∑ j ∈ Finset.range (k / 2 + 1),
            ((((a (k - j) * b ^ (k / 2 - j)) / q : ℕ) : ℚ) + (if rr j < ss j then 1 else 0)) -
          (if r = 0 then 1 else 0) + δ) ∧
    (Even q →
      (palindromeAPCount b m q r : ℚ) =
        if Odd k ∧ Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
        else if Odd k then
          (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) - 2) / q + m₁ - (if r = 0 then 1 else 0) + δ
        else if Odd r then
          ((a (k / 2) / q : ℕ) : ℚ) + m₂ + (if rr (k / 2) < ss (k / 2) then 1 else 0) + δ
        else
          2 * ((b : ℚ) ^ (k / 2) - 1) / q + ((a (k / 2) / q : ℕ) : ℚ) + m₃ -
            (if r = 0 then 1 else 0) + (if rr (k / 2) < ss (k / 2) then 1 else 0) + δ)

/-- **Palindromes up to a power of the base in residue classes.** Let $b \ge 2$, $k \ge 1$ and
$q \ge 1$ be natural numbers and let $r$ be a natural number with $r < q$. Write $A_b(m, q, r)$
for the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r \pmod q$, and
$[r = 0]$ for $1$ if $r = 0$ and $0$ otherwise. If $q \mid b$, then

$$A_b(b^k, q, r) = \left(\frac{b}{q} - [r = 0]\right)
\frac{b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2}{b - 1}.$$

If $b \equiv 1 \pmod q$, then $A_b(b^k, q, r)$ equals
$(b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2)/q$ if $q$ is odd,
$(b - 1) b^{\lfloor (k-1)/2 \rfloor}/q$ if $q$ is even and $r$ is odd, and
$((b + 1) b^{\lfloor (k-1)/2 \rfloor} + 2 b^{\lfloor k/2 \rfloor} - 4)/q$ if $q$ and $r$ are both
even. All these identities hold as identities of rational numbers.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 11. -/
public theorem_wanted palindromeAPCount_base_pow {b k q r : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hq : 1 ≤ q) (hr : r < q) :
    (q ∣ b →
      (palindromeAPCount b (b ^ k) q r : ℚ) =
        ((b : ℚ) / q - (if r = 0 then 1 else 0)) *
          (((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1))) ∧
    (b ≡ 1 [MOD q] →
      (palindromeAPCount b (b ^ k) q r : ℚ) =
        if Odd q then ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / q
        else if Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
        else (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) + 2 * (b : ℚ) ^ (k / 2) - 4) / q)

/-- **Palindromes in residue classes: a logarithmic error bound.** Let $b \ge 2$ be a natural
number, let $q$ be an odd natural number with $b \equiv 1 \pmod q$, and let $r$ be a natural
number with $r < q$. For natural numbers $m$, $q'$ and $r'$, write $A_b(m, q', r')$ for the number
of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r' \pmod{q'}$; thus $A_b(m, 1, 0)$
is the number of all base-$b$ palindromes in $[1, m]$. Then for every natural number $m \ge 1$,

$$\left| A_b(m, q, r) - \frac{A_b(m, 1, 0)}{q} \right| \le \frac{\log m}{2 \log b} + 2,$$

where $\log$ is the natural logarithm.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 12. -/
public theorem_wanted abs_palindromeAPCount_sub_le {b q r : ℕ} (hb : 2 ≤ b) (hq : Odd q)
    (hr : r < q) (hbq : b ≡ 1 [MOD q]) {m : ℕ} (hm : 1 ≤ m) :
    |(palindromeAPCount b m q r : ℝ) - (palindromeAPCount b m 1 0 : ℝ) / q| ≤
      Real.log m / (2 * Real.log b) + 2

end

end MetaMathlibExt
