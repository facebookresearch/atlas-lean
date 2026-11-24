/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.SpoofLehmerFactorization

/-!
# Spoof Lehmer factorizations (wanted statements)

Statements from Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26
(2026), Article A33. A spoof factorization `x_1^{a_1} ⋯ x_r^{a_r}` is a multiset of pairs
`(x_i, a_i)` of positive integers; `x_1 ⋯ x_r` denotes the factorization with all exponents `1`,
encoded as `Multiset.map (fun a => (a, 1)) x`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Nontrivial spoof Lehmer factorizations have all exponents $1$.** If $F$ is a nontrivial spoof
$k$-Lehmer factorization for some integer $k$, then every exponent of $F$ is $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 3 (`integers-2026-A33-thm-3`). -/
public theorem_wanted spoofLehmer_exponents_eq_one (F : Multiset (ℕ × ℕ))
    (k : ℤ) (hL : IsSpoofLehmer k F) (hnt : ¬ IsTrivialSpoof F) : ∀ p ∈ F, p.2 = 1

/-- **Bases of a spoof Lehmer factorization modulo divisors of its evaluation.** Let
$x_1, \dots, x_r$ be natural numbers and let $F = x_1 \cdots x_r$ be the spoof factorization with
these bases, all with exponent $1$. Suppose $F$ is a nontrivial spoof $k$-Lehmer factorization for
some integer $k$. If $n$ is an integer with $n \ne \pm 1$ that divides the spoof evaluation
$\tilde e(F)$, then $x_i \not\equiv 1 \pmod n$ for every $i$.

The source states this for every integer $n$ dividing $\tilde e(F)$, but the hypothesis
$n \ne \pm 1$ cannot be dropped: $3 \cdot 3$ is a nontrivial spoof $2$-Lehmer factorization
($2 \cdot 4 = 9 - 1$), $1$ divides $\tilde e(3 \cdot 3) = 9$, and $3 \equiv 1 \pmod 1$. The source's
proof reaches $0 \equiv -1 \pmod n$, which is a contradiction only when $n \nmid 1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 4 (`integers-2026-A33-thm-4`). -/
public theorem_wanted spoofLehmer_base_not_modEq_one (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) (n : ℤ)
    (hn : n ∣ spoofEval (spoofOfBases x)) (hunit : ¬ IsUnit n) :
    ∀ a ∈ x, ¬ (a : ℤ) ≡ 1 [ZMOD n]

/-- **Bases of a nontrivial spoof Lehmer factorization are not $1$ modulo one another.** Let
$x_1, \dots, x_r$ be natural numbers and let $F = x_1 \cdots x_r$ be the spoof factorization with
these bases, all with exponent $1$. If $F$ is a nontrivial spoof $k$-Lehmer factorization for some
integer $k$, then $x_i \not\equiv 1 \pmod{x_j}$ for all $i$ and $j$, including $i = j$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Corollary 1 (`integers-2026-A33-cor-1`). -/
public theorem_wanted spoofLehmer_base_not_modEq_one_base (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    ∀ a ∈ x, ∀ b ∈ x, ¬ a ≡ 1 [MOD b]

/-- **Primes dividing the evaluation of a spoof Lehmer factorization.** Let $x_1, \dots, x_r$ be
natural numbers and let $F = x_1 \cdots x_r$ be the spoof factorization with these bases, all with
exponent $1$. Suppose $F$ is a nontrivial spoof $k$-Lehmer factorization for some integer $k$. If
$p$ is a prime dividing the spoof evaluation $\tilde e(F)$, then $x_i \not\equiv 1 \pmod p$ for
every $i$. Moreover, if $F$ is even (not every base is odd), then every base $x_i$ is even.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Corollary 2 (`integers-2026-A33-cor-2`). -/
public theorem_wanted spoofLehmer_base_not_modEq_one_prime (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ spoofEval (spoofOfBases x) →
      ∀ a ∈ x, ¬ a ≡ 1 [MOD p]) ∧
    (¬ IsOddSpoof (spoofOfBases x) → ∀ a ∈ x, Even a)

/-- **Formulas for the Lehmer bounds.** Let $L(t; r)$ and $U(t; r)$ be the lower and upper
Lehmer bounds of a list $t$ of real numbers, and write $\emptyset$ for the empty list. Then
$L(\emptyset; r) = 1$ for every $r \ge 1$, and $U(\emptyset; r) = 2^r - 1$ for every natural
number $r$. Let $t = (t_1, \dots, t_s)$ with $s \ge 1$ and $2 \le t_1 \le \dots \le t_s$, and
let $r \ge s$ be a natural number. Then
$$U(t; r) = \frac{t_1 \cdots t_{s-1} t_s^{r-s+1} - 1}
{(t_1 - 1) \cdots (t_{s-1} - 1)(t_s - 1)^{r-s+1}},$$
and if moreover $r > s$, then
$$L(t; r) = \frac{t_1 \cdots t_s}{(t_1 - 1) \cdots (t_s - 1)}.$$

The condition $r > s$ for $L$ is needed: for $s = r$ the only admissible completion of $t$ is the
empty list, so $L(t; r) = \kappa_r(t)$, where $\kappa_r$ is the Lehmer function; for $t = (2)$
and $r = 1$ this is $\kappa_1(2) = 1$, while the formula gives $2$. Likewise
$L(\emptyset; 0) = \kappa_0 = 0$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 1 (`integers-2026-A33-lem-1`). -/
public theorem_wanted lehmerLower_upper_formula :
    (∀ r : ℕ, 1 ≤ r → lehmerLower [] r = 1) ∧ (∀ r : ℕ, lehmerUpper [] r = 2 ^ r - 1) ∧
    ∀ (t : List ℝ) (r : ℕ) (hne : t ≠ []), t.Pairwise (· ≤ ·) → (∀ x ∈ t, 2 ≤ x) →
      t.length ≤ r →
      (t.length < r → lehmerLower t r = t.prod / (t.map (· - 1)).prod) ∧
      lehmerUpper t r = (t.dropLast.prod * t.getLast hne ^ (r - t.length + 1) - 1) /
        ((t.dropLast.map (· - 1)).prod * (t.getLast hne - 1) ^ (r - t.length + 1))

/-- **Monotonicity of the Lehmer bounds.** Let $L(t; r)$ and $U(t; r)$ be the lower and upper
Lehmer bounds: the infimum and the supremum of $\kappa_r(t_1, \dots, t_s, u_1, \dots, u_{r-s})$
over the admissible completions $u$ of $t = (t_1, \dots, t_s)$, where $\kappa_r$ is the Lehmer
function. Let $r$ be a natural number and let $t = (t_1, \dots, t_s)$ and
$t' = (t'_1, \dots, t'_s)$ be nondecreasing lists of real numbers of the same length $s \le r$
with $t_i \ge 2$ and $t_i \le t'_i$ for every $i$. Then $L(t'; r) \le L(t; r)$ and
$U(t'; r) \le U(t; r)$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 2 (`integers-2026-A33-lem-2`). -/
public theorem_wanted lehmerLower_upper_antitone (r : ℕ) (t t' : List ℝ) (hs : t.length ≤ r)
    (ht : t.Pairwise (· ≤ ·)) (ht' : t'.Pairwise (· ≤ ·)) (h2 : ∀ x ∈ t, 2 ≤ x)
    (hle : List.Forall₂ (· ≤ ·) t t') :
    lehmerLower t' r ≤ lehmerLower t r ∧ lehmerUpper t' r ≤ lehmerUpper t r

/-- **Lehmer bounds at the initial segments of a spoof Lehmer factorization.** Let
$x_1 \le \dots \le x_r$ be natural numbers and let $F = x_1 \cdots x_r$ be the spoof factorization
with these bases, all with exponent $1$. Suppose $F$ is a nontrivial spoof $k$-Lehmer factorization
for an integer $k$. For a list $t = (t_1, \dots, t_s)$ of real numbers, let $L(t; r)$ and $U(t; r)$
be the lower and upper Lehmer bounds: the infimum and the supremum in $\mathbb{R}$ of
$\kappa_r(t_1, \dots, t_s, u_{s+1}, \dots, u_r)$ over all real numbers $u_{s+1}, \dots, u_r \ge 2$
such that $t_1, \dots, t_s, u_{s+1}, \dots, u_r$ is nondecreasing, where
$\kappa_r(y_1, \dots, y_r) = (y_1 \cdots y_r - 1) / ((y_1 - 1) \cdots (y_r - 1))$. Then for every
$s$ with $0 \le s \le r$ we have $L(x_1, \dots, x_s; r) \le k \le U(x_1, \dots, x_s; r)$, and
$L(x_1, \dots, x_s; r) = k$ if and only if $s = r$. Moreover $1 < k \le 2^r - 1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 3 (`integers-2026-A33-lem-3`). -/
public theorem_wanted spoofLehmer_lower_le_le_upper (x : List ℕ) (hsorted : x.Pairwise (· ≤ ·))
    (k : ℤ) (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    (∀ s ≤ x.length,
      lehmerLower ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length ≤ k ∧
      (k : ℝ) ≤ lehmerUpper ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length ∧
      (lehmerLower ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length = k ↔ s = x.length)) ∧
    1 < k ∧ k ≤ 2 ^ x.length - 1

/-- **Finitely many solutions of the Lehmer equation in $r$ variables.** For every natural
number $r \ge 2$, there are only finitely many pairs $(k, x)$ of an integer $k > 0$ and a tuple
$x = (x_1, \dots, x_r)$ of natural numbers with $x_i \ge 2$ for every $i$ such that
$k (x_1 - 1) \cdots (x_r - 1) = x_1 \cdots x_r - 1$.

The source also claims that the solutions can be computed explicitly; that claim is not part of
this statement.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 1 (`integers-2026-A33-thm-1`). -/
public theorem_wanted lehmerEquation_solutions_finite (r : ℕ) (hr : 2 ≤ r) :
    {p : ℤ × (Fin r → ℕ) | 0 < p.1 ∧ (∀ i, 2 ≤ p.2 i) ∧
      p.1 * ∏ i, ((p.2 i : ℤ) - 1) = ∏ i, (p.2 i : ℤ) - 1}.Finite

/-- **Solutions of the Lehmer equation with at most six variables.** Call a finite multiset
$\{x_1, \dots, x_r\}$ of natural numbers a solution of the Lehmer equation if $x_i \ge 2$ for
every $i$ and $k (x_1 - 1) \cdots (x_r - 1) = x_1 \cdots x_r - 1$ for some integer $k > 0$.
There are exactly $76$ solutions with $2 \le r \le 6$ (counted over all such $r$ together).
Exactly $31$ of them have every $x_i$ odd, and exactly $45$ have every $x_i$ even.

Solutions are counted as multisets, that is, up to the order of the $x_i$, as in Tables 1 and 2.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 2 (`integers-2026-A33-thm-2`). -/
public theorem_wanted lehmerEquation_solutions_count :
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x} = 76 ∧
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x ∧ ∀ a ∈ x, Odd a} = 31 ∧
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x ∧ ∀ a ∈ x, Even a} = 45

/-- **Finitely many nontrivial spoof Lehmer factorizations with $r$ factors.** For every natural
number $r$, there are only finitely many finite multisets $F$ of pairs (base, exponent) of natural
numbers with exactly $r$ elements such that $F$ is a nontrivial spoof $k$-Lehmer factorization for
some integer $k$.

The source also asserts that these factorizations can be computed explicitly and verifiably; that
claim is not part of this statement.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 6 (`integers-2026-A33-thm-6`). -/
public theorem_wanted spoofLehmer_finite (r : ℕ) :
    {F : Multiset (ℕ × ℕ) | Multiset.card F = r ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F}.Finite

/-- **Spoof Lehmer factorizations with at most six factors.** Let $F$ be a finite multiset of pairs
(base, exponent) of natural numbers with at most $6$ elements. Then $F$ is a nontrivial odd spoof
$k$-Lehmer factorization for some integer $k$ if and only if every exponent of $F$ is $1$ and the
multiset of bases of $F$ is one of the following $31$, written as tuples: $(3, 3)$, $(3, 5, 15)$,
$(3, 5, 17, 255)$, $(3, 3, 3, 3)$, $(3, 5, 17, 257, 65535)$, $(3, 5, 17, 285, 2507)$,
$(5, 5, 5, 43, 5375)$, $(5, 5, 9, 9, 89)$, $(3, 5, 17, 257, 65537, 4294967295)$,
$(3, 5, 17, 257, 65555, 226112997)$, $(3, 5, 17, 257, 65717, 23794275)$,
$(3, 5, 17, 257, 68975, 1314417)$, $(3, 5, 17, 353, 929, 83623935)$, $(3, 5, 17, 377, 1217, 2295)$,
$(3, 5, 17, 395, 1059, 2303)$, $(3, 5, 33, 53, 69, 8343)$, $(3, 9, 9, 23, 131, 732159)$,
$(5, 5, 5, 43, 5377, 28901375)$, $(5, 5, 5, 43, 5387, 2632285)$, $(5, 5, 5, 43, 5407, 937505)$,
$(5, 5, 5, 43, 5477, 291475)$, $(5, 5, 5, 43, 5717, 90115)$, $(5, 5, 5, 43, 6215, 39817)$,
$(5, 5, 5, 43, 6487, 31385)$, $(5, 5, 5, 43, 8507, 14605)$, $(5, 5, 5, 45, 807, 267023)$,
$(5, 5, 5, 47, 453, 2661375)$, $(5, 5, 5, 47, 457, 50659)$, $(5, 5, 5, 65, 129, 2325)$,
$(5, 7, 7, 7, 133, 228095)$ and $(3, 3, 5, 5, 9, 89)$. Also, $F$ is a nontrivial spoof $k$-Lehmer
factorization for some integer $k$ and $F$ is even (some base is even) if and only if every exponent
of $F$ is $1$ and the multiset of bases of $F$ is one of the following $45$, written as tuples:
$(2, 2)$, $(2, 4, 8)$, $(2, 2, 4)$, $(2, 2, 2)$, $(2, 4, 10, 80)$, $(2, 2, 6, 24)$, $(2, 2, 4, 4)$,
$(2, 2, 2, 8)$, $(2, 2, 2, 2)$, $(2, 4, 10, 82, 6560)$, $(2, 4, 10, 92, 670)$,
$(2, 4, 10, 100, 422)$, $(2, 4, 10, 112, 290)$, $(2, 2, 6, 26, 624)$, $(2, 2, 8, 12, 384)$,
$(2, 2, 2, 10, 80)$, $(2, 2, 2, 4, 32)$, $(2, 2, 2, 2, 16)$, $(2, 2, 2, 2, 6)$, $(2, 2, 2, 2, 4)$,
$(2, 2, 2, 2, 2)$, $(2, 4, 10, 82, 6562, 43046720)$, $(2, 4, 10, 82, 12440, 13882)$,
$(2, 4, 10, 88, 1120, 9944)$, $(2, 4, 26, 26, 26, 8272)$, $(2, 8, 8, 8, 206, 210944)$,
$(2, 2, 6, 26, 626, 390624)$, $(2, 2, 6, 42, 62, 2156)$, $(2, 2, 8, 12, 386, 148224)$,
$(2, 2, 8, 12, 404, 8166)$, $(2, 2, 8, 12, 416, 5154)$, $(2, 2, 8, 12, 636, 974)$,
$(2, 2, 12, 14, 18, 206)$, $(2, 2, 2, 10, 82, 6560)$, $(2, 2, 2, 10, 92, 670)$,
$(2, 2, 2, 10, 100, 422)$, $(2, 2, 2, 10, 112, 290)$, $(2, 2, 2, 4, 34, 1088)$,
$(2, 2, 2, 4, 38, 244)$, $(2, 2, 2, 6, 8, 384)$, $(2, 2, 2, 4, 8, 16)$, $(2, 2, 2, 2, 18, 288)$,
$(2, 2, 2, 2, 6, 6)$, $(2, 2, 2, 2, 2, 32)$ and $(2, 2, 2, 2, 2, 2)$.

The source further attributes $11$ of the odd and $27$ of the even factorizations to the families of
its Examples 2–5, leaving $20$ and $18$ sporadic ones; that attribution is not part of this
statement.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 7 (`integers-2026-A33-thm-7`). -/
public theorem_wanted spoofLehmer_atMostSix_tables :
    {F : Multiset (ℕ × ℕ) | Multiset.card F ≤ 6 ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F ∧ IsOddSpoof F} =
      {F | ∃ l ∈ ([
      [3, 3], [3, 5, 15], [3, 5, 17, 255], [3, 3, 3, 3], [3, 5, 17, 257, 65535],
      [3, 5, 17, 285, 2507], [5, 5, 5, 43, 5375], [5, 5, 9, 9, 89],
      [3, 5, 17, 257, 65537, 4294967295], [3, 5, 17, 257, 65555, 226112997],
      [3, 5, 17, 257, 65717, 23794275], [3, 5, 17, 257, 68975, 1314417],
      [3, 5, 17, 353, 929, 83623935], [3, 5, 17, 377, 1217, 2295], [3, 5, 17, 395, 1059, 2303],
      [3, 5, 33, 53, 69, 8343], [3, 9, 9, 23, 131, 732159], [5, 5, 5, 43, 5377, 28901375],
      [5, 5, 5, 43, 5387, 2632285], [5, 5, 5, 43, 5407, 937505], [5, 5, 5, 43, 5477, 291475],
      [5, 5, 5, 43, 5717, 90115], [5, 5, 5, 43, 6215, 39817], [5, 5, 5, 43, 6487, 31385],
      [5, 5, 5, 43, 8507, 14605], [5, 5, 5, 45, 807, 267023], [5, 5, 5, 47, 453, 2661375],
      [5, 5, 5, 47, 457, 50659], [5, 5, 5, 65, 129, 2325], [5, 7, 7, 7, 133, 228095],
      [3, 3, 5, 5, 9, 89]] : List (List ℕ)),
        F = spoofOfBases (l : Multiset ℕ)} ∧
    {F : Multiset (ℕ × ℕ) | Multiset.card F ≤ 6 ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F ∧ ¬ IsOddSpoof F} =
      {F | ∃ l ∈ ([
      [2, 2], [2, 4, 8], [2, 2, 4], [2, 2, 2], [2, 4, 10, 80], [2, 2, 6, 24], [2, 2, 4, 4],
      [2, 2, 2, 8], [2, 2, 2, 2], [2, 4, 10, 82, 6560], [2, 4, 10, 92, 670], [2, 4, 10, 100, 422],
      [2, 4, 10, 112, 290], [2, 2, 6, 26, 624], [2, 2, 8, 12, 384], [2, 2, 2, 10, 80],
      [2, 2, 2, 4, 32], [2, 2, 2, 2, 16], [2, 2, 2, 2, 6], [2, 2, 2, 2, 4], [2, 2, 2, 2, 2],
      [2, 4, 10, 82, 6562, 43046720], [2, 4, 10, 82, 12440, 13882], [2, 4, 10, 88, 1120, 9944],
      [2, 4, 26, 26, 26, 8272], [2, 8, 8, 8, 206, 210944], [2, 2, 6, 26, 626, 390624],
      [2, 2, 6, 42, 62, 2156], [2, 2, 8, 12, 386, 148224], [2, 2, 8, 12, 404, 8166],
      [2, 2, 8, 12, 416, 5154], [2, 2, 8, 12, 636, 974], [2, 2, 12, 14, 18, 206],
      [2, 2, 2, 10, 82, 6560], [2, 2, 2, 10, 92, 670], [2, 2, 2, 10, 100, 422],
      [2, 2, 2, 10, 112, 290], [2, 2, 2, 4, 34, 1088], [2, 2, 2, 4, 38, 244], [2, 2, 2, 6, 8, 384],
      [2, 2, 2, 4, 8, 16], [2, 2, 2, 2, 18, 288], [2, 2, 2, 2, 6, 6], [2, 2, 2, 2, 2, 32],
      [2, 2, 2, 2, 2, 2]] : List (List ℕ)),
        F = spoofOfBases (l : Multiset ℕ)}

end

end MetaMathlibExt
