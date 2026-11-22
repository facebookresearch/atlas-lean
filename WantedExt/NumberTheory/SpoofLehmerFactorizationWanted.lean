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

/-!
# Spoof Lehmer factorizations (wanted statements)

Statements from Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26
(2026), Article A33. A spoof factorization `x_1^{a_1} ⋯ x_r^{a_r}` is a multiset of pairs
`(x_i, a_i)` of positive integers; `x_1 ⋯ x_r` denotes the factorization with all exponents `1`,
encoded as `Multiset.map (fun a => (a, 1)) x`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Spoof factorizations.** A finite multiset $F = \{(x_1, a_1), \dots, (x_r, a_r)\}$ of pairs of
natural numbers, read as the formal product $x_1^{a_1} \cdots x_r^{a_r}$, is a spoof factorization
if every base $x_i$ and every exponent $a_i$ is positive.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 1. -/
def IsSpoofFactorization (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, 0 < p.1 ∧ 0 < p.2

/-- **Spoof evaluation.** Let $F = x_1^{a_1} \cdots x_r^{a_r}$ be a finite multiset of pairs
$(x_i, a_i)$ of natural numbers, each a base $x_i$ with an exponent $a_i$. The spoof evaluation of
$F$ is the integer $\tilde e(F) = x_1^{a_1} \cdots x_r^{a_r} = \prod_{i=1}^{r} x_i^{a_i}$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 2. -/
def spoofEval (F : Multiset (ℕ × ℕ)) : ℤ :=
  (F.map fun p => (p.1 : ℤ) ^ p.2).prod

/-- **Spoof totient.** Let $F$ be a finite multiset of pairs $(x_i, a_i)$ of natural numbers,
$i = 1, \dots, r$, viewed as the formal product $x_1^{a_1} \cdots x_r^{a_r}$. The spoof totient
of $F$ is the integer $\tilde\varphi(F) = \prod_{i=1}^{r} (x_i^{a_i} - x_i^{a_i - 1})$, where
the exponent $a_i - 1$ is truncated at $0$, so a pair with $a_i = 0$ contributes the factor $0$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 3. -/
def spoofTotient (F : Multiset (ℕ × ℕ)) : ℤ :=
  (F.map fun p => (p.1 : ℤ) ^ p.2 - (p.1 : ℤ) ^ (p.2 - 1)).prod

/-- **Spoof evaluation and spoof totient of $3 \cdot 3$.** Let $3 \cdot 3$ denote the spoof
factorization $3^1 \cdot 3^1$, with two factors of base $3$ and exponent $1$. Its spoof evaluation
is $\tilde e(3 \cdot 3) = 9$ and its spoof totient is $\tilde\varphi(3 \cdot 3) = 4$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definitions 2 and 3. -/
theorem spoofEval_spoofTotient_three_three :
    spoofEval {(3, 1), (3, 1)} = 9 ∧ spoofTotient {(3, 1), (3, 1)} = 4 := by
  norm_num [spoofEval, spoofTotient]

/-- **Spoof Lehmer factorizations.** Let $k$ be an integer and $F$ a finite multiset of pairs
$(x, a)$ of natural numbers. Write $\tilde e(F) = \prod x^a$ for the spoof evaluation and
$\tilde\varphi(F) = \prod (x^a - x^{a-1})$ for the spoof totient of $F$, the products running
over the pairs of $F$ with multiplicity. Then $F$ is a (spoof) $k$-Lehmer factorization if $F$ is
a spoof factorization (every base and exponent is positive), $k \cdot \tilde\varphi(F) =
\tilde e(F) - 1$, and $F$ has at least two factors counted with multiplicity or some factor
whose exponent is greater than $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 4. -/
def IsSpoofLehmer (k : ℤ) (F : Multiset (ℕ × ℕ)) : Prop :=
  IsSpoofFactorization F ∧ k * spoofTotient F = spoofEval F - 1 ∧
    (2 ≤ Multiset.card F ∨ ∃ p ∈ F, 1 < p.2)

/-- **$3 \cdot 3$ is a $2$-Lehmer factorization.** The spoof factorization $3^1 \cdot 3^1$ is a
$2$-Lehmer factorization; indeed $2 \cdot (3 - 1)(3 - 1) = 3 \cdot 3 - 1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Table 1. -/
theorem isSpoofLehmer_three_three : IsSpoofLehmer 2 {(3, 1), (3, 1)} :=
  ⟨by simp [IsSpoofFactorization], by norm_num [spoofEval, spoofTotient], Or.inl (by simp)⟩

/-- **The factorizations $1^a \cdot 1^b$ are Lehmer for every $k$.** For all positive integers
$a$ and $b$ and every integer $k$, the spoof factorization $1^a \cdot 1^b$ is a $k$-Lehmer
factorization.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Example 1. -/
theorem isSpoofLehmer_one_one (k : ℤ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    IsSpoofLehmer k {(1, a), (1, b)} :=
  ⟨by simp [IsSpoofFactorization, ha, hb], by simp [spoofEval, spoofTotient], Or.inl (by simp)⟩

/-- **Trivial spoof factorizations.** A finite multiset $F$ of pairs $(x, a)$ of natural numbers,
read as a spoof factorization with bases $x$ and exponents $a$, is trivial if every base $x$
occurring in $F$ equals $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 6. -/
def IsTrivialSpoof (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, p.1 = 1

/-- **Odd spoof factorizations.** A finite multiset $F$ of pairs $(x, a)$ of natural numbers, read
as a spoof factorization with bases $x$ and exponents $a$, is odd if every base $x$ occurring in
$F$ is odd.

A spoof factorization that is not odd is called even.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 7. -/
def IsOddSpoof (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, Odd p.1

/-- **Factorization with all exponents one.** For a finite multiset $x$ of natural numbers
$x_1, \dots, x_r$, this is the formal product $x_1 \cdots x_r = x_1^1 \cdots x_r^1$, that is,
the multiset of pairs $(x_1, 1), \dots, (x_r, 1)$, each consisting of a base $x_i$ and the
exponent $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Remark 3. -/
def spoofOfBases (x : Multiset ℕ) : Multiset (ℕ × ℕ) :=
  x.map fun a => (a, 1)

/-- **The exponent-one factorization on the bases 3 and 3.** The factorization with all exponents
one on the multiset of bases consisting of two copies of $3$ is the multiset consisting of two
copies of the pair $(3, 1)$, that is, $3 \cdot 3 = 3^1 \cdot 3^1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Remark 3. -/
theorem spoofOfBases_three_three : spoofOfBases {3, 3} = {(3, 1), (3, 1)} := by
  simp [spoofOfBases]

/-- **Solutions of the Lehmer equation.** A finite multiset $x$ of natural numbers solves
Equation (1) if every element $x_j$ of $x$ satisfies $x_j \ge 2$ and there is a positive integer
$k$ with $k \prod_j (x_j - 1) = \prod_j x_j - 1$, where the products run over the elements of $x$
with multiplicity and are computed in $\mathbb{Z}$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Equation (1). -/
def IsLehmerEquationSolution (x : Multiset ℕ) : Prop :=
  (∀ a ∈ x, 2 ≤ a) ∧ ∃ k : ℤ, 0 < k ∧
    k * (x.map fun a : ℕ => (a : ℤ) - 1).prod = (x.map fun a : ℕ => (a : ℤ)).prod - 1

/-- **The multiset $\{3, 3\}$ solves the Lehmer equation.** Every element of the multiset
$\{3, 3\}$ is at least $2$, and there is a positive integer $k$ with
$k \cdot (3 - 1)(3 - 1) = 3 \cdot 3 - 1$ (namely $k = 2$). So $\{3, 3\}$ solves Equation (1), the
equation $k \prod_j (x_j - 1) = \prod_j x_j - 1$ in the elements $x_j$ of a multiset, counted
with multiplicity.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Table 1. -/
theorem isLehmerEquationSolution_three_three : IsLehmerEquationSolution {3, 3} :=
  ⟨by simp, 2, by norm_num, by norm_num⟩

/-- **The Lehmer function $\kappa_r$.** For a list $t = (t_1, \dots, t_r)$ of real numbers,
$$\kappa_r(t_1, \dots, t_r) = \frac{t_1 \cdots t_r - 1}{(t_1 - 1) \cdots (t_r - 1)},$$
with division by zero giving $0$ (so $\kappa_r(t) = 0$ when some $t_i = 1$).

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 8. -/
noncomputable def lehmerKappa (t : List ℝ) : ℝ :=
  (t.prod - 1) / (t.map (· - 1)).prod

/-- **The Lehmer function at $(2, 2)$.** The Lehmer function
$\kappa_2(t_1, t_2) = (t_1 t_2 - 1) / ((t_1 - 1)(t_2 - 1))$ takes the value $\kappa_2(2, 2) = 3$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 8 and proof of Theorem 5. -/
theorem lehmerKappa_two_two : lehmerKappa [2, 2] = 3 := by
  simp only [lehmerKappa, List.prod_cons, List.prod_nil, List.map_cons, List.map_nil]
  norm_num

/-- **Admissible completions for the Lehmer bounds.** Let $t = (t_1, \dots, t_s)$ be a list of
real numbers and let $r$ be a natural number. The admissible completions of $t$ to length $r$
are the lists $u = (u_1, \dots, u_m)$ of real numbers with $s + m = r$ such that
$t_1, \dots, t_s, u_1, \dots, u_m$ is nondecreasing and $u_j \ge 2$ for every $j$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
def lehmerCompletions (t : List ℝ) (r : ℕ) : Set (List ℝ) :=
  {u | t.length + u.length = r ∧ (t ++ u).Pairwise (· ≤ ·) ∧ ∀ x ∈ u, 2 ≤ x}

/-- **The lower Lehmer bound.** Let $t = (t_1, \dots, t_s)$ be a list of real numbers and let $r$
be a natural number. An admissible completion of $t$ to length $r$ is a list
$u = (u_1, \dots, u_m)$ of real numbers with $s + m = r$ such that
$t_1, \dots, t_s, u_1, \dots, u_m$ is nondecreasing and $u_j \ge 2$ for every $j$. The lower
Lehmer bound $L(t; r)$ is the infimum of $\kappa_r(t_1, \dots, t_s, u_1, \dots, u_m)$ over all
admissible completions $u$ of $t$ to length $r$, where $\kappa_r$ is the Lehmer function. The
infimum is taken to be $0$ when there is no admissible completion or the values are unbounded
below.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
noncomputable def lehmerLower (t : List ℝ) (r : ℕ) : ℝ :=
  sInf ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r)

/-- **Upper Lehmer bound $U(t; r)$.** For real numbers $y_1, \dots, y_r$ let
$\kappa_r(y_1, \dots, y_r) = (y_1 \cdots y_r - 1) / ((y_1 - 1) \cdots (y_r - 1))$, where division
by $0$ gives $0$. For a list $t = (t_1, \dots, t_s)$ of real numbers and a natural number $r$, an
admissible completion of $t$ is a list $u = (u_{s+1}, \dots, u_r)$ of $r - s$ real numbers (there
is none if $s > r$) such that $t_1, \dots, t_s, u_{s+1}, \dots, u_r$ is nondecreasing and
$u_j \ge 2$ for every $j$. Then $U(t; r)$ is the supremum in $\mathbb{R}$ of
$\kappa_r(t_1, \dots, t_s, u_{s+1}, \dots, u_r)$ over all admissible completions $u$ of $t$; by
convention it is $0$ when $t$ has no admissible completion or these values are not bounded above.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
noncomputable def lehmerUpper (t : List ℝ) (r : ℕ) : ℝ :=
  sSup ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r)

/-- **A full-length nondecreasing list has only the empty completion.** Let
$t = (t_1, \dots, t_r)$ be a nondecreasing list of $r$ real numbers. Then the empty list is the
only admissible completion of $t$ to length $r$, that is, the only list $u$ of real numbers such
that $r + |u| = r$, the concatenation of $t$ and $u$ is nondecreasing, and every entry of $u$ is
at least $2$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
theorem lehmerCompletions_length {t : List ℝ} (ht : t.Pairwise (· ≤ ·)) :
    lehmerCompletions t t.length = {[]} := by
  ext u
  simp only [lehmerCompletions, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, -, -⟩
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl
    simpa using ht

/-- **The Lehmer bounds of a full-length list.** Let $L(t; r)$ and $U(t; r)$ be the lower and
upper Lehmer bounds and $\kappa_r$ the Lehmer function. For every nondecreasing list
$t = (t_1, \dots, t_r)$ of real numbers, $L(t; r) = U(t; r) = \kappa_r(t_1, \dots, t_r)$.

The only admissible completion of such a list to its own length $r$ is the empty list.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9 and proof of Lemma 3. -/
theorem lehmerLower_upper_length {t : List ℝ} (ht : t.Pairwise (· ≤ ·)) :
    lehmerLower t t.length = lehmerKappa t ∧ lehmerUpper t t.length = lehmerKappa t := by
  simp [lehmerLower, lehmerUpper, lehmerCompletions_length ht]

/-- **Spoof Lehmer factorizations with a base $1$ are trivial.** If a finite multiset $F$ of pairs
$(x, a)$ of natural numbers is a $k$-Lehmer factorization for some integer $k$, and some pair in
$F$ has base $x = 1$, then every base of $F$ equals $1$, that is, $F$ is trivial.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Proposition 1 (`integers-2026-A33-prop-1`). -/
public theorem_wanted isTrivialSpoof_of_isSpoofLehmer_of_one_mem (F : Multiset (ℕ × ℕ))
    (hL : ∃ k : ℤ, IsSpoofLehmer k F) (h1 : ∃ p ∈ F, p.1 = 1) :
    IsTrivialSpoof F

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

/-- **Bounds and monotonicity of the Lehmer function.** For real numbers $t_1, \dots, t_r$ let
$\kappa_r(t_1, \dots, t_r) = (t_1 \cdots t_r - 1) / ((t_1 - 1) \cdots (t_r - 1))$. Let $r \ge 2$
and let $t_1, \dots, t_r \ge 2$ be real numbers. Then
$1 < \kappa_r(t_1, \dots, t_r) \le 2^r - 1$. Moreover, for every index $j$ and every real
$y > t_j$, replacing $t_j$ by $y$ strictly decreases $\kappa_r$, that is,
$\kappa_r(t_1, \dots, t_{j-1}, y, t_{j+1}, \dots, t_r) < \kappa_r(t_1, \dots, t_r)$.

The hypothesis $r \ge 2$ is needed: $\kappa_1(t) = 1$ for every $t \ge 2$, so for $r = 1$ the
lower bound fails and $\kappa_1$ is not strictly decreasing.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 5 (`integers-2026-A33-thm-5`). -/
public theorem_wanted lehmerKappa_antitone_bounds (r : ℕ) (hr : 2 ≤ r) (t : List ℝ)
    (hlen : t.length = r)
    (ht : ∀ x ∈ t, 2 ≤ x) :
    (1 < lehmerKappa t ∧ lehmerKappa t ≤ 2 ^ r - 1) ∧
      ∀ (j : ℕ) (hj : j < t.length) (y : ℝ), t[j] < y → lehmerKappa (t.set j y) < lehmerKappa t

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
