/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.PowerSeries.Basic

namespace MetaMathlibExt

@[expose] public section

/--
**Term extraction from the generating function under cube-root growth.** Let
$t_0, t_1, t_2, \dots$ be natural numbers and let $c \ge 8$ be a natural number. Suppose that
the real series $\sum_{k \ge 0} t_k c^{-k}$ is summable and that $t_n < c^{n/3}$, a real power,
for every $n \ge 1$. Then for every $n \ge 1$,

$$t_n = \Bigl\lfloor c^{n^2} \sum_{k \ge 0} t_k \, (c^{-n})^k \Bigr\rfloor \bmod c^n.$$

Summability at $c^{-1}$ stands in for the paper's hypothesis that $c^{-1}$ lies inside the
radius of convergence of the generating function. It is implied by that hypothesis but is
strictly weaker, so this statement is stronger than the paper's.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 2, second part.
-/
public theorem_wanted generating_function_term_extraction_of_one_third_growth
    (t : ℕ → ℕ) (c : ℕ)
    (hc : 8 ≤ c)
    (hconv : Summable (fun k : ℕ => (t k : ℝ) * ((c : ℝ)⁻¹) ^ k))
    (hbound : ∀ n, 1 ≤ n → (t n : ℝ) < (c : ℝ) ^ ((n : ℝ) / 3))
    (n : ℕ) (hn : 1 ≤ n) :
    t n = Nat.floor ((c : ℝ) ^ (n ^ 2) *
      (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)) % c ^ n

/--
**Term extraction from the generating function persists in larger bases.** Let
$t_0, t_1, t_2, \dots$ be natural numbers and let $c$, $m$ and $r$ be natural numbers with
$c \ge 2$, $m \ge 2$ and $c \le r$. Suppose that for every $n \ge m$ the real series
$\sum_{k \ge 0} t_k \, (c^{-n})^k$ is summable and

$$t_n = \Bigl\lfloor c^{n^2} \sum_{k \ge 0} t_k \, (c^{-n})^k \Bigr\rfloor \bmod c^n.$$

Then for every $n \ge m$,

$$t_n = \Bigl\lfloor r^{n^2} \sum_{k \ge 0} t_k \, (r^{-n})^k \Bigr\rfloor \bmod r^n.$$

No summability at $r^{-n}$ is assumed: the hypothesis gives $t_n < c^n \le r^n$ for $n \ge m$,
which makes the series at $r^{-n}$ converge.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Corollary 3.
-/
public theorem_wanted generating_function_term_representation_mono_base
    (t : ℕ → ℕ) (c m r : ℕ)
    (hc : 2 ≤ c) (hm : 2 ≤ m) (hcr : c ≤ r)
    (hrep : ∀ n, m ≤ n →
      t n = Nat.floor ((c : ℝ) ^ (n ^ 2) *
        (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)) % c ^ n)
    (hconv : ∀ n, m ≤ n →
      Summable (fun k : ℕ => (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k))
    (n : ℕ) (hmn : m ≤ n) :
    t n = Nat.floor ((r : ℝ) ^ (n ^ 2) *
      (∑' k : ℕ, (t k : ℝ) * (((r : ℝ) ^ n)⁻¹) ^ k)) % r ^ n

/--
**Floor quotient of a negated non-multiple.** Let $A$ and $B$ be integers with $A \ge 1$ and
$B \ge 2$ such that $B$ does not divide $A$. Then
$-\lfloor -A/B \rfloor = \lfloor A/B \rfloor + 1$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 4.
-/
public theorem_wanted neg_ediv_eq_ediv_add_one_of_not_dvd
    (A B : ℤ) (hA : 1 ≤ A) (hB : 2 ≤ B) (hndvd : ¬ B ∣ A) :
    -((-A) / B) = A / B + 1

/--
**Pulling a factor out of a remainder.** Let $a$, $y$ and $C$ be natural numbers with $ay < C$.
Then $(ay) \bmod C = a \cdot (y \bmod C)$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 5.
-/
public theorem_wanted mul_mod_eq_mul_mod_of_mul_lt
    (a y C : ℕ) (hbound : a * y < C) :
    (a * y) % C = a * (y % C)

/--
**Adding one to a remainder without wrap-around.** Let $x$ and $C$ be natural numbers with
$C \ge 2$. If $x \bmod C \ne (C - 1) \bmod C$, that is, if $x$ is not congruent to $C - 1$
modulo $C$, then $(x + 1) \bmod C = (x \bmod C) + 1$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 6.
-/
public theorem_wanted add_one_mod_eq_mod_add_one_of_ne
    (x C : ℕ) (hC : 2 ≤ C) (hne : x % C ≠ (C - 1) % C) :
    (x + 1) % C = x % C + 1

/--
**Remainder of a remainder, negative residue case.** Let $a$, $A$, $B$ and $C$ be integers with
$A > 0$, $B > 0$ and $C \ge 2$ such that $C$ divides $A$, $B$ does not divide $A$, $a < 0$ and
$B \equiv a \pmod C$. Write $\lfloor A/B \rfloor$ for the floor of $A/B$ and $X \bmod M$ for the
remainder of $X$ modulo $M$ in $\{0, 1, \dots, M - 1\}$. If
$|a| \cdot (\lfloor A/B \rfloor \bmod C) < C$, then
$(A \bmod B) \bmod C = |a| \cdot (\lfloor A/B \rfloor \bmod C)$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 7(i).
-/
public theorem_wanted emod_emod_eq_abs_mul_ediv_emod_of_neg
    (a A B C : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 2 ≤ C)
    (hCA : C ∣ A) (hBA : ¬ B ∣ A)
    (hcongr : B % C = a % C) (ha : a < 0)
    (hbound : |a| * ((A / B) % C) < C) :
    (A % B) % C = |a| * ((A / B) % C)

/--
**Remainder of a remainder, positive residue case.** Let $a$, $A$, $B$ and $C$ be integers with
$A > 0$, $B > 0$ and $C \ge 2$ such that $C$ divides $A$, $B$ does not divide $A$, $a > 0$ and
$B \equiv a \pmod C$. Write $\lfloor A/B \rfloor$ for the floor of $A/B$ and $X \bmod M$ for the
remainder of $X$ modulo $M$ in $\{0, 1, \dots, M - 1\}$. If
$a + a \cdot (\lfloor A/B \rfloor \bmod C) < C$, then
$((-A) \bmod B) \bmod C = a \cdot \bigl(1 + (\lfloor A/B \rfloor \bmod C)\bigr)$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 7(ii).
-/
public theorem_wanted neg_emod_emod_eq_mul_one_add_ediv_emod_of_pos
    (a A B C : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 2 ≤ C)
    (hCA : C ∣ A) (hBA : ¬ B ∣ A)
    (hcongr : B % C = a % C) (ha : 0 < a)
    (hbound : a + a * ((A / B) % C) < C) :
    ((-A) % B) % C = a * (1 + (A / B) % C)

/--
**Mod-mod representation of C-recursive sequences, negative free term.** Let
$t_0, t_1, t_2, \dots$ be natural numbers, let $c$ be a natural number, and let $A$ and $B$ be
polynomials with integer coefficients such that $A \ne 0$, $B(0) = 1$ and
$k = \deg A < d = \deg B$. Suppose that $\bigl(\sum_{n \ge 0} t_n z^n\bigr) B(z) = A(z)$ as
formal power series. Let $\tilde A(x) = x^k A(1/x)$ and $\tilde B(x) = x^d B(1/x)$ be the
reversed polynomials, let $\alpha$ be the constant term of $\tilde B$, that is, the leading
coefficient of $B$, and for an integer $x$ put $P_x(n) = x^{n^2} x^{n(d-k)} \tilde A(x^n)$. For
integers $X$ and $M \ne 0$, write $X \bmod M$ for the remainder of $X$ modulo $M$ in
$\{0, 1, \dots, |M| - 1\}$, and set $X \bmod 0 = X$. Suppose that for every $n \ge 1$,

$$t_n = \bigl\lfloor P_c(n) / \tilde B(c^n) \bigr\rfloor \bmod c^n,$$

where the quotient is taken in $\mathbb{Q}$ and is $0$ when $\tilde B(c^n) = 0$. If $\alpha < 0$,
then there is a natural number $r$ such that for every $n \ge 1$,

$$|\alpha| \, t_n = \bigl( P_r(n) \bmod \tilde B(r^n) \bigr) \bmod r^n.$$

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 8, negative free term.
-/
public theorem_wanted exists_mod_mod_representation_of_neg_free_term
    (t : ℕ → ℕ) (A B : Polynomial ℤ) (c : ℕ)
    (hB0 : B.coeff 0 = 1) (hAB : A.natDegree < B.natDegree) (hA : A ≠ 0)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ))
    (hrep : ∀ n, 1 ≤ n →
      (t n : ℤ) = ⌊((c : ℚ) ^ (n ^ 2) * (c : ℚ) ^ (n * (B.natDegree - A.natDegree)) *
          A.reverse.eval ((c : ℤ) ^ n)) / B.reverse.eval ((c : ℤ) ^ n)⌋ % (c : ℤ) ^ n)
    (hα : B.reverse.coeff 0 < 0) :
    ∃ r : ℕ, ∀ n, 1 ≤ n →
      |B.reverse.coeff 0| * (t n : ℤ) =
        ((r : ℤ) ^ (n ^ 2) * (r : ℤ) ^ (n * (B.natDegree - A.natDegree)) *
            A.reverse.eval ((r : ℤ) ^ n)) % B.reverse.eval ((r : ℤ) ^ n) % (r : ℤ) ^ n

/--
**Mod-mod representation of C-recursive sequences, positive free term.** Let
$t_0, t_1, t_2, \dots$ be natural numbers, let $c$ be a natural number, and let $A$ and $B$ be
polynomials with integer coefficients such that $A \ne 0$, $B(0) = 1$ and
$k = \deg A < d = \deg B$. Suppose that $\bigl(\sum_{n \ge 0} t_n z^n\bigr) B(z) = A(z)$ as
formal power series. Let $\tilde A(x) = x^k A(1/x)$ and $\tilde B(x) = x^d B(1/x)$ be the
reversed polynomials, let $\alpha$ be the constant term of $\tilde B$, that is, the leading
coefficient of $B$, and for an integer $x$ put $P_x(n) = x^{n^2} x^{n(d-k)} \tilde A(x^n)$. For
integers $X$ and $M \ne 0$, write $X \bmod M$ for the remainder of $X$ modulo $M$ in
$\{0, 1, \dots, |M| - 1\}$, and set $X \bmod 0 = X$. Suppose that for every $n \ge 1$,

$$t_n = \bigl\lfloor P_c(n) / \tilde B(c^n) \bigr\rfloor \bmod c^n,$$

where the quotient is taken in $\mathbb{Q}$ and is $0$ when $\tilde B(c^n) = 0$. If $\alpha > 0$,
then there is a natural number $r$ such that for every $n \ge 1$,

$$\alpha \, (t_n + 1) = \bigl( (-P_r(n)) \bmod \tilde B(r^n) \bigr) \bmod r^n.$$

The hypothesis $A \ne 0$ is needed: for $A = 0$ and $B(z) = 1 + z$ the left side is $1$ and the
right side is $0$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 8, positive free term.
-/
public theorem_wanted exists_mod_mod_representation_of_pos_free_term
    (t : ℕ → ℕ) (A B : Polynomial ℤ) (c : ℕ)
    (hB0 : B.coeff 0 = 1) (hAB : A.natDegree < B.natDegree) (hA : A ≠ 0)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ))
    (hrep : ∀ n, 1 ≤ n →
      (t n : ℤ) = ⌊((c : ℚ) ^ (n ^ 2) * (c : ℚ) ^ (n * (B.natDegree - A.natDegree)) *
          A.reverse.eval ((c : ℤ) ^ n)) / B.reverse.eval ((c : ℤ) ^ n)⌋ % (c : ℤ) ^ n)
    (hα : 0 < B.reverse.coeff 0) :
    ∃ r : ℕ, ∀ n, 1 ≤ n →
      B.reverse.coeff 0 * ((t n : ℤ) + 1) =
        (-((r : ℤ) ^ (n ^ 2) * (r : ℤ) ^ (n * (B.natDegree - A.natDegree)) *
            A.reverse.eval ((r : ℤ) ^ n))) % B.reverse.eval ((r : ℤ) ^ n) % (r : ℤ) ^ n

/--
**Single-formula mod-mod representation of C-recursive sequences.** Let
$t_0, t_1, t_2, \dots$ be natural numbers, let $c$ be a natural number, and let $A$ and $B$ be
polynomials with integer coefficients such that $A \ne 0$, $B(0) = 1$ and
$k = \deg A < d = \deg B$. Suppose that $\bigl(\sum_{n \ge 0} t_n z^n\bigr) B(z) = A(z)$ as
formal power series. Let $\tilde A(x) = x^k A(1/x)$ and $\tilde B(x) = x^d B(1/x)$ be the
reversed polynomials, let $\alpha$ be the constant term of $\tilde B$, that is, the leading
coefficient of $B$, and for an integer $x$ put $P_x(n) = x^{n^2} x^{n(d-k)} \tilde A(x^n)$. For
integers $X$ and $M \ne 0$, write $X \bmod M$ for the remainder of $X$ modulo $M$ in
$\{0, 1, \dots, |M| - 1\}$, and set $X \bmod 0 = X$. Suppose that for every $n \ge 1$,

$$t_n = \bigl\lfloor P_c(n) / \tilde B(c^n) \bigr\rfloor \bmod c^n,$$

where the quotient is taken in $\mathbb{Q}$ and is $0$ when $\tilde B(c^n) = 0$. Put
$\sigma = \operatorname{sgn} \alpha$; note $\alpha \ne 0$ because $B \ne 0$. Then there is a
natural number $r \ge c$ such that for every $n \ge 1$, writing
$\rho_n = \bigl( (-\sigma P_r(n)) \bmod \tilde B(r^n) \bigr) \bmod r^n$, the rational numbers
satisfy

$$t_n = \frac{-1 - \sigma}{2} + \frac{\rho_n}{|\alpha|}.$$

The hypothesis $A \ne 0$ excludes the zero sequence: for $A = 0$ and $B(z) = 1 + z$ the right
side is $-1$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Corollary 9.
-/
public theorem_wanted exists_mod_mod_representation_sign
    (t : ℕ → ℕ) (A B : Polynomial ℤ) (c : ℕ)
    (hB0 : B.coeff 0 = 1) (hAB : A.natDegree < B.natDegree) (hA : A ≠ 0)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ))
    (hrep : ∀ n, 1 ≤ n →
      (t n : ℤ) = ⌊((c : ℚ) ^ (n ^ 2) * (c : ℚ) ^ (n * (B.natDegree - A.natDegree)) *
          A.reverse.eval ((c : ℤ) ^ n)) / B.reverse.eval ((c : ℤ) ^ n)⌋ % (c : ℤ) ^ n) :
    ∃ r : ℕ, c ≤ r ∧ ∀ n, 1 ≤ n →
      (t n : ℚ) = (-1 - (B.reverse.coeff 0).sign : ℚ) / 2 +
        (1 / |(B.reverse.coeff 0 : ℚ)|) *
          (((-(B.reverse.coeff 0).sign * ((r : ℤ) ^ (n ^ 2) *
              (r : ℤ) ^ (n * (B.natDegree - A.natDegree)) * A.reverse.eval ((r : ℤ) ^ n))) %
            B.reverse.eval ((r : ℤ) ^ n) % (r : ℤ) ^ n : ℤ) : ℚ)

end

end MetaMathlibExt
