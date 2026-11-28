/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.PowerSeries.Basic
import MathlibExt.NumberTheory.Recurrences.CRecursiveModModRepresentation

/-!
# Double remainders with a negative free term

When the constant term of the reversed denominator is negative, the sign-dependent formula
has zero offset and an unnegated numerator. Multiplying by the absolute value of that term
recovers an integer identity.

## References

* M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
  Journal of Integer Sequences 28 (2025), Article 25.5.3, pp. 1–10, Theorem 8 (negative free
  term) and Corollary 9. Their proof of Theorem 8 uses Corollary 3 and Lemma 7(i).
* M. Prunescu and L. Sauras-Altuzarra, *On the representation of C-recursive integer sequences
  by arithmetic terms*, Journal of Difference Equations and Applications 31 (2025), no. 9,
  1263–1285, Lemma 4 and Theorems 1 and 2, credited for the growth bound and the div-mod
  representation used by Prunescu and Shunia in Lemma 1 and Theorem 2.
* G. Everest, A. van der Poorten, I. Shparlinski, and T. Ward, *Recurrence Sequences*,
  Mathematical Surveys and Monographs 104, American Mathematical Society (2003), also cited
  by Prunescu and Shunia for the growth bound in Lemma 1.
* M. Prunescu, *On other two representations of the C-recursive integer sequences by terms in
  modular arithmetic*, Journal of Symbolic Computation 130 (2025), Article 102433, for the
  earlier, eventual mod-mod representation discussed in Section 1 of Prunescu and Shunia.
-/

namespace MetaMathlibExt

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
public theorem exists_mod_mod_representation_of_neg_free_term
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
            A.reverse.eval ((r : ℤ) ^ n)) % B.reverse.eval ((r : ℤ) ^ n) % (r : ℤ) ^ n := by
  obtain ⟨r, _, hr⟩ := exists_mod_mod_representation_sign t A B c hB0 hAB hA hgf hrep
  refine ⟨r, fun n hn => ?_⟩
  have hrn := hr n hn
  rw [Int.sign_eq_neg_one_of_neg hα] at hrn
  simp only [Int.cast_neg, Int.cast_one, sub_self, zero_div, zero_add, neg_neg, one_mul,
    one_div_mul_eq_div] at hrn
  have ha : |(B.reverse.coeff 0 : ℚ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hα.ne)
  have hmul := (eq_div_iff ha).mp hrn
  rw [mul_comm]
  exact_mod_cast hmul

end MetaMathlibExt
