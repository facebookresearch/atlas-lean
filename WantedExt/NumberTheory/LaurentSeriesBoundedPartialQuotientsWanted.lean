/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

namespace MetaMathlibExt

@[expose] public noncomputable section

section LaurentContinuedFraction

variable {K : Type*} [Field K]

/-- **The variable $x$ of $K((x^{-1}))$.** Let $K$ be a field. Formal Laurent series in $x^{-1}$
over $K$ are realized as Laurent series $\sum_n c_n X^n$ in $X = x^{-1}$, and the variable $x$
is the series $X^{-1}$, with coefficient $1$ at $X^{-1}$ and $0$ elsewhere.

A series $\alpha = \sum_n c_n x^{-n} \ne 0$ has absolute value $|\alpha| = |x|^{-v(\alpha)}$,
where its order $v(\alpha)$ is the least $n$ with $c_n \ne 0$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1. -/
def laurentInvVar (K : Type*) [Field K] : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) (1 : K)

/-- **The variable $x$ times $x^{-1}$ is one.** Let $K$ be a field. In $K((x^{-1}))$, the
product of the variable $x$ and the series $x^{-1}$ (coefficient $1$ at $x^{-1}$ and $0$
elsewhere) is $1$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1. -/
theorem laurentInvVar_mul_single_one :
    laurentInvVar K * HahnSeries.single (1 : ℤ) (1 : K) = 1 := by
  simp [laurentInvVar, HahnSeries.single_mul_single]

/-- **Polynomials as Laurent series in the inverse variable.** Let $K$ be a field. The embedding
$K[x] \to K((x^{-1}))$ is the $K$-algebra homomorphism that sends $x$ to the element $x$ of
$K((x^{-1}))$, that is, it evaluates a polynomial at $x$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1. -/
def polyToLaurentInv (p : Polynomial K) : LaurentSeries K :=
  Polynomial.aeval (laurentInvVar K) p

/-- **The polynomial variable embeds as the Laurent variable.** Let $K$ be a field. The
embedding $K[x] \to K((x^{-1}))$ sends the polynomial $x$ to the element $x$ of
$K((x^{-1}))$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1. -/
theorem polyToLaurentInv_X : polyToLaurentInv (Polynomial.X : Polynomial K) = laurentInvVar K := by
  simp [polyToLaurentInv]

/-- **Polynomial part of a Laurent series.** Let $K$ be a field and write a Laurent series
$\alpha \in K((x^{-1}))$ as $\alpha = \sum_n c_n x^{-n}$. Its polynomial part is
$[\alpha] = \sum_{n \le 0} c_n x^{-n}$, the sum of the terms in nonnegative powers of $x$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
def laurentPolyPart (α : LaurentSeries K) : LaurentSeries K where
  coeff n := if n ≤ 0 then α.coeff n else 0
  isPWO_support' := α.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn
    split_ifs at hn with h
    · exact hn
    · exact (hn rfl).elim

/-- **Coefficients of the polynomial part of a Laurent series.** Let $K$ be a field and write
$\alpha \in K((x^{-1}))$ as $\alpha = \sum_n c_n x^{-n}$. For every integer $n$, the coefficient
of $x^{-n}$ in the polynomial part $[\alpha]$ is $c_n$ if $n \le 0$ and $0$ if $n > 0$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
theorem laurentPolyPart_coeff (α : LaurentSeries K) (n : ℤ) :
    (laurentPolyPart α).coeff n = if n ≤ 0 then α.coeff n else 0 :=
  rfl

/-- **Polynomial parts of the variable and its inverse.** Let $K$ be a field. In
$K((x^{-1}))$ the polynomial part of $x$ is $x$, and the polynomial part of $x^{-1}$ is $0$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
theorem laurentPolyPart_laurentInvVar :
    laurentPolyPart (laurentInvVar K) = laurentInvVar K ∧
      laurentPolyPart (HahnSeries.single (1 : ℤ) (1 : K)) = 0 := by
  constructor
  · ext n
    simp only [laurentPolyPart_coeff, laurentInvVar, HahnSeries.coeff_single]
    split_ifs <;> first | rfl | omega
  · ext n
    simp only [laurentPolyPart_coeff, HahnSeries.coeff_single, HahnSeries.coeff_zero]
    split_ifs with h₁ h₂ <;> first | rfl | omega

/-- **Complete quotients of a Laurent series.** Let $K$ be a field and $\alpha \in K((x^{-1}))$. The
complete quotients of the continued fraction expansion of $\alpha$ are $\alpha_0 = \alpha$ and
$\alpha_{n+1} = (\alpha_n - [\alpha_n])^{-1}$ for $n \ge 0$, where $[\beta]$ is the polynomial part
of $\beta$ and $0^{-1} = 0$. So the complete quotients become $0$ after a finite expansion ends.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
def laurentCompleteQuotient (α : LaurentSeries K) : ℕ → LaurentSeries K
  | 0 => α
  | n + 1 => (laurentCompleteQuotient α n - laurentPolyPart (laurentCompleteQuotient α n))⁻¹

/-- **Partial quotients of a Laurent series.** Let $K$ be a field, $\alpha \in K((x^{-1}))$ and
$n \ge 0$. The $n$-th partial quotient of $\alpha$ is $b_n = [\alpha_n]$, the polynomial part of
the $n$-th complete quotient $\alpha_n$ of $\alpha$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
def laurentPartialQuotient (α : LaurentSeries K) (n : ℕ) : LaurentSeries K :=
  laurentPolyPart (laurentCompleteQuotient α n)

/-- **First step of the continued fraction of a Laurent series.** Let $K$ be a field and
$\alpha \in K((x^{-1}))$. The partial quotient $b_0$ of $\alpha$ is its polynomial part
$[\alpha]$, and the complete quotient $\alpha_1$ is $(\alpha - [\alpha])^{-1}$, where
$0^{-1} = 0$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
theorem laurentPartialQuotient_zero (α : LaurentSeries K) :
    laurentPartialQuotient α 0 = laurentPolyPart α ∧
      laurentCompleteQuotient α 1 = (α - laurentPolyPart α)⁻¹ :=
  ⟨rfl, rfl⟩

/-- **Laurent series with bounded partial quotients.** Let $K$ be a field. A Laurent series
$\alpha \in K((x^{-1}))$ with partial quotients $b_0, b_1, \dots$ has bounded partial quotients
if there is an integer $B$ such that for every $n \ge 0$ and every integer $k > B$ the
coefficient of $x^k$ in $b_n$ is zero, that is, every nonzero $b_n$ is a polynomial in $x$ of
degree at most $B$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
def LaurentHasBoundedPartialQuotients (α : LaurentSeries K) : Prop :=
  ∃ B : ℤ, ∀ n : ℕ, ∀ m : ℤ, m < -B → (laurentPartialQuotient α n).coeff m = 0

/-- **Numerators of the convergents of a Laurent series.** Let $K$ be a field and let
$\alpha \in K((x^{-1}))$ have partial quotients $b_0, b_1, \dots$. The numerators of the
convergents of $\alpha$ are $P_{-1} = 1$, $P_0 = b_0$ and $P_{n+1} = b_{n+1} P_n + P_{n-1}$ for
$n \ge 0$. The sequence is indexed with a shift of one: its term at $n \ge 0$ is $P_{n-1}$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
def laurentConvNum (α : LaurentSeries K) : ℕ → LaurentSeries K
  | 0 => 1
  | 1 => laurentPartialQuotient α 0
  | n + 2 => laurentPartialQuotient α (n + 1) * laurentConvNum α (n + 1) + laurentConvNum α n

/-- **Denominators of the convergents.** Let $K$ be a field, let $\alpha \in K((x^{-1}))$ and let
$b_0, b_1, \dots$ be its partial quotients. The denominators of the convergents of $\alpha$ are
given by $Q_{-1} = 0$, $Q_0 = 1$ and $Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$ for $n \ge 0$. They are
indexed from $0$ here: the $k$-th term of the sequence is $Q_{k-1}$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
def laurentConvDen (α : LaurentSeries K) : ℕ → LaurentSeries K
  | 0 => 0
  | 1 => 1
  | n + 2 => laurentPartialQuotient α (n + 1) * laurentConvDen α (n + 1) + laurentConvDen α n

/-- **The convergent $P_1 / Q_1$ of a Laurent series.** Let $K$ be a field and let
$\alpha \in K((x^{-1}))$ have partial quotients $b_0, b_1, \dots$. Let $P_n$ and $Q_n$ be the
numerators and denominators of its convergents, given by $P_{-1} = 1$, $Q_{-1} = 0$, $P_0 = b_0$,
$Q_0 = 1$, $P_{n+1} = b_{n+1} P_n + P_{n-1}$ and $Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$. Then
$P_1 = b_1 b_0 + 1$ and $Q_1 = b_1$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
theorem laurentConv_two (α : LaurentSeries K) :
    laurentConvNum α 2 = laurentPartialQuotient α 1 * laurentPartialQuotient α 0 + 1 ∧
      laurentConvDen α 2 = laurentPartialQuotient α 1 := by
  simp [laurentConvNum, laurentConvDen]

/-- **Irrational Laurent series.** Let $K$ be a field. A Laurent series $\alpha \in K((x^{-1}))$
is irrational if $Q \alpha \ne P$ for all polynomials $P, Q \in K[x]$ with $Q \ne 0$, where
polynomials are embedded in $K((x^{-1}))$ by sending $x$ to the variable $x$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
def LaurentIsIrrational (α : LaurentSeries K) : Prop :=
  ∀ P Q : Polynomial K, Q ≠ 0 → polyToLaurentInv Q * α ≠ polyToLaurentInv P

/-- **Polynomials are not irrational.** Let $K$ be a field. For every polynomial $P \in K[x]$,
the image of $P$ in $K((x^{-1}))$ is not irrational.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
theorem not_laurentIsIrrational_polyToLaurentInv (P : Polynomial K) :
    ¬ LaurentIsIrrational (polyToLaurentInv P) := fun h =>
  h P 1 one_ne_zero (by simp [polyToLaurentInv])

/-- **Baum–Sweet: cubics with bounded partial quotients.** Let $p \in \mathbb{F}_2[x]$ have degree
at least $1$. If $f \in \mathbb{F}_2((x^{-1}))$ satisfies $f^3 + p^{-1} f + 1 = 0$, then $f$ has
bounded partial quotients.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Theorem 1 (quoting Baum and Sweet, Corollary 3) (`integers-2026-A57-thm-1`). -/
public theorem_wanted baumSweet_cubic_boundedPartialQuotients (p : Polynomial (ZMod 2))
    (hp : 1 ≤ p.natDegree) (f : LaurentSeries (ZMod 2))
    (hf : f ^ 3 + (polyToLaurentInv p)⁻¹ * f + 1 = 0) :
    LaurentHasBoundedPartialQuotients f

/-- **Baum–Sweet: unbounded partial quotients for higher degrees.** Let $n > 1$ and let
$g \in \mathbb{F}_2[x]$ have degree at least $1$. If $f \in \mathbb{F}_2((x^{-1}))$ satisfies
$f^{2^n+1} + g^{-1} f + 1 = 0$, then $f$ does not have bounded partial quotients.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Theorem 2 (quoting Baum and Sweet, Theorem 5) (`integers-2026-A57-thm-2`). -/
public theorem_wanted baumSweet_unboundedPartialQuotients (n : ℕ) (hn : 1 < n)
    (g : Polynomial (ZMod 2)) (hg : 1 ≤ g.natDegree) (f : LaurentSeries (ZMod 2))
    (hf : f ^ (2 ^ n + 1) + (polyToLaurentInv g)⁻¹ * f + 1 = 0) :
    ¬ LaurentHasBoundedPartialQuotients f

/-- **Baum–Sweet: explicit continued fractions of roots.** Let $n \ge 0$ and let
$P, Q \in \mathbb{F}_2[x]$ with $P + Q^{2^n} \ne 0$ and $P + Q^{2^n} \ne 1$. Then some
$f \in \mathbb{F}_2((x^{-1}))$ satisfies $f^{2^n+1} + Q f^{2^n} + P f + QP + 1 = 0$ and has partial
quotients $b_0 = Q$ and $b_k = P^{2^{(k-1)n}} + Q^{2^{kn}}$ for all $k \ge 1$, that is,
$f = [Q; P + Q^{2^n}, P^{2^n} + Q^{2^{2n}}, P^{2^{2n}} + Q^{2^{3n}}, \dots]$.

The paper also claims that this root is unique, which fails: for $n = 0$, $P = x$ and $Q = 0$ the
equation $f(f + x) = 1$ has the two roots $[0; x, x, \dots]$ and $[x; x, x, \dots]$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Theorem 3 (quoting Baum and Sweet) (`integers-2026-A57-thm-3`). -/
public theorem_wanted baumSweet_exists_root_continuedFraction (n : ℕ)
    (P Q : Polynomial (ZMod 2)) (h0 : P + Q ^ (2 ^ n) ≠ 0) (h1 : P + Q ^ (2 ^ n) ≠ 1) :
    ∃ f : LaurentSeries (ZMod 2),
      f ^ (2 ^ n + 1) + polyToLaurentInv Q * f ^ (2 ^ n) + polyToLaurentInv P * f +
          polyToLaurentInv Q * polyToLaurentInv P + 1 = 0 ∧
        laurentPartialQuotient f 0 = polyToLaurentInv Q ∧
        ∀ k, 1 ≤ k → laurentPartialQuotient f k =
          polyToLaurentInv (P ^ (2 ^ ((k - 1) * n)) + Q ^ (2 ^ (k * n)))

/-- **Basic properties of the convergents of a Laurent series.** Let $K$ be a field and let
$\alpha \in K((x^{-1}))$ be irrational, with partial quotients $b_0, b_1, \dots$ and convergents
$P_n / Q_n$, where $P_{-1} = 1$, $Q_{-1} = 0$, $P_0 = b_0$, $Q_0 = 1$,
$P_{n+1} = b_{n+1} P_n + P_{n-1}$ and $Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$. For a Laurent series
$y = \sum_m c_m x^{-m}$ let $v(y)$ be its order, the least $m$ with $c_m \ne 0$, and let
$v(0) = 0$; thus $|y| = |x|^{-v(y)}$ for $y \ne 0$. For $\beta \in K((x^{-1}))$ write
$[b_k, \dots, b_n, \beta] = b_k + 1/(b_{k+1} + 1/(\cdots + 1/(b_n + 1/\beta)))$. Then:
(i) for every $n \ge 0$ and every $\beta \ne 0$ such that $[b_k, \dots, b_n, \beta] \ne 0$ for
all $1 \le k \le n$, $(\beta P_n + P_{n-1}) / (\beta Q_n + Q_{n-1}) = [b_0, \dots, b_n, \beta]$;
(ii) $P_n Q_{n-1} - P_{n-1} Q_n = (-1)^{n+1}$ for every $n \ge 0$;
(iii) $Q_{n-1} \ne 0$ and $v(Q_n) < v(Q_{n-1})$ for every $n \ge 1$;
(iv) $v(Q_n) = v(b_1) + \dots + v(b_n)$ for every $n \ge 1$;
(v) $v(\alpha - P_n / Q_n) = -v(b_{n+1}) - 2 v(Q_n)$ for every $n \ge 1$;
(vi) $v(Q_n \alpha - P_n) < v(Q_{n+1} \alpha - P_{n+1})$ for every $n \ge 1$.

Part (iii) fails at $n = 0$ because $Q_{-1} = 0$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 1 (`integers-2026-A57-lem-1`). -/
public theorem_wanted laurentConvergent_properties (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) :
    (∀ n : ℕ, ∀ β : LaurentSeries K, β ≠ 0 →
        (∀ k, 1 ≤ k → k ≤ n → ((List.range' k (n + 1 - k)).map (laurentPartialQuotient α)).foldr
          (fun b t => b + t⁻¹) β ≠ 0) →
        (β * laurentConvNum α (n + 1) + laurentConvNum α n) /
            (β * laurentConvDen α (n + 1) + laurentConvDen α n) =
          ((List.range (n + 1)).map (laurentPartialQuotient α)).foldr (fun b t => b + t⁻¹) β) ∧
      (∀ n : ℕ, laurentConvNum α (n + 1) * laurentConvDen α n -
          laurentConvNum α n * laurentConvDen α (n + 1) = (-1) ^ (n + 1)) ∧
      (∀ n : ℕ, 1 ≤ n → laurentConvDen α n ≠ 0 ∧
          (laurentConvDen α (n + 1)).order < (laurentConvDen α n).order) ∧
      (∀ n : ℕ, 1 ≤ n → (laurentConvDen α (n + 1)).order =
          ∑ i ∈ Finset.Icc 1 n, (laurentPartialQuotient α i).order) ∧
      (∀ n : ℕ, 1 ≤ n → (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order =
          -(laurentPartialQuotient α (n + 1)).order - 2 * (laurentConvDen α (n + 1)).order) ∧
      (∀ n : ℕ, 1 ≤ n → (laurentConvDen α (n + 1) * α - laurentConvNum α (n + 1)).order <
          (laurentConvDen α (n + 2) * α - laurentConvNum α (n + 2)).order)

/-- **Frobenius acts on continued fractions of Laurent series.** Let $K$ be a finite field with
$q$ elements and let $\alpha \in K((x^{-1}))$, with partial quotients $b_0, b_1, \dots$ and
convergent numerators and denominators $P_n, Q_n$, where $P_{-1} = 1$ and $Q_{-1} = 0$. Then for
every $n \ge 0$ the $n$-th partial quotient of $\alpha^q$ is $b_n^q$, and for every $n \ge -1$
the convergent numerator and denominator of $\alpha^q$ of index $n$ are $P_n^q$ and $Q_n^q$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 2 (`integers-2026-A57-lem-2`). -/
public theorem_wanted laurentPartialQuotient_pow_card [Fintype K] (α : LaurentSeries K) (n : ℕ) :
    laurentPartialQuotient (α ^ Fintype.card K) n =
        laurentPartialQuotient α n ^ Fintype.card K ∧
      laurentConvNum (α ^ Fintype.card K) n = laurentConvNum α n ^ Fintype.card K ∧
      laurentConvDen (α ^ Fintype.card K) n = laurentConvDen α n ^ Fintype.card K

/-- **Close rational approximations and convergents.** Let $K$ be a field and let
$\alpha \in K((x^{-1}))$ be irrational, with partial quotients $b_0, b_1, \dots$ and convergents
$P_n / Q_n$, where $P_{-1} = 1$, $Q_{-1} = 0$, $P_0 = b_0$, $Q_0 = 1$,
$P_{n+1} = b_{n+1} P_n + P_{n-1}$ and $Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$. For a Laurent series
$y = \sum_m c_m x^{-m}$ let $v(y)$ be its order, the least $m$ with $c_m \ne 0$, and let
$v(0) = 0$. Let $P, Q \in K[x]$ be coprime with $Q \ne 0$.
(i) If $v(Q \alpha - P) = s + \deg Q$ for some integer $s \ge 1$, then there are $n \ge 0$ and
$c \in K \setminus \{0\}$ with $P = c P_n$, $Q = c Q_n$ and $v(b_{n+1}) = -s$.
(ii) If $v(Q \alpha - P) = \deg Q$, then there are $n \ge 0$ and $c, d \in K \setminus \{0\}$
with $P = c P_n + d P_{n-1}$ and $Q = c Q_n + d Q_{n-1}$.

With $|y| = |x|^{-v(y)}$, the hypothesis of (i) reads $|Q \alpha - P| = |x|^{-s} |Q|^{-1}$ and
its conclusion $|b_{n+1}| = |x|^s$; the hypothesis of (ii) reads $|Q \alpha - P| = |Q|^{-1}$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 3 (generalizing Baum and Sweet, Lemma 1) (`integers-2026-A57-lem-3`). -/
public theorem_wanted laurent_eq_convergent_of_order (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0) :
    (∀ s : ℕ, 1 ≤ s →
        (polyToLaurentInv Q * α - polyToLaurentInv P).order = s + Q.natDegree →
        ∃ (n : ℕ) (c : K), c ≠ 0 ∧
          polyToLaurentInv P = HahnSeries.C c * laurentConvNum α (n + 1) ∧
          polyToLaurentInv Q = HahnSeries.C c * laurentConvDen α (n + 1) ∧
          (laurentPartialQuotient α (n + 1)).order = -(s : ℤ)) ∧
      ((polyToLaurentInv Q * α - polyToLaurentInv P).order = Q.natDegree →
        ∃ (n : ℕ) (c d : K), c ≠ 0 ∧ d ≠ 0 ∧
          polyToLaurentInv P =
            HahnSeries.C c * laurentConvNum α (n + 1) + HahnSeries.C d * laurentConvNum α n ∧
          polyToLaurentInv Q =
            HahnSeries.C c * laurentConvDen α (n + 1) + HahnSeries.C d * laurentConvDen α n)

/-- **Distance from an irrational Laurent series to its convergents.** Let $K$ be a field, let
$\alpha \in K((x^{-1}))$ be irrational with convergents $P_n/Q_n$ ($n \ge 0$), and for nonzero
$y \in K((x^{-1}))$ let $|y| = |x|^{\deg y}$, where $\deg y$ is the largest exponent of $x$
occurring in $y$ and $|x| > 1$ is fixed. (i) If $|\alpha| \ge 1$, then
$|\alpha - P_n/Q_n| < |\alpha|$ for all $n \ge 0$. (ii) If $|\alpha| < 1$, then
$|\alpha - P_0/Q_0| = |\alpha|$ and $|\alpha - P_n/Q_n| < |\alpha|$ for all $n \ge 1$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 4 (`integers-2026-A57-lem-4`). -/
public theorem_wanted laurent_sub_convergent_order (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) :
    (α.order ≤ 0 → ∀ n : ℕ,
        α.order < (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order) ∧
      (0 < α.order →
        (α - laurentConvNum α 1 / laurentConvDen α 1).order = α.order ∧
          ∀ n : ℕ, 1 ≤ n →
            α.order < (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order)

/-- **Lasjaunias's bound on the next partial quotient.** Let $\mathbb{F}_q$ be a finite field, let
$A, B, C, D \in \mathbb{F}_q[x]$ with $\Delta = AD - BC \ne 0$ and $C \ne 0$, and let
$\alpha \in \mathbb{F}_q((x^{-1}))$ be irrational with $\alpha = (A\alpha^q + B)/(C\alpha^q + D)$.
Write $|y| = |x|^{\deg y}$ for the absolute value on $\mathbb{F}_q((x^{-1}))$, where $\deg y$ is
the largest exponent of $x$ occurring in $y \ne 0$, and write $P_n/Q_n$ for the convergents and
$b_n$ for the partial quotients of $\alpha$. Let $n \ge 0$, let $P, Q \in \mathbb{F}_q[x]$ be
coprime with $Q \ne 0$ and $P/Q = P_n/Q_n$, and suppose $|\alpha - P/Q| < |\alpha - A/C|$. Put
$R_1 = DP - BQ$, $S_1 = -CP + AQ$ and $\delta_1 = \gcd(R_1, S_1)$. If $R_1/\delta_1$ or
$S_1/\delta_1$ is not a $q$-th power in $\mathbb{F}_q[x]$, then
$|b_{n+1}| < |\Delta|\,|\delta_1|^{-2}$.

The hypothesis $C \ne 0$, which makes $A/C$ meaningful, is implicit in the paper.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 5 (quoting Lasjaunias, Lemma 1) (`integers-2026-A57-lem-5`). -/
public theorem_wanted lasjaunias_partialQuotient_bound [Fintype K] [DecidableEq K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1))
    (hclose : (α - polyToLaurentInv A / polyToLaurentInv C).order <
      (α - polyToLaurentInv P / polyToLaurentInv Q).order)
    (hpow : (¬ ∃ T : Polynomial K,
        (D * P - B * Q) / gcd (D * P - B * Q) (-C * P + A * Q) = T ^ Fintype.card K) ∨
      ¬ ∃ T : Polynomial K,
        (-C * P + A * Q) / gcd (D * P - B * Q) (-C * P + A * Q) = T ^ Fintype.card K) :
    -(laurentPartialQuotient α (n + 1)).order <
      ((A * D - B * C).natDegree : ℤ) - 2 * (gcd (D * P - B * Q) (-C * P + A * Q)).natDegree

/-- **Difference identities for a Möbius–Frobenius fixed point.** Let $K$ be a finite field with
$q$ elements, let $A, B, C, D \in K[x]$ with $\Delta = AD - BC \ne 0$, and let
$\alpha \in K((x^{-1}))$ be irrational with $\alpha = (A \alpha^q + B) / (C \alpha^q + D)$. Let
$P, Q \in K[x]$ with $Q \ne 0$, put $R_1 = DP - BQ$, $S_1 = -CP + AQ$, $R_2 = AP^q + BQ^q$ and
$S_2 = CP^q + DQ^q$, and assume $S_1 \ne 0$ and $S_2 \ne 0$. Then
$\alpha^q - R_1 / S_1 = \Delta (Q \alpha - P) / ((A - C \alpha) S_1)$ and
$\alpha - R_2 / S_2 = \Delta (Q \alpha - P)^q / ((C \alpha^q + D) S_2)$.

For $C \ne 0$ the conditions $S_1 \ne 0$ and $S_2 \ne 0$ say $P/Q \ne A/C$ and
$(P/Q)^q \ne -D/C$. The source also assumes $\gcd(A, B, C, D) = 1$ and that $P/Q$ is a
convergent of $\alpha$ in lowest terms; the identities do not need these hypotheses.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 6 (`integers-2026-A57-lem-6`). -/
public theorem_wanted laurentMobius_sub_identities [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K) (hQ : Q ≠ 0) (hS₁ : -C * P + A * Q ≠ 0)
    (hS₂ : C * P ^ Fintype.card K + D * Q ^ Fintype.card K ≠ 0) :
    α ^ Fintype.card K - polyToLaurentInv (D * P - B * Q) / polyToLaurentInv (-C * P + A * Q) =
        polyToLaurentInv (A * D - B * C) * (polyToLaurentInv Q * α - polyToLaurentInv P) /
          ((polyToLaurentInv A - polyToLaurentInv C * α) * polyToLaurentInv (-C * P + A * Q)) ∧
      α - polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K) /
          polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) =
        polyToLaurentInv (A * D - B * C) *
            (polyToLaurentInv Q * α - polyToLaurentInv P) ^ Fintype.card K /
          ((polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D) *
            polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K))

/-- **Degree identities at convergents of a Möbius–Frobenius fixed point.** Let $K$ be a finite
field with $q$ elements, let $A, B, C, D \in K[x]$ with $\Delta = AD - BC \ne 0$ and $C \ne 0$,
and let $\alpha \in K((x^{-1}))$ be irrational with $\alpha = (A \alpha^q + B) / (C \alpha^q + D)$.
Let $b_0, b_1, \dots$ be the partial quotients of $\alpha$ and $P_n / Q_n$ its convergents, where
$P_{-1} = 1$, $Q_{-1} = 0$, $P_0 = b_0$, $Q_0 = 1$, $P_{n+1} = b_{n+1} P_n + P_{n-1}$ and
$Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$. For a Laurent series $y = \sum_m c_m x^{-m}$ let $v(y)$ be its
order, the least $m$ with $c_m \ne 0$, and let $v(0) = 0$; thus $|y| = |x|^{-v(y)}$ for
$y \ne 0$. Let $n \ge 0$, let $P, Q \in K[x]$ be coprime with $Q \ne 0$ and $P Q_n = Q P_n$,
and put $R_1 = DP - BQ$, $S_1 = -CP + AQ$, $R_2 = AP^q + BQ^q$ and $S_2 = CP^q + DQ^q$, with
the degree of the zero polynomial taken to be $0$. Then:
(i) if $v(\alpha - A/C) < v(\alpha - P/Q)$, then
$v(S_1 \alpha^q - R_1) = \deg S_1 - \deg \Delta - v(b_{n+1})$;
(ii) if $v(\alpha^q + D/C) < q \, v(\alpha - P/Q)$, then
$v(S_2 \alpha - R_2) = \deg S_2 - \deg \Delta - q \, v(b_{n+1})$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 7, (3.7) and (3.8) (`integers-2026-A57-lem-7`). -/
public theorem_wanted laurentMobius_order_identities [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1)) :
    ((α - polyToLaurentInv A / polyToLaurentInv C).order <
        (α - polyToLaurentInv P / polyToLaurentInv Q).order →
      (polyToLaurentInv (-C * P + A * Q) * α ^ Fintype.card K -
          polyToLaurentInv (D * P - B * Q)).order =
        ((-C * P + A * Q).natDegree : ℤ) - (A * D - B * C).natDegree -
          (laurentPartialQuotient α (n + 1)).order) ∧
      ((α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
          Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order →
        (polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) * α -
            polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K)).order =
          ((C * P ^ Fintype.card K + D * Q ^ Fintype.card K).natDegree : ℤ) -
            (A * D - B * C).natDegree -
            Fintype.card K * (laurentPartialQuotient α (n + 1)).order)

/-- **Lasjaunias's criterion for unbounded partial quotients.** Let $\mathbb{F}_q$ be a finite
field, let $A, B, C, D \in \mathbb{F}_q[x]$ with $\Delta = AD - BC \ne 0$ and $C \ne 0$, and let
$\alpha \in \mathbb{F}_q((x^{-1}))$ be irrational with $\alpha = (A\alpha^q + B)/(C\alpha^q + D)$.
Write $|y| = |x|^{\deg y}$ for the absolute value on $\mathbb{F}_q((x^{-1}))$, where $\deg y$ is
the largest exponent of $x$ occurring in $y \ne 0$, and write $P_n/Q_n$ for the convergents and
$b_n$ for the partial quotients of $\alpha$. Suppose that for some $n \ge 0$ there are coprime
$P, Q \in \mathbb{F}_q[x]$ with $Q \ne 0$ and $P/Q = P_n/Q_n$ such that
$|\alpha - P/Q|^q < |\alpha^q + D/C|$, $|\alpha - P/Q|^{q-1} < |\Delta|\,|C\alpha^q + D|^2$ and
$|b_{n+1}|^{q-1} > |\Delta|$. Then $\alpha$ does not have bounded partial quotients.

In the paper these conditions read $|\alpha - P/Q| < |\alpha^q + D/C|^{1/q}$,
$|\alpha - P/Q| < |\Delta|^{1/(q-1)} |C\alpha^q + D|^{2/(q-1)}$ and
$|b_{n+1}| > |\Delta|^{1/(q-1)}$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 8 (quoting Lasjaunias) (`integers-2026-A57-lem-8`). -/
public theorem_wanted lasjaunias_unbounded_criterion [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1))
    (hF : (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
      Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order)
    (h₁ : -((Fintype.card K : ℤ) - 1) * (α - polyToLaurentInv P / polyToLaurentInv Q).order <
      ((A * D - B * C).natDegree : ℤ) -
        2 * (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D).order)
    (h₂ : ((A * D - B * C).natDegree : ℤ) <
      -((Fintype.card K : ℤ) - 1) * (laurentPartialQuotient α (n + 1)).order) :
    ¬ LaurentHasBoundedPartialQuotients α

/-- **Bounded partial quotients for a cubic of Ayadi et al.** Let $\ell \ge 2$ and let
$A \in \mathbb{F}_2[x]$ be a polynomial of degree $2\ell$ whose constant and linear coefficients
are both $1$, that is, $A = x^{2\ell} + \sum_{i=2}^{2\ell-1} e_i x^i + x + 1$ with
$e_i \in \mathbb{F}_2$. If $\alpha \in \mathbb{F}_2((x^{-1}))$ has positive degree in $x$ (the
largest exponent of $x$ occurring in $\alpha$ is positive) and satisfies
$x^\ell \alpha^3 + A \alpha^2 + 1 = 0$, then $\alpha$ has bounded partial quotients.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Corollary 1 (`integers-2026-A57-cor-1`). -/
public theorem_wanted ayadi_cubic_boundedPartialQuotients (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (A : Polynomial (ZMod 2)) (hA : A.natDegree = 2 * ℓ) (hA₁ : A.coeff 1 = 1)
    (hA₀ : A.coeff 0 = 1) (α : LaurentSeries (ZMod 2)) (hdeg : α.order < 0)
    (hroot : laurentInvVar (ZMod 2) ^ ℓ * α ^ 3 + polyToLaurentInv A * α ^ 2 + 1 = 0) :
    LaurentHasBoundedPartialQuotients α

/-- **Baum–Sweet cubic: partial quotients of degree at most 2.** If
$\alpha \in \mathbb{F}_2((x^{-1}))$ satisfies $x\alpha^3 + \alpha + x = 0$, then every partial
quotient $b_n$ of $\alpha$, $n \ge 0$, has degree at most $2$ in $x$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Corollary 2 (`integers-2026-A57-cor-2`). -/
public theorem_wanted baumSweet_x_cubic_partialQuotient_degree_le_two
    (α : LaurentSeries (ZMod 2))
    (hroot : laurentInvVar (ZMod 2) * α ^ 3 + α + laurentInvVar (ZMod 2) = 0) :
    ∀ n : ℕ, ∀ m : ℤ, m < -2 → (laurentPartialQuotient α n).coeff m = 0

/-- **Small roots of a hyperquadratic equation have unbounded partial quotients.** Let
$\mathbb{F}_q$ be a finite field, let $\ell \ge 1$ and let $D \in \mathbb{F}_q[x]$ with
$D(0) \ne 0$. Write $|y| = |x|^{\deg y}$ for the absolute value on $\mathbb{F}_q((x^{-1}))$, where
$\deg y$ is the largest exponent of $x$ occurring in $y \ne 0$. If
$\alpha \in \mathbb{F}_q((x^{-1}))$ is irrational, satisfies $x\alpha^{q+1} + D\alpha + x^\ell = 0$
and $|\alpha| < |x|^{-((q-1)\ell + 1)}$, then $\alpha$ does not have bounded partial quotients.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Theorem 6 (`integers-2026-A57-thm-6`). -/
public theorem_wanted lasjaunias_unboundedPartialQuotients_of_small [Fintype K] (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (D : Polynomial K) (hD : D.coeff 0 ≠ 0) (α : LaurentSeries K)
    (hα : LaurentIsIrrational α)
    (hroot : laurentInvVar K * α ^ (Fintype.card K + 1) + polyToLaurentInv D * α +
      laurentInvVar K ^ ℓ = 0)
    (hsmall : ((Fintype.card K : ℤ) - 1) * ℓ + 1 < α.order) :
    ¬ LaurentHasBoundedPartialQuotients α

end LaurentContinuedFraction

end

end MetaMathlibExt
