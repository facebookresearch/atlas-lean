/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Continued fractions of formal Laurent series

This module defines partial quotients and convergents in the inverse variable and proves the
two difference identities for a Möbius–Frobenius fixed point.
-/

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
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1.
-/
def laurentInvVar (K : Type*) [Field K] : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) (1 : K)

/-- **The variable $x$ times $x^{-1}$ is one.** Let $K$ be a field. In $K((x^{-1}))$, the
product of the variable $x$ and the series $x^{-1}$ (coefficient $1$ at $x^{-1}$ and $0$
elsewhere) is $1$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1.
-/
theorem laurentInvVar_mul_single_one :
    laurentInvVar K * HahnSeries.single (1 : ℤ) (1 : K) = 1 := by
  simp [laurentInvVar, HahnSeries.single_mul_single]

/-- **Polynomials as Laurent series in the inverse variable.** Let $K$ be a field. The embedding
$K[x] \to K((x^{-1}))$ is the $K$-algebra homomorphism that sends $x$ to the element $x$ of
$K((x^{-1}))$, that is, it evaluates a polynomial at $x$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1.
-/
def polyToLaurentInv (p : Polynomial K) : LaurentSeries K :=
  Polynomial.aeval (laurentInvVar K) p

/-- **The polynomial variable embeds as the Laurent variable.** Let $K$ be a field. The
embedding $K[x] \to K((x^{-1}))$ sends the polynomial $x$ to the element $x$ of
$K((x^{-1}))$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1.
-/
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

/-- **The denominator at a Möbius–Frobenius fixed point is nonzero.** Let $K$ be a finite field
with $q$ elements, let $A, B, C, D \in K[x]$, and let $\alpha \in K((x^{-1}))$ be irrational with
$\alpha = (A \alpha^q + B) / (C \alpha^q + D)$, where division by $0$ gives $0$. Then
$C \alpha^q + D \ne 0$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 6 (`integers-2026-A57-lem-6`). -/
public theorem laurentMobius_den_ne_zero [Fintype K] (A B C D : Polynomial K)
    (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D)) :
    polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D ≠ 0 := by
  intro h
  have hzero : α = 0 := by simpa [h] using hfix
  exact hα 0 1 one_ne_zero (by simp [hzero, polyToLaurentInv])

/-- **The inverse denominator at a Möbius–Frobenius fixed point is nonzero.** Let $K$ be a finite
field with $q$ elements, let $A, B, C, D \in K[x]$ with $\Delta = AD - BC \ne 0$, and let
$\alpha \in K((x^{-1}))$ be irrational with $\alpha = (A \alpha^q + B) / (C \alpha^q + D)$. Then
$A - C \alpha \ne 0$, since $(A - C \alpha)(C \alpha^q + D) = \Delta$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 6 (`integers-2026-A57-lem-6`). -/
public theorem laurentMobius_invDen_ne_zero [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D)) :
    polyToLaurentInv A - polyToLaurentInv C * α ≠ 0 := by
  have hden := laurentMobius_den_ne_zero A B C D α hα hfix
  let e : Polynomial K →ₐ[K] LaurentSeries K := Polynomial.aeval (laurentInvVar K)
  let q := Fintype.card K
  change α = (e A * α ^ q + e B) / (e C * α ^ q + e D) at hfix
  change e C * α ^ q + e D ≠ 0 at hden
  change e A - e C * α ≠ 0
  -- If a nonzero polynomial evaluated to zero, it would witness the rational relation Tα = 0.
  have hnonzero (T : Polynomial K) (hT : T ≠ 0) : e T ≠ 0 := by
    intro h
    apply hα 0 T hT
    change e T * α = e 0
    rw [h, zero_mul, map_zero]
  have hcross := (eq_div_iff hden).mp hfix
  -- The forward and inverse Möbius denominators multiply to the determinant.
  have hdet : (e A - e C * α) * (e C * α ^ q + e D) = e (A * D - B * C) := by
    simp only [map_sub, map_mul]
    linear_combination -e C * hcross
  exact (mul_ne_zero_iff.mp (hdet.trans_ne (hnonzero _ hΔ))).1

/-- **First difference identity for a Möbius–Frobenius fixed point.** Let $K$ be a finite field
with $q$ elements, let $A, B, C, D \in K[x]$ with $\Delta = AD - BC \ne 0$, and let
$\alpha \in K((x^{-1}))$ be irrational with $\alpha = (A \alpha^q + B) / (C \alpha^q + D)$. Let
$P, Q \in K[x]$, put $R_1 = DP - BQ$ and $S_1 = -CP + AQ$, and assume $S_1 \ne 0$. Then
$\alpha^q - R_1 / S_1 = \Delta (Q \alpha - P) / ((A - C \alpha) S_1)$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 6 (`integers-2026-A57-lem-6`). -/
public theorem laurentMobius_pow_sub_identity [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K) (hS₁ : -C * P + A * Q ≠ 0) :
    α ^ Fintype.card K - polyToLaurentInv (D * P - B * Q) / polyToLaurentInv (-C * P + A * Q) =
        polyToLaurentInv (A * D - B * C) * (polyToLaurentInv Q * α - polyToLaurentInv P) /
          ((polyToLaurentInv A - polyToLaurentInv C * α) * polyToLaurentInv (-C * P + A * Q)) := by
  have hden := laurentMobius_den_ne_zero A B C D α hα hfix
  have hinvDen := laurentMobius_invDen_ne_zero A B C D hΔ α hα hfix
  let e : Polynomial K →ₐ[K] LaurentSeries K := Polynomial.aeval (laurentInvVar K)
  let q := Fintype.card K
  change α = (e A * α ^ q + e B) / (e C * α ^ q + e D) at hfix
  change e C * α ^ q + e D ≠ 0 at hden
  change e A - e C * α ≠ 0 at hinvDen
  have hnonzero (T : Polynomial K) (hT : T ≠ 0) : e T ≠ 0 := by
    intro h
    apply hα 0 T hT
    change e T * α = e 0
    rw [h, zero_mul, map_zero]
  have hcross := (eq_div_iff hden).mp hfix
  have hinv : α ^ q = (e D * α - e B) / (e A - e C * α) := by
    apply (eq_div_iff hinvDen).mpr
    linear_combination -hcross
  change α ^ q - e _ / e _ = e _ * (e Q * α - e P) / ((e A - e C * α) * e _)
  rw [hinv, div_sub_div _ _ hinvDen (hnonzero _ hS₁)]
  congr 1
  simp only [map_add, map_sub, map_neg, map_mul]
  ring

/-- **Second difference identity for a Möbius–Frobenius fixed point.** Let $K$ be a finite field
with $q$ elements, let $A, B, C, D \in K[x]$, and let $\alpha \in K((x^{-1}))$ be irrational with
$\alpha = (A \alpha^q + B) / (C \alpha^q + D)$. Let $P, Q \in K[x]$, put $R_2 = AP^q + BQ^q$ and
$S_2 = CP^q + DQ^q$, and assume $S_2 \ne 0$. Then
$\alpha - R_2 / S_2 = (AD - BC) (Q \alpha - P)^q / ((C \alpha^q + D) S_2)$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 6 (`integers-2026-A57-lem-6`). -/
public theorem laurentMobius_sub_identity [Fintype K] (A B C D : Polynomial K)
    (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K) (hS₂ : C * P ^ Fintype.card K + D * Q ^ Fintype.card K ≠ 0) :
    α - polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K) /
          polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) =
        polyToLaurentInv (A * D - B * C) *
            (polyToLaurentInv Q * α - polyToLaurentInv P) ^ Fintype.card K /
          ((polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D) *
            polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K)) := by
  have hden := laurentMobius_den_ne_zero A B C D α hα hfix
  let e : Polynomial K →ₐ[K] LaurentSeries K := Polynomial.aeval (laurentInvVar K)
  let q := Fintype.card K
  change α = (e A * α ^ q + e B) / (e C * α ^ q + e D) at hfix
  change e C * α ^ q + e D ≠ 0 at hden
  have hnonzero (T : Polynomial K) (hT : T ≠ 0) : e T ≠ 0 := by
    intro h
    apply hα 0 T hT
    change e T * α = e 0
    rw [h, zero_mul, map_zero]
  have hpow (u v : LaurentSeries K) : (u - v) ^ q = u ^ q - v ^ q :=
    map_sub (FiniteField.frobeniusAlgHom K (LaurentSeries K)) u v
  change α - e _ / e _ = e _ * (e Q * α - e P) ^ q / ((e C * α ^ q + e D) * e _)
  nth_rw 1 [hfix]
  rw [div_sub_div _ _ hden (hnonzero _ hS₂), hpow, mul_pow]
  congr 1
  simp only [map_add, map_sub, map_mul, map_pow]
  ring

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
public theorem laurentMobius_sub_identities [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K) (_hQ : Q ≠ 0) (hS₁ : -C * P + A * Q ≠ 0)
    (hS₂ : C * P ^ Fintype.card K + D * Q ^ Fintype.card K ≠ 0) :
    α ^ Fintype.card K - polyToLaurentInv (D * P - B * Q) / polyToLaurentInv (-C * P + A * Q) =
        polyToLaurentInv (A * D - B * C) * (polyToLaurentInv Q * α - polyToLaurentInv P) /
          ((polyToLaurentInv A - polyToLaurentInv C * α) * polyToLaurentInv (-C * P + A * Q)) ∧
      α - polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K) /
          polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) =
        polyToLaurentInv (A * D - B * C) *
            (polyToLaurentInv Q * α - polyToLaurentInv P) ^ Fintype.card K /
          ((polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D) *
            polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K)) :=
  ⟨laurentMobius_pow_sub_identity A B C D hΔ α hα hfix P Q hS₁,
    laurentMobius_sub_identity A B C D α hα hfix P Q hS₂⟩

end LaurentContinuedFraction

end

end MetaMathlibExt
