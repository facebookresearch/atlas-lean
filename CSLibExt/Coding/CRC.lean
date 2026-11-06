/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

/-!
# Cyclic redundancy checks

A **CRC** with generator polynomial `g` of degree `r` over a field `F` (in practice `F₂`) encodes
a message polynomial `m` as `c = m·X^r - (m·X^r mod g)`, which over `F₂` is
`m·X^r + (m·X^r mod g)`: the message shifted up by `r` positions, followed by an `r`-symbol
check. Every codeword is a multiple of `g` (`dvd_encode`), and the message is read back from
coefficients `r, r + 1, …` (`coeff_encode_add`). The receiver accepts a word iff `g` divides it,
so an error pattern `e` added to a codeword goes undetected iff `g ∣ e` (`dvd_encode_add_iff`).

* `not_dvd_C_mul_X_pow`: if `g` has at least two terms, **every single-symbol error** `a·X^i`
  (`a ≠ 0`) is detected.
* `not_dvd_of_isBurstLE`: if `X ∤ g`, **every burst of length at most `deg g`** is detected. A
  burst of length at most `L` starting at position `i` is an error `X^i·b` with `b(0) ≠ 0` and
  `deg b < L` (`IsBurstLE`): its nonzero symbols lie in positions `i, …, i + L - 1`, the first one
  nonzero. Every nonzero error confined to `L` consecutive positions is one
  (`isBurstLE_of_support`).
* `detects`: both guarantees together, for a generator with at least two terms and `X ∤ g`.

The bursts here are linear (non-wrap-around) bursts: a CRC has no fixed block length, and
shortened cyclic codes lose the end-around guarantee that cyclic codes of full length enjoy. Both
hypotheses are needed: the tests exhibit an undetected single-bit error for `g = X^3` and for
`g = 1` (which has `X ∤ g` but one term), and an undetected burst of length 2 for `g = X^2 + X`
(two terms, but `X ∣ g`). The bound `deg g` is sharp: `g` itself is an undetected burst of length
`deg g + 1`. The encoder here is the polynomial-level specification (Mathlib's polynomials are
noncomputable); a bit-level shift-register implementation proved equal to it is future work.

## References

* W. W. Peterson, D. T. Brown, "Cyclic codes for error detection", *Proceedings of the IRE* 49
  (1961), 228-235.
* S. Lin, D. J. Costello, *Error Control Coding*, 2nd ed., Pearson, 2004, Ch. 5.
-/

namespace Cslib.CodingTheory.CRC

open Polynomial

variable {F : Type*} [Field F]

/-- **CRC encoder.** Let $F$ be a field, let $g$ be a polynomial over $F$ (the generator), and let
$r$ be the degree of $g$ (with $r = 0$ when $g = 0$). The CRC encoding of a polynomial $m$ over
$F$ (the message) is $m X^r - (m X^r \bmod g)$: the message shifted up by $r$ positions, minus the
remainder of the shifted message modulo $g$. -/
noncomputable def encode (g m : F[X]) : F[X] := m * X ^ g.natDegree - m * X ^ g.natDegree % g

/-- **CRC encoding in characteristic 2.** Let $F$ be a field of characteristic 2 (for example
$\mathbb{F}_2$), let $g$ and $m$ be polynomials over $F$, and let $r$ be the degree of $g$ (with
$r = 0$ when $g = 0$). Then the CRC encoding of $m$ with generator $g$ equals
$m X^r + (m X^r \bmod g)$: the encoder appends the remainder to the shifted message. -/
theorem encode_eq_add [CharP F 2] (g m : F[X]) :
    encode g m = m * X ^ g.natDegree + m * X ^ g.natDegree % g := by
  rw [encode, CharTwo.sub_eq_add]

/-- **CRC codewords are multiples of the generator.** Let $F$ be a field. For all polynomials $g$
and $m$ over $F$, the polynomial $g$ divides the CRC encoding of $m$ with generator $g$. -/
theorem dvd_encode (g m : F[X]) : g ∣ encode g m := by
  rw [encode, EuclideanDomain.mod_eq_sub_mul_div, sub_sub_cancel]
  exact dvd_mul_right g _

/-- **CRC encoding is systematic.** Let $F$ be a field and $g \ne 0$ a polynomial over $F$ of
degree $r$. For every message polynomial $m$ over $F$ and every natural number $i$, the
coefficient of $X^{i+r}$ in the CRC encoding of $m$ with generator $g$ equals the coefficient of
$X^i$ in $m$. -/
theorem coeff_encode_add {g : F[X]} (hg : g ≠ 0) (m : F[X]) (i : ℕ) :
    (encode g m).coeff (i + g.natDegree) = m.coeff i := by
  have hrem : (m * X ^ g.natDegree % g).coeff (i + g.natDegree) = 0 := by
    apply coeff_eq_zero_of_degree_lt
    calc (m * X ^ g.natDegree % g).degree < g.degree := degree_mod_lt _ hg
      _ = g.natDegree := degree_eq_natDegree hg
      _ ≤ (i + g.natDegree : ℕ) := by exact_mod_cast Nat.le_add_left _ _
  rw [encode, coeff_sub, hrem, sub_zero, coeff_mul_X_pow]

/-- **CRC detection criterion.** Let $F$ be a field, let $g$, $m$ and $e$ be polynomials over
$F$, and let $c$ be the CRC encoding of $m$ with generator $g$. Then $g$ divides $c + e$ if and
only if $g$ divides $e$: a codeword plus an error pattern passes the check exactly when $g$
divides the error. -/
theorem dvd_encode_add_iff (g m e : F[X]) : g ∣ encode g m + e ↔ g ∣ e :=
  dvd_add_right (dvd_encode g m)

/-- **Single-symbol errors are detected.** Let $F$ be a field and $g$ a polynomial over $F$ with
at least two nonzero coefficients. Then $g$ does not divide $a X^i$ for any nonzero $a \in F$ and
any natural number $i$.

The divisors of $X^i$ are the monomials $c X^j$ with $c \in F$ nonzero and $j \le i$, each of
which has only one nonzero coefficient. -/
theorem not_dvd_C_mul_X_pow {g : F[X]} (hg : 2 ≤ g.support.card) {a : F} (ha : a ≠ 0) (i : ℕ) :
    ¬g ∣ C a * X ^ i := by
  intro h
  have hX : g ∣ X ^ i := ((isUnit_C.mpr ha.isUnit).dvd_mul_left).mp h
  obtain ⟨j, -, hassoc⟩ := (dvd_prime_pow prime_X i).mp hX
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rw [← hcu, mul_comm] at hu
  rw [← hu, support_C_mul_X_pow j hc.ne_zero, Finset.card_singleton] at hg
  omega

/-- **Burst errors.** Let $F$ be a field and $L$ a natural number. A polynomial $e$ over $F$ is a
burst of length at most $L$ when $e = X^i b$ for some natural number $i$ and some polynomial $b$
over $F$ with $b(0) \ne 0$ and $\deg b < L$. Then the nonzero coefficients of $e$ lie in
positions $i, \dots, i + L - 1$, the first one nonzero. -/
def IsBurstLE (e : F[X]) (L : ℕ) : Prop :=
  ∃ i : ℕ, ∃ b : F[X], e = X ^ i * b ∧ b.coeff 0 ≠ 0 ∧ b.natDegree < L

/-- **Errors confined to a window are bursts.** Let $F$ be a field, let $e \ne 0$ be a polynomial
over $F$, and let $i$ and $L$ be natural numbers. If every $j$ for which the coefficient of $X^j$
in $e$ is nonzero satisfies $i \le j < i + L$, then $e$ is a burst of length at most $L$. -/
theorem isBurstLE_of_support {e : F[X]} (he : e ≠ 0) {i L : ℕ}
    (h : ∀ j ∈ e.support, i ≤ j ∧ j < i + L) : IsBurstLE e L := by
  set t := e.natTrailingDegree
  obtain ⟨b, hb⟩ : X ^ t ∣ e := by
    rw [X_pow_dvd_iff]
    exact fun d hd ↦ coeff_eq_zero_of_lt_natTrailingDegree hd
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact he hb
  refine ⟨t, b, hb, ?_, ?_⟩
  · have hcoeff : e.coeff t = b.coeff 0 := by
      have := coeff_X_pow_mul b t 0
      rw [zero_add] at this
      rw [hb, this]
    rw [← hcoeff]
    exact mt trailingCoeff_eq_zero.mp he
  · have hdeg : e.natDegree = t + b.natDegree := by
      rw [hb, natDegree_mul (pow_ne_zero _ X_ne_zero) hb0, natDegree_X_pow]
    have h1 := h _ (natDegree_mem_support_of_nonzero he)
    have h2 := h _ (natTrailingDegree_mem_support_of_nonzero he)
    omega

/-- **Short bursts are detected.** Let $F$ be a field, let $g$ be a polynomial over $F$ that is
not divisible by $X$, and let $L$ be a natural number with $L \le \deg g$. If a polynomial $e$
over $F$ is a burst of length at most $L$, then $g$ does not divide $e$.

Write $e = X^i b$ with $b(0) \ne 0$ and $\deg b < L$. Since $X \nmid g$, $g$ is coprime to
$X^i$, so $g \mid X^i b$ would force $g \mid b$, impossible for a nonzero $b$ of smaller degree. -/
theorem not_dvd_of_isBurstLE {g e : F[X]} (hX : ¬X ∣ g) {L : ℕ} (he : IsBurstLE e L)
    (hL : L ≤ g.natDegree) : ¬g ∣ e := by
  obtain ⟨i, b, rfl, hb0, hbL⟩ := he
  intro h
  have hcop : IsCoprime g (X ^ i) :=
    (((irreducible_X : Irreducible (X : F[X])).coprime_iff_not_dvd).mpr hX).symm.pow_right
  have hgb : g ∣ b := hcop.dvd_of_dvd_mul_left h
  have hb : b ≠ 0 := fun h0 ↦ hb0 (by rw [h0, coeff_zero])
  have := natDegree_le_of_dvd hgb hb
  omega

/-- **CRC error-detection guarantee.** Let $F$ be a field, let $g$ be a polynomial over $F$ with
at least two nonzero coefficients that is not divisible by $X$, let $m$ be a polynomial over $F$,
and let $c$ be the CRC encoding of $m$ with generator $g$. Then $g$ does not divide $c + aX^i$ for
any nonzero $a \in F$ and any natural number $i$, and $g$ does not divide $c + e$ for any
polynomial $e$ over $F$ that is a burst of length at most $\deg g$. That is, the check detects
every single-symbol error and every burst of length at most $\deg g$ in every codeword.

Given $X \nmid g$, having at least two terms is the same as $\deg g \ge 1$, and a single-symbol
error is a burst of length 1. -/
theorem detects {g : F[X]} (hg : 2 ≤ g.support.card) (hX : ¬X ∣ g) (m : F[X]) :
    (∀ a : F, a ≠ 0 → ∀ i, ¬g ∣ encode g m + C a * X ^ i) ∧
      ∀ e, IsBurstLE e g.natDegree → ¬g ∣ encode g m + e :=
  ⟨fun a ha i ↦ by rw [dvd_encode_add_iff]; exact not_dvd_C_mul_X_pow hg ha i,
    fun e he ↦ by rw [dvd_encode_add_iff]; exact not_dvd_of_isBurstLE hX he le_rfl⟩

end Cslib.CodingTheory.CRC
