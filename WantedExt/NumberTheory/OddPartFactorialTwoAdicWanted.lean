/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib

namespace MetaMathlibExt

@[expose] public section

/-!
This file formalizes, without proving the paper's main results, the statements in
Donald M. Davis's paper on the odd part of `(2^e)!`.  Congruences in `ℤ` and `ℕ`
are represented by divisibility of an integer difference, while congruences in
`ℤ_[2]` are represented uniformly by divisibility by a power of `2`.
-/

/--
**Odd part.** For a natural number $n \ge 1$, the odd part $\operatorname{od}(n)$ is
$n / 2^{\nu_2(n)}$, where $2^{\nu_2(n)}$ is the largest power of $2$ dividing $n$; it is the odd
factor of $n$ left after removing that power of $2$. For $n = 0$ the definition gives
$\operatorname{od}(0) = 0$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of od.
-/
public def oddPart (n : ℕ) : ℕ :=
  ordCompl[2] n

/--
**Odd part as a quotient by a power of two.** For every natural number $n$,
$\mathrm{od}(n) = n / 2^{\nu_2(n)}$, where $\mathrm{od}(n)$ is the odd part of $n$ and
$\nu_2(n)$ is the exponent of $2$ in the prime factorization of $n$, with $\nu_2(0) = 0$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of od.
-/
public theorem oddPart_eq (n : ℕ) :
    oddPart n = n / 2 ^ n.factorization 2 := by
  rfl

/--
**Odd-range product.** For natural numbers $l$ and $m$, the odd-range product
$\operatorname{odpr}(l, m)$ is the product of the odd natural numbers $j$ with $l \le j \le m$;
it equals $1$ when there are none.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of odpr.
-/
public def oddRangeProduct (l m : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Icc l m).filter Odd, j

/--
**Odd-range product as a filtered product.** For all natural numbers $l$ and $m$, the odd-range
product $\operatorname{odpr}(l, m)$ equals the product $\prod j$ over the odd natural numbers $j$ in
the closed interval $[l, m]$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of odpr.
-/
public theorem oddRangeProduct_eq (l m : ℕ) :
    oddRangeProduct l m = ∏ j ∈ (Finset.Icc l m).filter Odd, j := by
  rfl

/--
**Odd product block.** For a natural number $m$, the odd product block $h(m)$ is the product of
the odd integers $j$ with $2^{m-1}+1 \le j \le 2^m-1$. In particular $h(0) = h(1) = 1$, as empty
products.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of h.
-/
public def oddProductBlock (m : ℕ) : ℕ :=
  oddRangeProduct (2 ^ (m - 1) + 1) (2 ^ m - 1)

/--
**Odd product block as an odd-range product.** For every natural number $m$, the odd product block
$h(m)$ equals $\operatorname{odpr}(2^{m-1}+1, 2^m-1)$, the product of the odd integers $j$ with
$2^{m-1}+1 \le j \le 2^m-1$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of h.
-/
public theorem oddProductBlock_eq (m : ℕ) :
    oddProductBlock m = oddRangeProduct (2 ^ (m - 1) + 1) (2 ^ m - 1) := by
  rfl

/--
**Unstable bits.** Write $\operatorname{od}(n)$ for the odd part of a natural number $n$. For
natural numbers $e$ and $d$, the unstable bits $\operatorname{uns}(e,d)$ are the natural number
$\lfloor \operatorname{od}((2^e)!) / 2^{e+1} \rfloor \bmod 2^d$, whose binary digits are the $d$
bits of $\operatorname{od}((2^e)!)$ at positions $e+1, \dots, e+d$ (position $0$ being the least
significant bit).

The paper assumes $e > d$ only when stating Theorem 1, so the definition itself is total.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of uns.
-/
public def unstableBits (e d : ℕ) : ℕ :=
  oddPart (Nat.factorial (2 ^ e)) / 2 ^ (e + 1) % 2 ^ d

/--
**Formula for the unstable bits.** Write $\operatorname{od}(n)$ for the odd part of a natural
number $n$. For all natural numbers $e$ and $d$, the unstable bits are
$\operatorname{uns}(e,d) = \lfloor \operatorname{od}((2^e)!) / 2^{e+1} \rfloor \bmod 2^d$.

The binary digits of this number, least significant first, are the paper's first $d$ unstable
bits of $\operatorname{od}((2^e)!)$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of uns.
-/
public theorem unstableBits_eq (e d : ℕ) :
    unstableBits e d = oddPart (Nat.factorial (2 ^ e)) / 2 ^ (e + 1) % 2 ^ d := by
  rfl

/--
**Stable bits of the odd part of a factorial.** For natural numbers $s$ and $d$, let
$\operatorname{stab}(s, d)$ be the number whose binary digits are the digits of
$\operatorname{od}((2^{s+d-1})!)$ in positions $s, \dots, s + d - 1$ (position $0$ being the
units digit), where $\operatorname{od}(m)$ is the odd part of $m$ and $s + d - 1$ is truncated
subtraction. That is,
$$\operatorname{stab}(s, d) = \lfloor \operatorname{od}((2^{s+d-1})!) / 2^s \rfloor \bmod 2^d.$$

For $s = e + 1$ this is the source's $\operatorname{stab}(e + 1, d)$, the digits in positions
$e + 1, \dots, e + d$ of $\operatorname{od}((2^{e+d})!)$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of stab.
-/
public def stableBits (s d : ℕ) : ℕ :=
  oddPart (Nat.factorial (2 ^ (s + d - 1))) / 2 ^ s % 2 ^ d

/--
**Formula for the stable bits.** Write $\operatorname{od}(n)$ for the odd part of a natural
number $n$. For all natural numbers $s$ and $d$, the stable bits are
$\operatorname{stab}(s, d) = \lfloor \operatorname{od}((2^{s+d-1})!) / 2^s \rfloor \bmod 2^d$,
where $s + d - 1$ is read as $0$ when $s = d = 0$.

For $s = e + 1$ the factorial is that of $2^{e+d}$, the shift is by $e + 1$ binary digits and the
modulus is $2^d$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of stab.
-/
public theorem stableBits_eq (s d : ℕ) :
    stableBits s d = oddPart (Nat.factorial (2 ^ (s + d - 1))) / 2 ^ s % 2 ^ d := by
  rfl

/--
**The unstable bits for $e = 4$ and $d = 2$.** The unstable bits $\operatorname{uns}(4,2)$ equal
$3$; that is, $\lfloor \operatorname{od}(16!) / 2^5 \rfloor \bmod 2^2 = 3$, where
$\operatorname{od}(16!)$ is the odd part of $16!$.

This small case stands in for the paper's worked example $\operatorname{uns}(17,7) = 74$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Worked example after Theorem 1.
-/
public theorem unstableBits_four_two : unstableBits 4 2 = 3 := by
  change Nat.factorial 16 / 2 ^ (Nat.factorial 16).factorization 2 / 32 % 4 = 3
  rw [Nat.factorization_factorial (p := 2) (n := 16) (b := 5)
    (by norm_num) (by norm_num [Nat.log])]
  norm_num [Finset.sum_Ico_succ_top]

/--
**The stable bits $\operatorname{stab}(5, 2)$ vanish.** Writing $\operatorname{od}(m)$ for the odd
part of $m$, the binary digits of $\operatorname{od}(64!)$ in positions $5$ and $6$ (the units
digit being position $0$) are both $0$; that is,
$\operatorname{stab}(5, 2) = \lfloor \operatorname{od}(64!) / 2^5 \rfloor \bmod 4 = 0$.

This small instance checks the same factorial, shift and remainder convention as the source's
larger worked example $\operatorname{stab}(18, 7) = 55$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Worked example after Theorem 1.
-/
public theorem stableBits_five_two : stableBits 5 2 = 0 := by
  change Nat.factorial 64 / 2 ^ (Nat.factorial 64).factorization 2 / 32 % 4 = 0
  rw [Nat.factorization_factorial (p := 2) (n := 64) (b := 7)
    (by norm_num) (by norm_num [Nat.log])]
  norm_num [Finset.sum_Ico_succ_top]

/--
**Dyadic upper half interval.** For a natural number $e$, $I_e$ is the finite set of natural
numbers $i$ with $2^{e-1} < i \le 2^e$, where $e - 1$ is truncated subtraction, so that $I_0$ is
empty.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of I_e.
-/
public def dyadicUpperHalf (e : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ (e - 1)) (2 ^ e)

/--
**Membership in the dyadic upper half.** For natural numbers $e$ and $i$, $i$ belongs to the
dyadic upper half $I_e$ if and only if $2^{e-1} < i$ and $i \le 2^e$, where $e - 1$ is truncated
subtraction.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of I_e.
-/
public theorem mem_dyadicUpperHalf (e i : ℕ) :
    i ∈ dyadicUpperHalf e ↔ 2 ^ (e - 1) < i ∧ i ≤ 2 ^ e := by
  simp [dyadicUpperHalf]

/--
**Odd numbers below a power of two.** For a natural number $e$, $S_e$ is the finite set of odd
natural numbers $i$ with $1 \le i < 2^e$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of S_e.
-/
public def oddBelowTwoPow (e : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (2 ^ e)).filter Odd

/--
**Membership in the odd numbers below $2^e$.** For natural numbers $e$ and $i$, $i$ belongs to the
set $S_e$ of odd positive integers below $2^e$ if and only if $1 \le i$, $i < 2^e$ and $i$ is odd.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of S_e.
-/
public theorem mem_oddSet (e i : ℕ) :
    i ∈ oddBelowTwoPow e ↔ 1 ≤ i ∧ i < 2 ^ e ∧ Odd i := by
  simp [oddBelowTwoPow, and_assoc]

/--
**Integer multiset of a finite set of naturals.** For a finite set $s$ of natural numbers, its
integer multiset is the multiset of integers obtained by sending each element $n \in s$ to $n$
viewed as an integer, so each element of $s$ occurs exactly once.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Convention for finite multisets.
-/
public def integerMultiset (s : Finset ℕ) : Multiset ℤ :=
  s.val.map fun n : ℕ => (n : ℤ)

/--
**Cardinality of the integer multiset.** For every finite set $s$ of natural numbers, the integer
multiset of $s$ has the same number of elements, counted with multiplicity, as $s$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Convention for finite multisets.
-/
public theorem integerMultiset_card (s : Finset ℕ) :
    (integerMultiset s).card = s.card := by
  simp [integerMultiset]

/--
**Reversed elementary symmetric functions.** Let $R$ be a commutative semiring, let $S$ be a
finite multiset of elements of $R$ with $n$ elements counted with multiplicity, and let $i$ be a
natural number. The reversed elementary symmetric function $\hat\sigma_i(S)$ is
$\sigma_{n-i}(S)$, the elementary symmetric function of degree $n - i$ in the elements of $S$.
Here $n - i$ is truncated subtraction, so $\hat\sigma_i(S) = \sigma_0(S) = 1$ whenever $i \ge n$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of σ̂_i.
-/
public def reverseESymm {R : Type*} [CommSemiring R] (i : ℕ) (s : Multiset R) : R :=
  Multiset.esymm s (s.card - i)

/--
**Unfolding the reversed elementary symmetric function.** For every commutative semiring $R$,
natural number $i$ and finite multiset $S$ of elements of $R$ with $n$ elements counted with
multiplicity, the reversed elementary symmetric function satisfies
$\hat\sigma_i(S) = \sigma_{n-i}(S)$, the elementary symmetric function of $S$ of degree $n - i$,
where $n - i$ is truncated subtraction.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of σ̂_i.
-/
public theorem reverseESymm_eq {R : Type*} [CommSemiring R] (i : ℕ) (s : Multiset R) :
    reverseESymm i s = Multiset.esymm s (s.card - i) := by
  rfl

/--
**Odd double factorial below a power of two.** For a natural number $e$, $(2^e-1)!!$ is the
product of the odd natural numbers in the closed interval $[1, 2^e-1]$. The parameter is the
exponent $e$, not the odd endpoint $2^e-1$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of (2^e-1)!!.
-/
public def oddDoubleFactorial (e : ℕ) : ℕ :=
  oddRangeProduct 1 (2 ^ e - 1)

/--
**Odd double factorial below a power of two as an odd-range product.** For every natural number
$e$, $(2^e-1)!!$ equals the product of the odd natural numbers in the closed interval
$[1, 2^e-1]$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of (2^e-1)!!.
-/
public theorem oddDoubleFactorial_eq (e : ℕ) :
    oddDoubleFactorial e = oddRangeProduct 1 (2 ^ e - 1) := by
  rfl

/--
**Numbers below $2^e$ congruent to $1$ modulo $8$.** For a natural number $e$, this is the
finite set of natural numbers $n$ with $n < 2^e$ and $n \equiv 1 \pmod 8$.

For $e \ge 3$ its elements are $1, 9, \dots, 2^e - 7$, the sequence displayed in Lemma 21 of
the source.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21 notation.
-/
public def oneModEightBelowTwoPow (e : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ e)).filter fun n => n % 8 = 1

/--
**Membership in the residues one modulo eight below a power of two.** For all natural numbers $e$
and $n$, $n$ lies in the set of natural numbers below $2^e$ that are congruent to $1$ modulo $8$
if and only if $n < 2^e$ and $n \equiv 1 \pmod 8$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21 notation.
-/
public theorem mem_oneModEight (e n : ℕ) :
    n ∈ oneModEightBelowTwoPow e ↔ n < 2 ^ e ∧ n % 8 = 1 := by
  simp [oneModEightBelowTwoPow]

/--
**Four copies of the residues $1 \bmod 8$ below $2^e$.** For a natural number $e$, this is the
multiset of integers containing exactly four copies of each natural number $n < 2^e$ with
$n \equiv 1 \pmod 8$, that is, of each of $1, 9, \dots, 2^e - 7$ when $e \ge 3$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21.
-/
public def fourCopiesOneModEightBelowTwoPow (e : ℕ) : Multiset ℤ :=
  4 • integerMultiset (oneModEightBelowTwoPow e)

/--
**Four copies as a multiset scalar multiple.** For every natural number $e$, the multiset of four
copies of the residues $1 \bmod 8$ below $2^e$ equals $4 \cdot M$, the sum of four copies of $M$,
where $M$ is the integer multiset of the set of natural numbers $n < 2^e$ with $n \equiv 1 \pmod 8$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21.
-/
public theorem fourCopiesOneModEight_eq (e : ℕ) :
    fourCopiesOneModEightBelowTwoPow e = 4 • integerMultiset (oneModEightBelowTwoPow e) := by
  rfl

/--
**A 2-adic constant relating unstable and stable bits.** Write
$\mathrm{od}(n)$ for the odd part of a natural number $n$, and for natural numbers $d$ and $e$ let
$\mathrm{uns}(e, d) = \lfloor \mathrm{od}((2^e)!) / 2^{e+1} \rfloor \bmod 2^d$ and
$\mathrm{stab}(e + 1, d) = \lfloor \mathrm{od}((2^{e+d})!) / 2^{e+1} \rfloor \bmod 2^d$. There is a
2-adic integer $K$ such that for all natural numbers $d < e$, $2^d$ divides
$\mathrm{uns}(e, d) + K - \mathrm{stab}(e + 1, d)$ in $\mathbb{Z}_2$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Theorem 1.
-/
public theorem_wanted exists_twoAdic_unstable_add_eq_stable :
    ∃ K : ℤ_[2], ∀ d e : ℕ, d < e →
      (2 : ℤ_[2]) ^ d ∣ (unstableBits e d : ℤ_[2]) + K - (stableBits (e + 1) d : ℤ_[2])

/--
**Odd part of a dyadic factorial as a product of odd blocks.** For every natural number
$e \ge 1$,
$$\mathrm{od}((2^e)!) = \prod_{m=2}^{e} h(m)^{e+1-m},$$
where $\mathrm{od}(n)$ is the odd part of $n$ and $h(m)$ is the product of the odd numbers from
$2^{m-1}+1$ to $2^m-1$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Proposition 3.
-/
public theorem_wanted oddPart_factorial_eq_prod_h (e : ℕ) (he : 1 ≤ e) :
    oddPart (Nat.factorial (2 ^ e)) =
      ∏ m ∈ Finset.Icc 2 e, oddProductBlock m ^ (e + 1 - m)

/--
**Initial-segment congruence for the odd product block.** For natural numbers $l$ and $u$ write
$\operatorname{odpr}(l, u)$ for the product of the odd integers $j$ with $l \le j \le u$, and let
$h(m) = \operatorname{odpr}(2^{m-1}+1, 2^m-1)$. Let $m \ge 4$ and $B$ be natural numbers with
$m - 1 \le B \le 3m - 7$, and put $d = \lfloor (B + 4 - m)/2 \rfloor$, that is,
$d = 2 + \lfloor (B - m)/2 \rfloor$ (so $d = 1$ when $B = m - 1$). Then
$$
h(m) \equiv \operatorname{odpr}\bigl(2^{m-1}+1,\ 2^{m-1}+2^d-1\bigr)^{2^{m-1-d}} \pmod{2^B}.
$$

The paper prints the hypotheses $2 \le m - 1 \le B \le 3m - 7$, which also allow $(m, B) = (3, 2)$.
There $d = 1$, $h(3) = 35$ and the right-hand side is $5^2 = 25$, but $35 - 25 = 10$ is not
divisible by $4$. Requiring $m \ge 4$ removes exactly that case and keeps every other printed case.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Theorem 4.
-/
public theorem_wanted oddProductBlock_congr_initial_segment
    (m B : ℕ) (hm : 4 ≤ m) (hmB : m - 1 ≤ B) (hB : B ≤ 3 * m - 7) :
    let d := (B + 4 - m) / 2
    (2 : ℤ) ^ B ∣ (oddProductBlock m : ℤ) -
      (oddRangeProduct (2 ^ (m - 1) + 1) (2 ^ (m - 1) + 2 ^ d - 1) : ℤ) ^
        (2 ^ (m - 1 - d))

/--
**Odd parts biject the upper dyadic half onto the odd numbers below a power of two.**
For every natural number $e \ge 1$, the map sending each natural number to its odd part restricts
to a bijection from $I_e = \{i \in \mathbb{N} : 2^{e-1} < i \le 2^e\}$ onto the set $S_e$ of odd
natural numbers $i$ with $1 \le i < 2^e$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 5.
-/
public theorem_wanted oddPart_bijOn_upperHalf_oddSet (e : ℕ) (he : 1 ≤ e) :
    Set.BijOn oddPart (↑(dyadicUpperHalf e) : Set ℕ) (↑(oddBelowTwoPow e) : Set ℕ)

/--
**Product of the odd numbers below $2^e$.** For every natural number $e \ge 3$, the product of the
odd integers $i$ with $1 \le i < 2^e$ is congruent to $2^e + 1$ modulo $2^{e+1}$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 6.
-/
public theorem_wanted oddSet_product_congr (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ (e + 1) ∣
      ((∏ i ∈ oddBelowTwoPow e, i : ℕ) : ℤ) - ((2 ^ e + 1 : ℕ) : ℤ)

/--
**Odd parts of consecutive dyadic factorials agree modulo a power of two.** For every natural
number $e \ge 3$, $\mathrm{od}((2^{e-1})!) \equiv \mathrm{od}((2^e)!) \pmod{2^e}$, where
$\mathrm{od}(n)$ denotes the odd part of $n$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 7.
-/
public theorem_wanted oddPart_factorial_congr_previous (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ e ∣ (oddPart (Nat.factorial (2 ^ (e - 1))) : ℤ) -
      (oddPart (Nat.factorial (2 ^ e)) : ℤ)

/--
**A 2-adic limit of the odd parts of $(2^e)!$.** There is a 2-adic integer $z \in \mathbb{Z}_2$
such that $z \equiv \operatorname{od}((2^{e-1})!) \pmod{2^e}$ in $\mathbb{Z}_2$ for every natural
number $e \ge 1$, where $\operatorname{od}(n)$ is the odd part of $n$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 8.
-/
public theorem_wanted exists_twoAdic_oddPart_factorial_limit :
    ∃ z : ℤ_[2], ∀ e : ℕ, 1 ≤ e →
      (2 : ℤ_[2]) ^ e ∣ z - (oddPart (Nat.factorial (2 ^ (e - 1))) : ℤ_[2])

/--
**Shifting the odd numbers below $2^e$ by $2^e$.** For every natural number $e \ge 2$, let $S_e$ be
the set of odd integers $i$ with $1 \le i < 2^e$. Then
$$
\prod_{i \in S_e} i \equiv \prod_{i \in S_e} (2^e + i) \pmod{2^{2e}}.
$$

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Proposition 9.
-/
public theorem_wanted oddSet_product_congr_shift (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (2 * e) ∣
      ((∏ i ∈ oddBelowTwoPow e, i : ℕ) : ℤ) -
        (∏ i ∈ oddBelowTwoPow e, ((2 ^ e + i : ℕ) : ℤ))

/--
**Congruence of normalized odd double factorials.** For every natural number $e \ge 3$, writing
$(2^k-1)!!$ for the product of the odd numbers from $1$ to $2^k-1$, the integer $2^e$ divides
$(2^e-1)!! - 1$, the integer $2^{e+1}$ divides $(2^{e+1}-1)!! - 1$, and
$$\frac{(2^e-1)!! - 1}{2^e} \equiv \frac{(2^{e+1}-1)!! - 1}{2^{e+1}} \pmod{2^{e-1}}.$$

The source states this for $e \ge 2$, but at $e = 2$ the first quotient is not an integer:
$(2^2-1)!! - 1 = 2$ is not divisible by $4$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 10.
-/
public theorem_wanted oddDoubleFactorial_normalized_congr (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ e ∣ (oddDoubleFactorial e : ℤ) - 1 ∧
    (2 : ℤ) ^ (e + 1) ∣ (oddDoubleFactorial (e + 1) : ℤ) - 1 ∧
    (2 : ℤ) ^ (e - 1) ∣
      ((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e -
        ((oddDoubleFactorial (e + 1) : ℤ) - 1) / (2 : ℤ) ^ (e + 1)

/--
**A 2-adic limit of normalized odd double factorials.** Write $(2^e - 1)!!$ for the product of
the odd natural numbers from $1$ to $2^e - 1$. There is a 2-adic integer $w$ such that for every
natural number $e \ge 3$, $2^{e-1}$ divides $w - \lfloor ((2^e - 1)!! - 1) / 2^e \rfloor$ in
$\mathbb{Z}_2$.

For $e \ge 3$ the division is exact. The paper writes $e \ge 2$, but at $e = 2$ the quotient
$(3 - 1)/4$ is not an integer.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition after Corollary 10.
-/
public theorem_wanted exists_twoAdic_oddDoubleFactorial_limit :
    ∃ w : ℤ_[2], ∀ e : ℕ, 3 ≤ e →
      (2 : ℤ_[2]) ^ (e - 1) ∣ w -
        (↑(((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e) : ℤ_[2])

/--
**Normalized difference of odd parts of dyadic factorials.** Write $\mathrm{od}(n)$ for the odd
part of $n$, $(2^e-1)!!$ for the product of the odd numbers from $1$ to $2^e-1$, and
$\lfloor x \rfloor$ for the floor of $x$; congruences are taken in the $2$-adic integers
$\mathbb{Z}_2$. Let $z, w \in \mathbb{Z}_2$ satisfy $z \equiv \mathrm{od}((2^{e-1})!) \pmod{2^e}$
for every $e \ge 1$ and $w \equiv \lfloor ((2^e-1)!! - 1)/2^e \rfloor \pmod{2^{e-1}}$ for every
$e \ge 3$. Then for every $e \ge 3$,
$$\lfloor (\mathrm{od}((2^e)!) - \mathrm{od}((2^{e-1})!))/2^e \rfloor \equiv zw \pmod{2^{e-1}}.$$

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Theorem 12.
-/
public theorem_wanted oddPart_factorial_difference_congr_product
    (z w : ℤ_[2])
    (hz : ∀ e : ℕ, 1 ≤ e →
      (2 : ℤ_[2]) ^ e ∣ z - (oddPart (Nat.factorial (2 ^ (e - 1))) : ℤ_[2]))
    (hw : ∀ e : ℕ, 3 ≤ e →
      (2 : ℤ_[2]) ^ (e - 1) ∣ w -
        (↑(((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e) : ℤ_[2]))
    (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ_[2]) ^ (e - 1) ∣
      (↑(((oddPart (Nat.factorial (2 ^ e)) : ℤ) -
          (oddPart (Nat.factorial (2 ^ (e - 1))) : ℤ)) / (2 : ℤ) ^ e) : ℤ_[2]) - z * w

/--
**The unstable translation constant equals $-zw$.** Write $\operatorname{od}(n)$ for the odd part
of a natural number $n$, $(2^e-1)!!$ for the product of the odd numbers from $1$ to $2^e-1$,
$\operatorname{uns}(e,d) = \lfloor \operatorname{od}((2^e)!)/2^{e+1} \rfloor \bmod 2^d$ and
$\operatorname{stab}(e+1,d) = \lfloor \operatorname{od}((2^{e+d})!)/2^{e+1} \rfloor \bmod 2^d$.
Let $K$, $z$ and $w$ be $2$-adic integers such that, with congruences in $\mathbb{Z}_2$,
$\operatorname{uns}(e,d) + K \equiv \operatorname{stab}(e+1,d) \pmod{2^d}$ for all natural
numbers $d < e$, $z \equiv \operatorname{od}((2^{e-1})!) \pmod{2^e}$ for all $e \ge 1$, and
$w \equiv \lfloor ((2^e-1)!! - 1)/2^e \rfloor \pmod{2^{e-1}}$ for all $e \ge 3$. Then $K = -zw$.

The three hypotheses are the defining properties of $K$ (Theorem 1), $z$ (Corollary 8) and $w$
(the definition after Corollary 10).

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Theorem 14.
-/
public theorem_wanted unstable_translation_eq_neg_product
    (K z w : ℤ_[2])
    (hK : ∀ d e : ℕ, d < e →
      (2 : ℤ_[2]) ^ d ∣ (unstableBits e d : ℤ_[2]) + K - (stableBits (e + 1) d : ℤ_[2]))
    (hz : ∀ e : ℕ, 1 ≤ e →
      (2 : ℤ_[2]) ^ e ∣ z - (oddPart (Nat.factorial (2 ^ (e - 1))) : ℤ_[2]))
    (hw : ∀ e : ℕ, 3 ≤ e →
      (2 : ℤ_[2]) ^ (e - 1) ∣ w -
        (↑(((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e) : ℤ_[2])) :
    K = -z * w

/--
**Shifting the odd numbers below $2^e$ by a multiple of $2^e$.** For every integer $A$ and every
natural number $e \ge 2$, let $S_e$ be the set of odd integers $i$ with $1 \le i < 2^e$. Then
$$
\prod_{i \in S_e} (A \cdot 2^e + i) \equiv \prod_{i \in S_e} i \pmod{2^{3e-1}}.
$$

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Theorem 16.
-/
public theorem_wanted oddSet_product_linear_shift_congr
    (A : ℤ) (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (3 * e - 1) ∣
      (∏ i ∈ oddBelowTwoPow e, (A * (2 : ℤ) ^ e + (i : ℤ))) -
        ∏ i ∈ oddBelowTwoPow e, (i : ℤ)

/--
**Powers of shifted products over the odd numbers below $2^e$.** For all integers $A$ and $B$ and
all natural numbers $j$ and $e$ with $e \ge 2$, let $S_e$ be the set of odd integers $i$ with
$1 \le i < 2^e$. Then
$$
\prod_{i \in S_e} (A \cdot 2^e + i)^{2^j} \equiv \prod_{i \in S_e} (B \cdot 2^e + i)^{2^j}
\pmod{2^{3e-1+j}}.
$$

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 17.
-/
public theorem_wanted oddSet_product_power_shift_congr
    (A B : ℤ) (j e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (3 * e - 1 + j) ∣
      (∏ i ∈ oddBelowTwoPow e, (A * (2 : ℤ) ^ e + (i : ℤ)) ^ (2 ^ j)) -
        ∏ i ∈ oddBelowTwoPow e, (B * (2 : ℤ) ^ e + (i : ℤ)) ^ (2 ^ j)

/--
**$\hat\sigma_1$ of the odd numbers below $2^e$.** Let $e \ge 2$ and let $S_e$ be the set of odd
natural numbers $i$ with $1 \le i < 2^e$, regarded as a multiset of integers with $n$ elements,
and write $\sigma_k$ for the elementary symmetric function of degree $k$. Then the reversed
elementary symmetric function $\hat\sigma_1(S_e) = \sigma_{n-1}(S_e)$ satisfies
$\hat\sigma_1(S_e) \equiv 2^{2e-2} \pmod{2^{2e-1}}$ in $\mathbb{Z}$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 18.
-/
public theorem_wanted reverseESymm_one_oddSet_congr (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (2 * e - 1) ∣
      reverseESymm 1 (integerMultiset (oddBelowTwoPow e)) - (2 : ℤ) ^ (2 * e - 2)

/--
**$\hat\sigma_2$ of the odd numbers below $2^e$.** Let $e \ge 2$ and let $S_e$ be the set of odd
natural numbers $i$ with $1 \le i < 2^e$, regarded as a multiset of integers with $n$ elements,
and write $\sigma_k$ for the elementary symmetric function of degree $k$. Then the reversed
elementary symmetric function $\hat\sigma_2(S_e) = \sigma_{n-2}(S_e)$ satisfies
$\hat\sigma_2(S_e) \equiv 2^{e-2} \pmod{2^{e-1}}$ in $\mathbb{Z}$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 19.
-/
public theorem_wanted reverseESymm_two_oddSet_congr (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (e - 1) ∣
      reverseESymm 2 (integerMultiset (oddBelowTwoPow e)) - (2 : ℤ) ^ (e - 2)

/--
**Each residue $1 \bmod 8$ has four odd square roots modulo $2^e$.** Let $e \ge 3$ and let $S_e$
be the set of odd natural numbers $i$ with $1 \le i < 2^e$. For every natural number $v < 2^e$
with $v \equiv 1 \pmod 8$, exactly four elements $i \in S_e$ satisfy $i^2 \bmod 2^e = v$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 20.
-/
public theorem_wanted square_mod_twoPower_fiber_card
    (e : ℕ) (he : 3 ≤ e) (v : ℕ) (hv : v < 2 ^ e) (hv8 : v % 8 = 1) :
    ({i ∈ oddBelowTwoPow e | i ^ 2 % 2 ^ e = v}).card = 4

/--
**$\hat\sigma_1$ of four copies of the numbers $1 \bmod 8$ below $2^e$.** Let $e \ge 3$ and let
$M_e$ be the multiset of integers containing each natural number $n < 2^e$ with
$n \equiv 1 \pmod 8$ (that is, $1, 9, \dots, 2^e - 7$) exactly four times, let $N$ be the
number of elements of $M_e$ counted with multiplicity, and write $\sigma_k$ for the elementary
symmetric function of degree $k$. Then the reversed elementary symmetric function
$\hat\sigma_1(M_e) = \sigma_{N-1}(M_e)$ satisfies $\hat\sigma_1(M_e) \equiv 2^{e-1} \pmod{2^e}$
in $\mathbb{Z}$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21.
-/
public theorem_wanted reverseESymm_fourCopies_oneModEight_congr
    (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ e ∣
      reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e) - (2 : ℤ) ^ (e - 1)

/--
**Squared products of the odd residues omitting one factor.** Let $e \ge 1$ and let
$S_e$ be the set of odd positive integers below $2^e$. Then, as integers,
$$\sum_{i \in S_e} \Bigl(\prod_{j \in S_e \setminus \{i\}} j\Bigr)^2 \equiv 2^{e-1} \pmod{2^e}.$$

Each squared product equals the paper's $((2^e-1)!!)^2/i^2$; the product form avoids an exact
division for every summand.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Proposition 22.
-/
public theorem_wanted sum_square_erased_oddSet_product_congr
    (e : ℕ) (he : 1 ≤ e) :
    (2 : ℤ) ^ e ∣
      (∑ i ∈ oddBelowTwoPow e, (∏ j ∈ (oddBelowTwoPow e).erase i, (j : ℤ)) ^ 2) -
        (2 : ℤ) ^ (e - 1)

end

end MetaMathlibExt
