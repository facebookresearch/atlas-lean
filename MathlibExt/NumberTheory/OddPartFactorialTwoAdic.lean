/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# The odd part of dyadic factorials

This file collects the definitions for Davis's study of the odd part of `(2^e)!`. It proves the
odd-part bijection on the upper dyadic half and congruences for odd double factorials and their
normalized quotients. It also counts the odd square roots of each residue congruent to one modulo
eight, and the $\hat\sigma_1$ congruence for four copies of those residues.
-/

@[expose] public section

namespace MetaMathlibExt

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
**Odd parts biject the upper dyadic half onto the odd numbers below a power of two.**
For every natural number $e \ge 1$, the map sending each natural number to its odd part restricts
to a bijection from $I_e = \{i \in \mathbb{N} : 2^{e-1} < i \le 2^e\}$ onto the set $S_e$ of odd
natural numbers $i$ with $1 \le i < 2^e$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 5.
-/
public theorem oddPart_bijOn_upperHalf_oddSet (e : ℕ) (he : 1 ≤ e) :
    Set.BijOn oddPart (↑(dyadicUpperHalf e) : Set ℕ) (↑(oddBelowTwoPow e) : Set ℕ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  -- Scale each odd number by the largest power of two that fits below the upper bound.
  let k (u : ℕ) := Nat.log 2 (2 ^ (d + 1) / u)
  have scale_mem {u t : ℕ} (hu : 0 < u) (hle : u ≤ 2 ^ (d + 1)) :
      2 ^ t * u ∈ dyadicUpperHalf (d + 1) ↔ k u = t := by
    dsimp only [k]
    rw [mem_dyadicUpperHalf, Nat.log_eq_iff (.inr ⟨Nat.one_lt_two, (Nat.div_pos hle hu).ne'⟩),
      Nat.le_div_iff_mul_le hu, Nat.div_lt_iff_lt_mul hu, Nat.succ_sub_one, pow_succ, pow_succ,
      mul_right_comm (2 ^ t) 2 u]
    omega
  have maps : Set.MapsTo oddPart (↑(dyadicUpperHalf (d + 1))) (↑(oddBelowTwoPow (d + 1))) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := (mem_dyadicUpperHalf _ _).mp hn
    have hn0 : n ≠ 0 := ((Nat.zero_le _).trans_lt hlo).ne'
    have hodd : Odd (oddPart n) := (Nat.coprime_ordCompl Nat.prime_two hn0).odd_of_left
    refine (mem_oddSet _ _).mpr ⟨Nat.ordCompl_pos 2 hn0, ?_, hodd⟩
    have hle : oddPart n ≤ 2 ^ (d + 1) := (Nat.ordCompl_le n 2).trans hhi
    exact hle.lt_of_ne fun h ↦ hodd.not_two_dvd_nat (h.symm ▸ dvd_pow_self 2 d.succ_ne_zero)
  refine Set.InvOn.bijOn (f' := fun u ↦ 2 ^ k u * u) ⟨?_, ?_⟩ maps ?_
  · intro n hn
    obtain ⟨hu, hlt, _⟩ := (mem_oddSet _ _).mp (maps hn)
    have hfac : 2 ^ n.factorization 2 * oddPart n = n := Nat.ordProj_mul_ordCompl_eq_self n 2
    have hk := (scale_mem (t := n.factorization 2) hu hlt.le).mp (by rwa [hfac])
    change 2 ^ k (oddPart n) * oddPart n = n
    rwa [hk]
  · intro u hu
    exact Nat.ordCompl_pow_mul_of_not_dvd (k u) Nat.prime_two
      ((mem_oddSet _ _).mp hu).2.2.not_two_dvd_nat
  · intro u hu
    obtain ⟨hpos, hlt, _⟩ := (mem_oddSet _ _).mp hu
    exact (scale_mem hpos hlt.le).mpr rfl

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

namespace oddDoubleFactorial_normalized_congr

open Finset

/-- Product of the first `n` odd numbers, each translated by `x`. -/
private def block (x : ℤ) (n : ℕ) : ℤ :=
  ∏ i ∈ range n, (x + (2 * (i : ℤ) + 1))

private theorem oddDoubleFactorial_succ_eq (e : ℕ) :
    (oddDoubleFactorial (e + 1) : ℤ) = block 0 (2 ^ e) := by
  simp only [oddDoubleFactorial, oddRangeProduct, Nat.cast_prod, block, zero_add, pow_succ]
  symm
  refine prod_nbij' (fun i ↦ 2 * i + 1) (fun j ↦ j / 2) ?_ ?_ ?_ ?_ ?_ <;>
    simp only [mem_filter, mem_Icc, mem_range, Nat.odd_iff, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat, implies_true] <;> omega

private theorem block_add (x : ℤ) (m n : ℕ) :
    block x (m + n) = block x m * block (x + 2 * m) n := by
  simp [block, prod_range_add, mul_add, add_assoc]

/-- Pair the odd factors from opposite ends of a block. -/
private theorem block_pairs (x : ℤ) (m : ℕ) :
    block x (m + m) =
      ∏ i ∈ range m, (x + (2 * (i : ℤ) + 1)) * (x + (4 * m - (2 * i + 1))) := by
  rw [block_add, block, block,
    ← prod_range_reflect (fun i : ℕ ↦ x + 2 * m + (2 * (i : ℤ) + 1)) m, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have h : i < m := mem_range.mp hi
  have hcast : ((m - 1 - i : ℕ) : ℤ) = m - 1 - i := by omega
  simp only [hcast]
  ring

/-- Translating the complementary pair `j, 4m - j` by `4m` adds twice `(4m)²` to its product. -/
private theorem block_shift (m : ℕ) :
    block 0 (m + m) ≡ block (4 * m) (m + m) [ZMOD (4 * (m : ℤ)) ^ 2] := by
  rw [block_pairs, block_pairs]
  apply Int.ModEq.prod
  intro i _
  exact Int.modEq_iff_dvd.mpr ⟨2, by ring⟩

private theorem square_congr (k : ℕ) :
    (oddDoubleFactorial (k + 2) : ℤ) ^ 2 ≡ oddDoubleFactorial (k + 3)
      [ZMOD ((2 : ℤ) ^ (k + 2)) ^ 2] := by
  let m := 2 ^ k
  have hlen : 2 ^ (k + 1) = m + m := by simp [m, pow_succ, mul_two]
  have hlen' : 2 ^ (k + 2) = (m + m) + (m + m) := by rw [pow_succ, hlen, mul_two]
  have hmod : (2 : ℤ) ^ (k + 2) = 4 * m := by push_cast [m, pow_add]; ring
  rw [oddDoubleFactorial_succ_eq, oddDoubleFactorial_succ_eq, hlen, hlen', block_add 0 (m + m),
    hmod, sq (block 0 (m + m)), zero_add]
  rw [show 2 * ((m + m : ℕ) : ℤ) = 4 * m by push_cast; ring]
  exact (block_shift m).mul_left _

private theorem normalized_step {e : ℕ} (he : 2 ≤ e)
    (h : (2 : ℤ) ^ e ∣ (oddDoubleFactorial e : ℤ) - 1) :
    (2 : ℤ) ^ (e + 1) ∣ (oddDoubleFactorial (e + 1) : ℤ) - 1 ∧
    (2 : ℤ) ^ (e - 1) ∣
      ((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e -
        ((oddDoubleFactorial (e + 1) : ℤ) - 1) / (2 : ℤ) ^ (e + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := (square_congr k).dvd
  have hnext : (oddDoubleFactorial (k + 3) : ℤ) - 1 =
      2 ^ (k + 3) * (a + 2 ^ (k + 1) * (a ^ 2 + b)) := by
    rw [show (oddDoubleFactorial (k + 3) : ℤ) =
      (oddDoubleFactorial (k + 2) : ℤ) ^ 2 + ((2 : ℤ) ^ (k + 2)) ^ 2 * b by linarith,
      show (oddDoubleFactorial (k + 2) : ℤ) = 1 + 2 ^ (k + 2) * a by linarith]
    ring
  refine ⟨⟨_, hnext⟩, ?_⟩
  rw [ha, hnext, Int.mul_ediv_cancel_left _ (by positivity),
    Int.mul_ediv_cancel_left _ (by positivity)]
  exact ⟨-(a ^ 2 + b), by simp only [Nat.reduceSubDiff]; ring⟩

end oddDoubleFactorial_normalized_congr

open oddDoubleFactorial_normalized_congr in
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
public theorem oddDoubleFactorial_normalized_congr (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ e ∣ (oddDoubleFactorial e : ℤ) - 1 ∧
    (2 : ℤ) ^ (e + 1) ∣ (oddDoubleFactorial (e + 1) : ℤ) - 1 ∧
    (2 : ℤ) ^ (e - 1) ∣
      ((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e -
        ((oddDoubleFactorial (e + 1) : ℤ) - 1) / (2 : ℤ) ^ (e + 1) := by
  have h : (2 : ℤ) ^ e ∣ (oddDoubleFactorial e : ℤ) - 1 := by
    induction e, he using Nat.le_induction with
    | base => decide
    | succ e he ih => exact (normalized_step (by omega) ih).1
  exact ⟨h, normalized_step (by omega) h⟩

/--
**Product of the odd numbers below $2^e$.** For every natural number $e \ge 3$, the product of the
odd integers $i$ with $1 \le i < 2^e$ is congruent to $2^e + 1$ modulo $2^{e+1}$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 6.
-/
public theorem oddSet_product_congr (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ (e + 1) ∣
      ((∏ i ∈ oddBelowTwoPow e, i : ℕ) : ℤ) - ((2 ^ e + 1 : ℕ) : ℤ) := by
  have hparity : 1 ≡ ((oddDoubleFactorial e : ℤ) - 1) / 2 ^ e [ZMOD 2] := by
    induction e, he using Nat.le_induction with
    | base => decide
    | succ e he ih =>
      have hstep := Int.modEq_of_dvd (oddDoubleFactorial_normalized_congr e he).2.2
      exact ih.trans (hstep.symm.of_dvd (dvd_pow_self 2 (by omega)))
  have hprod : ∏ i ∈ oddBelowTwoPow e, i = oddDoubleFactorial e := by
    have hpos : 0 < (2 : ℕ) ^ e := by positivity
    simp only [oddBelowTwoPow, oddDoubleFactorial, oddRangeProduct,
      Finset.Icc_sub_one_right_eq_Ico_of_not_isMin hpos.not_isMin]
  rw [hprod]
  push_cast
  apply Int.modEq_iff_dvd.mp
  have hexact := Int.mul_ediv_cancel' (oddDoubleFactorial_normalized_congr e he).1
  simpa only [pow_succ, mul_one, hexact, sub_add_cancel] using
    (hparity.mul_left' (c := 2 ^ e)).add_right 1

namespace oddSet_product_congr_shift

open Finset oddDoubleFactorial_normalized_congr

/-- The odd numbers below `2^(k+1)`, each translated by `x`, form the block of length `2^k`. -/
private theorem prod_oddBelowTwoPow_eq_block (x : ℤ) (k : ℕ) :
    ∏ i ∈ oddBelowTwoPow (k + 1), (x + (i : ℤ)) = block x (2 ^ k) := by
  simp only [oddBelowTwoPow, block, pow_succ]
  symm
  refine prod_nbij' (fun i ↦ 2 * i + 1) (fun j ↦ j / 2) ?_ ?_ ?_ ?_ ?_ <;>
    simp only [mem_filter, mem_Ico, mem_range, Nat.odd_iff, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat, implies_true] <;> omega

end oddSet_product_congr_shift

open oddDoubleFactorial_normalized_congr oddSet_product_congr_shift in
/--
**Shifting the odd numbers below $2^e$ by $2^e$.** For every natural number $e \ge 2$, let $S_e$ be
the set of odd integers $i$ with $1 \le i < 2^e$. Then
$$
\prod_{i \in S_e} i \equiv \prod_{i \in S_e} (2^e + i) \pmod{2^{2e}}.
$$

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Proposition 9.
-/
public theorem oddSet_product_congr_shift (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (2 * e) ∣
      ((∏ i ∈ oddBelowTwoPow e, i : ℕ) : ℤ) -
        (∏ i ∈ oddBelowTwoPow e, ((2 ^ e + i : ℕ) : ℤ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  -- Pair `i` with `2^e - i`: shifting both by `2^e` changes their product by `2^(2e+1)`.
  let m := 2 ^ k
  have hlen : 2 ^ (k + 1) = m + m := by simp [m, pow_succ, mul_two]
  have hmod : (2 : ℤ) ^ (2 * (k + 2)) = (4 * (m : ℤ)) ^ 2 := by
    push_cast [m]
    ring
  have h₀ : ((∏ i ∈ oddBelowTwoPow (k + 2), i : ℕ) : ℤ) = block 0 (m + m) := by
    rw [← hlen, ← prod_oddBelowTwoPow_eq_block]
    simp
  have h₁ : ∏ i ∈ oddBelowTwoPow (k + 2), ((2 ^ (k + 2) + i : ℕ) : ℤ) = block (4 * m) (m + m) := by
    rw [← hlen, ← prod_oddBelowTwoPow_eq_block]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    push_cast [m]
    ring
  rw [h₀, h₁, hmod]
  exact (block_shift m).symm.dvd

namespace oddPart_factorial_congr_previous

open Finset

private theorem oddPart_mul (a b : ℕ) : oddPart (a * b) = oddPart a * oddPart b :=
  Nat.ordCompl_mul a b 2

private theorem oddPart_prod (s : Finset ℕ) :
    oddPart (∏ i ∈ s, i) = ∏ i ∈ s, oddPart i := by
  induction s using Finset.induction_on with
  | empty => simp [oddPart]
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, oddPart_mul, ih]

private theorem prod_Ioc_zero_eq_factorial (n : ℕ) : ∏ i ∈ Ioc 0 n, i = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prod_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ, mul_comm]

end oddPart_factorial_congr_previous

open oddPart_factorial_congr_previous in
/--
**Odd parts of consecutive dyadic factorials agree modulo a power of two.** For every natural
number $e \ge 3$, $\mathrm{od}((2^{e-1})!) \equiv \mathrm{od}((2^e)!) \pmod{2^e}$, where
$\mathrm{od}(n)$ denotes the odd part of $n$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 7.
-/
public theorem oddPart_factorial_congr_previous (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ e ∣ (oddPart (Nat.factorial (2 ^ (e - 1))) : ℤ) -
      (oddPart (Nat.factorial (2 ^ e)) : ℤ) := by
  -- Split `(2^e)!` at `2^(e-1)`; the odd parts of the upper factors are the odd numbers below
  -- `2^e` (Lemma 5), whose product is `1` modulo `2^e` (Lemma 6).
  have hfac : Nat.factorial (2 ^ e) =
      Nat.factorial (2 ^ (e - 1)) * ∏ i ∈ dyadicUpperHalf e, i := by
    rw [dyadicUpperHalf, ← prod_Ioc_zero_eq_factorial, ← prod_Ioc_zero_eq_factorial,
      Finset.prod_Ioc_consecutive _ (Nat.zero_le _)
        (Nat.pow_le_pow_right two_pos (Nat.sub_le e 1))]
  have hbij : ∏ i ∈ dyadicUpperHalf e, oddPart i = ∏ i ∈ oddBelowTwoPow e, i := by
    have h := oddPart_bijOn_upperHalf_oddSet e (by omega)
    exact Finset.prod_nbij oddPart (fun _ ha ↦ h.mapsTo ha) h.injOn h.surjOn (fun _ _ ↦ rfl)
  have hP : (2 : ℤ) ^ e ∣ ((∏ i ∈ oddBelowTwoPow e, i : ℕ) : ℤ) - 1 := by
    have h := (pow_dvd_pow 2 (Nat.le_succ e)).trans (oddSet_product_congr e he)
    have h' := dvd_add h (dvd_refl ((2 : ℤ) ^ e))
    convert h' using 1
    push_cast
    ring
  rw [hfac, oddPart_mul, oddPart_prod, hbij, Nat.cast_mul]
  generalize ((∏ i ∈ oddBelowTwoPow e, i : ℕ) : ℤ) = P at hP ⊢
  generalize (oddPart (2 ^ (e - 1)).factorial : ℤ) = a
  rw [show a - a * P = -(a * (P - 1)) by ring, dvd_neg]
  exact dvd_mul_of_dvd_right hP _

namespace square_mod_twoPower_fiber_card

/-- In either odd class modulo four, the root parameter runs through exactly two lifts
of a single residue modulo `2^k`. -/
private theorem roots_in_class (k r c w : ℕ) (hr : Odd r) (hc : r ^ 2 = 8 * c + 1)
    (hw : w < 2 ^ k) :
    ∃ a < 2 ^ k, ∀ t < 2 * 2 ^ k,
      (4 * t + r) ^ 2 % (8 * 2 ^ k) = 8 * w + 1 ↔ t = a ∨ t = a + 2 ^ k := by
  let f (t : ℕ) := 2 * t ^ 2 + r * t + c
  -- In the difference f(a) - f(b), the factor 2(a + b) + r is odd and can be cancelled.
  have congr_iff (a b : ℕ) : f a ≡ f b [MOD 2 ^ k] ↔ a ≡ b [MOD 2 ^ k] := by
    constructor
    · intro h
      have hodd : Odd (2 * (a + b) + r) := (even_two_mul _).add_odd hr
      apply Nat.ModEq.cancel_left_of_coprime (hodd.coprime_two_left.pow_left k)
      convert (Nat.ModEq.add_right_cancel' c h).add_right (2 * a * b) using 1 <;> ring
    · intro h
      exact (((h.pow 2).mul_left 2).add (h.mul_left r)).add_right c
  let g (a : Fin (2 ^ k)) : Fin (2 ^ k) := ⟨f a % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
  have inj : Function.Injective g := by
    intro a b h
    exact Fin.ext (((congr_iff a b).mp (congrArg Fin.val h)).eq_of_lt_of_lt a.isLt b.isLt)
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective inj ⟨w, hw⟩
  have ha' : f a ≡ w [MOD 2 ^ k] := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hw] using congrArg Fin.val ha
  refine ⟨a, a.isLt, fun t ht ↦ ?_⟩
  have hs : (4 * t + r) ^ 2 = 8 * f t + 1 := by
    rw [add_sq, hc]
    dsimp [f]
    ring
  calc
    _ ↔ 8 * f t + 1 ≡ 8 * w + 1 [MOD 8 * 2 ^ k] := by
      rw [hs, Nat.ModEq, Nat.mod_eq_of_lt (show 8 * w + 1 < 8 * 2 ^ k by omega)]
    _ ↔ f t ≡ w [MOD 2 ^ k] := by
      rw [Nat.ModEq.add_iff_right (Nat.ModEq.refl 1), Nat.ModEq.mul_left_cancel_iff' (by decide)]
    _ ↔ t ≡ a.val [MOD 2 ^ k] := by
      rw [← congr_iff t a]
      exact ⟨fun h ↦ h.trans ha'.symm, fun h ↦ h.trans ha'⟩
    _ ↔ _ := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt a.isLt]
      by_cases h : t < 2 ^ k
      · rw [Nat.mod_eq_of_lt h]
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show t - 2 ^ k < 2 ^ k by omega)]
        omega

end square_mod_twoPower_fiber_card

open square_mod_twoPower_fiber_card in
/--
**Each residue $1 \bmod 8$ has four odd square roots modulo $2^e$.** Let $e \ge 3$ and let $S_e$
be the set of odd natural numbers $i$ with $1 \le i < 2^e$. For every natural number $v < 2^e$
with $v \equiv 1 \pmod 8$, exactly four elements $i \in S_e$ satisfy $i^2 \bmod 2^e = v$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 20.
-/
public theorem square_mod_twoPower_fiber_card
    (e : ℕ) (he : 3 ≤ e) (v : ℕ) (hv : v < 2 ^ e) (hv8 : v % 8 = 1) :
    ({i ∈ oddBelowTwoPow e | i ^ 2 % 2 ^ e = v}).card = 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  let n := 2 ^ k
  have hm : 2 ^ (k + 3) = 8 * n := by simp [n, pow_add, Nat.mul_comm]
  rw [hm] at hv ⊢
  obtain ⟨w, rfl⟩ : ∃ w, v = 8 * w + 1 := ⟨v / 8, by omega⟩
  have hw : w < n := by omega
  obtain ⟨a, ha, h₁⟩ := roots_in_class k 1 0 w (by decide) (by decide) hw
  obtain ⟨b, hb, h₃⟩ := roots_in_class k 3 1 w (by decide) (by decide) hw
  change a < n at ha
  change b < n at hb
  apply Finset.card_eq_four.mpr
  refine ⟨4 * a + 1, 4 * (a + n) + 1, 4 * b + 3, 4 * (b + n) + 3,
    by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  ext i
  simp only [Finset.mem_filter, mem_oddSet, hm, Nat.odd_iff, Finset.mem_insert,
    Finset.mem_singleton]
  by_cases hi : i < 8 * n ∧ i % 2 = 1
  · obtain ⟨t, rfl | rfl⟩ : ∃ t, i = 4 * t + 1 ∨ i = 4 * t + 3 := ⟨i / 4, by omega⟩
    · rw [h₁ t (by omega)]
      omega
    · rw [h₃ t (by omega)]
      omega
  · omega


namespace reverseESymm_fourCopies_oneModEight_congr

private theorem cast_prod (t : Multiset ℤ) (m : ℕ) :
    ((t.prod : ℤ) : ZMod m) = (t.map (Int.castRingHom (ZMod m))).prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih => simp [ih]

private theorem cast_sum (t : Multiset ℤ) (m : ℕ) :
    ((t.sum : ℤ) : ZMod m) = (t.map (Int.castRingHom (ZMod m))).sum := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih => simp [ih]

private theorem cast_esymm (s : Multiset ℤ) (k : ℕ) (m : ℕ) :
    ((s.esymm k : ℤ) : ZMod m) = (s.map (Int.castRingHom (ZMod m))).esymm k := by
  rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map,
    cast_sum, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun t _ => ?_
  exact cast_prod t m

/-- Four copies factorisation, over any commutative ring. -/
private theorem reverseESymm_one_four_smul {R : Type*} [CommRing R]
    (s : Multiset R) (hs : 1 ≤ s.card) :
    reverseESymm 1 (4 • s) = 4 * s.prod ^ 3 * reverseESymm 1 s := by
  have hprod : ((4 • s).map fun r => Polynomial.X + Polynomial.C r).prod =
      ((s.map fun r => Polynomial.X + Polynomial.C r).prod) ^ 4 := by
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
  have hcard4 : (4 • s).card = 4 * s.card := by simp
  have key : reverseESymm 1 (4 • s) =
      ((s.map fun r => Polynomial.X + Polynomial.C r).prod ^ 4).coeff 1 := by
    have hcoeff := Multiset.prod_X_add_C_coeff (s := 4 • s) (k := 1) (by omega)
    rw [hprod] at hcoeff
    change (4 • s).esymm ((4 • s).card - 1) = _
    exact hcoeff.symm
  rw [key]
  have h1 : (((s.map fun r => Polynomial.X + Polynomial.C r).prod ^ 4).coeff 1) =
      (((s.map fun r => Polynomial.X + Polynomial.C r).prod ^ 4).derivative).coeff 0 := by
    rw [Polynomial.coeff_derivative]; simp
  rw [h1, Polynomial.coeff_zero_eq_eval_zero, Polynomial.derivative_pow]
  have hq0 : ((s.map fun r => Polynomial.X + Polynomial.C r).prod).eval 0 = s.prod := by
    simp [Polynomial.eval_multiset_prod]
  have hdq0 : ((s.map fun r => Polynomial.X + Polynomial.C r).prod).derivative.eval 0 =
      reverseESymm 1 s := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp only [Nat.cast_zero, zero_add, mul_one]
    rw [reverseESymm_eq, Multiset.prod_X_add_C_coeff _ hs]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, hq0, hdq0]
  ring

private theorem decomp (e : ℕ) (he : 3 ≤ e) :
    oneModEightBelowTwoPow (e + 2) =
      (Finset.range 4 ×ˢ oneModEightBelowTwoPow e).image
        fun p : ℕ × ℕ => p.2 + p.1 * 2 ^ e := by
  have h8 : (8 : ℕ) ∣ 2 ^ e := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 he
  have hpow : (2 : ℕ) ^ (e + 2) = 4 * 2 ^ e := by
    rw [pow_add]; ring
  have hpos : 0 < (2 : ℕ) ^ e := by positivity
  ext n
  simp only [mem_oneModEight, Finset.mem_image, Finset.mem_product, Finset.mem_range]
  constructor
  · intro ⟨hn, hmod⟩
    have hdiv : n < 4 * 2 ^ e := by rw [← hpow]; exact hn
    refine ⟨(n / 2 ^ e, n % 2 ^ e), ⟨?_, ?_⟩, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hpos]; exact hdiv
    · refine ⟨Nat.mod_lt _ hpos, ?_⟩
      have hmm : (n % 2 ^ e) % 8 = n % 8 := Nat.mod_mod_of_dvd n h8
      omega
    · change n % 2 ^ e + n / 2 ^ e * 2 ^ e = n
      rw [add_comm, Nat.mul_comm]
      exact Nat.div_add_mod n (2 ^ e)
  · rintro ⟨⟨k, n0⟩, ⟨hk, ⟨hn0, hmod0⟩⟩, rfl⟩
    dsimp only
    have h0 : (k * 2 ^ e) % 8 = 0 :=
      Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left h8 k)
    have hmul : k * 2 ^ e ≤ 3 * 2 ^ e := Nat.mul_le_mul_right _ (by omega)
    refine ⟨?_, ?_⟩
    · rw [hpow]; omega
    · rw [Nat.add_mod, h0, Nat.add_zero, Nat.mod_mod]; exact hmod0

private theorem injOn_decomp (e : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.2 + p.1 * 2 ^ e)
      (↑(Finset.range 4 ×ˢ oneModEightBelowTwoPow e)) := by
  intro p hp q hq h
  have hpos : 0 < (2 : ℕ) ^ e := by positivity
  have hpb : p.2 < 2 ^ e := by
    have := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    exact (mem_oneModEight _ _).mp this.2 |>.1
  have hqb : q.2 < 2 ^ e := by
    have := Finset.mem_product.mp (Finset.mem_coe.mp hq)
    exact (mem_oneModEight _ _).mp this.2 |>.1
  have hdivp : (p.2 + p.1 * 2 ^ e) / 2 ^ e = p.1 := by
    rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hpb, zero_add]
  have hdivq : (q.2 + q.1 * 2 ^ e) / 2 ^ e = q.1 := by
    rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hqb, zero_add]
  have hmodp : (p.2 + p.1 * 2 ^ e) % 2 ^ e = p.2 := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpb]
  have hmodq : (q.2 + q.1 * 2 ^ e) % 2 ^ e = q.2 := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hqb]
  have h' : p.2 + p.1 * 2 ^ e = q.2 + q.1 * 2 ^ e := h
  have h1 : p.1 = q.1 := by rw [← hdivp, ← hdivq, h']
  have h2 : p.2 = q.2 := by rw [← hmodp, ← hmodq, h']
  exact Prod.ext h1 h2

private theorem poly_identity (e : ℕ) (he : 3 ≤ e) :
    ∏ n ∈ oneModEightBelowTwoPow (e + 2),
        (Polynomial.X + Polynomial.C ((n : ZMod (2 ^ e)) : ZMod (2 ^ e))) =
      ∏ n0 ∈ oneModEightBelowTwoPow e,
        (Polynomial.X + Polynomial.C ((n0 : ZMod (2 ^ e)) : ZMod (2 ^ e))) ^ 4 := by
  rw [decomp e he, Finset.prod_image (injOn_decomp e)]
  rw [Finset.prod_product, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro n0 hn0
  rw [show (4 : ℕ) = (Finset.range 4).card by simp, ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro k hk
  have hcast : ((n0 + k * 2 ^ e : ℕ) : ZMod (2 ^ e)) = (n0 : ZMod (2 ^ e)) := by
    have h0 : ((2 : ZMod (2 ^ e)) ^ e = 0) := by
      have h := ZMod.natCast_self (2 ^ e)
      rw [Nat.cast_pow] at h
      simpa using h
    push_cast
    rw [h0, mul_zero, add_zero]
  rw [hcast]

private theorem card_oneModEight_pos (e : ℕ) (he : 3 ≤ e) :
    1 ≤ (oneModEightBelowTwoPow e).card := by
  have hlt : (1 : ℕ) < 2 ^ e := by
    calc (1 : ℕ) < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he
  have hmem : (1 : ℕ) ∈ oneModEightBelowTwoPow e := by
    rw [mem_oneModEight]; omega
  exact Finset.one_le_card.mpr ⟨1, hmem⟩

private theorem esymm_congr_step (e : ℕ) (he : 3 ≤ e) :
    Int.ModEq ((2 : ℤ) ^ e)
      (reverseESymm 1 (integerMultiset (oneModEightBelowTwoPow (e + 2))))
      (reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e)) := by
  have hpoly := poly_identity e he
  have hL : (∏ n ∈ oneModEightBelowTwoPow (e + 2),
        (Polynomial.X + Polynomial.C ((n : ZMod (2 ^ e)) : ZMod (2 ^ e)))).coeff 1 =
      ((reverseESymm 1 (integerMultiset (oneModEightBelowTwoPow (e + 2))) : ℤ) :
        ZMod (2 ^ e)) := by
    rw [Finset.prod_X_add_C_coeff (oneModEightBelowTwoPow (e + 2))
      (fun n : ℕ => (n : ZMod (2 ^ e))) (k := 1)
      (by exact card_oneModEight_pos (e + 2) (by omega))]
    rw [← Finset.esymm_map_val]
    rw [reverseESymm_eq, cast_esymm]
    congr 1
    · simp [integerMultiset, Multiset.map_map]
    · rw [integerMultiset_card]
  have hR : (∏ n0 ∈ oneModEightBelowTwoPow e,
        (Polynomial.X + Polynomial.C ((n0 : ZMod (2 ^ e)) : ZMod (2 ^ e))) ^ 4).coeff 1 =
      ((reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e) : ℤ) : ZMod (2 ^ e)) := by
    rw [Finset.prod_pow]
    set A : Multiset (ZMod (2 ^ e)) :=
      (integerMultiset (oneModEightBelowTwoPow e)).map (Int.castRingHom (ZMod (2 ^ e)))
      with hA
    have hq : (∏ n0 ∈ oneModEightBelowTwoPow e,
          (Polynomial.X + Polynomial.C ((n0 : ZMod (2 ^ e)) : ZMod (2 ^ e)))) =
        (A.map fun r => Polynomial.X + Polynomial.C r).prod := by
      rw [hA, Finset.prod_eq_multiset_prod]
      simp only [integerMultiset, Multiset.map_map, Function.comp_apply]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)
      change (Polynomial.X + Polynomial.C ((x : ZMod (2 ^ e)) : ZMod (2 ^ e))) =
        Polynomial.X + Polynomial.C (((x : ℤ) : ZMod (2 ^ e)))
      rw [Int.cast_natCast]
    rw [hq]
    have hAcard0 : A.card = (oneModEightBelowTwoPow e).card := by
      simp [hA, integerMultiset_card]
    have hcoeff := Multiset.prod_X_add_C_coeff (s := 4 • A) (k := 1) (by
      have hc := card_oneModEight_pos e he
      have hcard4 : (4 • A).card = 4 * (oneModEightBelowTwoPow e).card := by
        simp [Multiset.card_nsmul, hAcard0]
      omega)
    have hprod : ((4 • A).map fun r => Polynomial.X + Polynomial.C r).prod =
        ((A.map fun r => Polynomial.X + Polynomial.C r).prod) ^ 4 := by
      rw [Multiset.map_nsmul, Multiset.prod_nsmul]
    rw [hprod] at hcoeff
    have hcast : ((reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e) : ℤ) :
        ZMod (2 ^ e)) = (4 • A).esymm ((4 • A).card - 1) := by
      rw [fourCopiesOneModEight_eq, reverseESymm_eq, cast_esymm,
        Multiset.map_nsmul, ← hA]
      congr 1
      simp [hAcard0, Multiset.card_nsmul, integerMultiset_card]
    rw [hcast]
    exact hcoeff
  have hcast : ((reverseESymm 1 (integerMultiset (oneModEightBelowTwoPow (e + 2))) : ℤ) :
      ZMod (2 ^ e)) =
      ((reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e) : ℤ) : ZMod (2 ^ e)) := by
    rw [← hL, ← hR, hpoly]
  rw [ZMod.intCast_eq_intCast_iff] at hcast
  have hmod : ((2 ^ e : ℕ) : ℤ) = (2 : ℤ) ^ e := by push_cast; ring
  rwa [hmod] at hcast

private theorem prod_odd (e : ℕ) :
    Odd ((integerMultiset (oneModEightBelowTwoPow e)).prod ^ 3) := by
  apply Odd.pow
  have hprod : (integerMultiset (oneModEightBelowTwoPow e)).prod =
      ∏ n ∈ oneModEightBelowTwoPow e, (n : ℤ) := by
    rw [integerMultiset, Finset.prod_eq_multiset_prod]
  rw [hprod]
  refine Finset.prod_induction (fun n : ℕ => (n : ℤ)) Odd
    (fun a b ha hb => ha.mul hb) (by decide) ?_
  intro n hn
  have hmod : n % 8 = 1 := (mem_oneModEight _ _).mp hn |>.2
  obtain ⟨q, rfl⟩ : ∃ q, n = 8 * q + 1 := ⟨n / 8, by omega⟩
  exact ⟨(4 * q : ℤ), by push_cast; ring⟩

private theorem step (e : ℕ) (he : 3 ≤ e)
    (ih : (2 : ℤ) ^ e ∣ reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e) -
      (2 : ℤ) ^ (e - 1)) :
    (2 : ℤ) ^ (e + 2) ∣ reverseESymm 1 (fourCopiesOneModEightBelowTwoPow (e + 2)) -
      (2 : ℤ) ^ (e + 2 - 1) := by
  rw [show e + 2 - 1 = e + 1 from by omega]
  have hA := reverseESymm_one_four_smul
    (integerMultiset (oneModEightBelowTwoPow (e + 2)))
    (by rw [integerMultiset_card]; exact card_oneModEight_pos (e + 2) (by omega))
  have hB := esymm_congr_step e he
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hB
  obtain ⟨u, hu⟩ := ih
  obtain ⟨v, hv⟩ := prod_odd (e + 2)
  set P : ℤ := (integerMultiset (oneModEightBelowTwoPow (e + 2))).prod with hP
  set E : ℤ := reverseESymm 1 (integerMultiset (oneModEightBelowTwoPow (e + 2))) with hE
  set R : ℤ := reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e) with hR
  have hEeq : E = R - (2 : ℤ) ^ e * t := by omega
  have hReq : R = (2 : ℤ) ^ (e - 1) + (2 : ℤ) ^ e * u := by omega
  have hp1 : (2 : ℤ) ^ (e + 2) = 4 * (2 : ℤ) ^ e := by rw [pow_add]; ring
  have hp2 : (2 : ℤ) ^ (e + 1) = 4 * (2 : ℤ) ^ (e - 1) := by
    have h : e + 1 = (e - 1) + 2 := by omega
    rw [h, pow_add]; ring
  have hp3 : (2 : ℤ) ^ e = 2 * (2 : ℤ) ^ (e - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    change (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k
    rw [pow_succ]; ring
  refine ⟨v + P ^ 3 * (u - t), ?_⟩
  rw [fourCopiesOneModEight_eq, hA, hEeq, hReq, hv, hp1, hp2, hp3]
  ring

end reverseESymm_fourCopies_oneModEight_congr

open reverseESymm_fourCopies_oneModEight_congr in
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
public theorem reverseESymm_fourCopies_oneModEight_congr
    (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ e ∣
      reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e) - (2 : ℤ) ^ (e - 1) := by
  have pair : ∀ k : ℕ,
      ((2 : ℤ) ^ (2 * k + 3) ∣
        reverseESymm 1 (fourCopiesOneModEightBelowTwoPow (2 * k + 3)) -
          (2 : ℤ) ^ (2 * k + 3 - 1)) ∧
      ((2 : ℤ) ^ (2 * k + 4) ∣
        reverseESymm 1 (fourCopiesOneModEightBelowTwoPow (2 * k + 4)) -
          (2 : ℤ) ^ (2 * k + 4 - 1)) := by
    intro k
    induction k with
    | zero => exact ⟨by decide, by decide⟩
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · have hEq : 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by ring
        rw [hEq]
        exact step (2 * k + 3) (by omega) ih.1
      · have hEq : 2 * (k + 1) + 4 = (2 * k + 4) + 2 := by ring
        rw [hEq]
        exact step (2 * k + 4) (by omega) ih.2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, e = 2 * k + 3 ∨ e = 2 * k + 4 := ⟨(e - 3) / 2, by omega⟩
  rcases hk with rfl | rfl
  · exact (pair k).1
  · exact (pair k).2

end MetaMathlibExt
