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
`oddPart n` is the factor of `n` left after removing the full power of two in
`n`.  The paper writes this as `od(n)`; the formalization reuses Mathlib's
`ordCompl[2] n`, rather than introducing a quotient with a separately defined
valuation.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of od.
-/
public def oddPart (n : ℕ) : ℕ :=
  ordCompl[2] n

/--
The characteristic formula for `oddPart`: it divides `n` by `2` raised to the
exponent recorded by `Nat.factorization`.  This makes the correspondence with
the paper's `n / 2^{ν(n)}` explicit.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of od.
-/
public theorem oddPart_eq (n : ℕ) :
    oddPart n = n / 2 ^ n.factorization 2 := by
  rfl

/--
`oddRangeProduct l m` is the product of the odd natural numbers in the closed
interval `[l,m]`.  This is the paper's `odpr(l,m)`; a filtered `Finset.Icc`
makes both endpoints and the oddness restriction explicit.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of odpr.
-/
public def oddRangeProduct (l m : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Icc l m).filter Odd, j

/--
The characteristic expansion of `oddRangeProduct` is exactly the product over
the closed interval filtered by `Odd`; this lemma exposes the computation used
for the paper's `odpr(l,m)`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of odpr.
-/
public theorem oddRangeProduct_eq (l m : ℕ) :
    oddRangeProduct l m = ∏ j ∈ (Finset.Icc l m).filter Odd, j := by
  rfl

/--
`oddProductBlock m` is the odd product from `2^(m-1)+1` through `2^m-1`, matching the
paper's definition.  Natural subtraction is used only in `m-1`, exactly as in
the paper; all results that need a nontruncated exponent impose a lower bound.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of h.
-/
public def oddProductBlock (m : ℕ) : ℕ :=
  oddRangeProduct (2 ^ (m - 1) + 1) (2 ^ m - 1)

/--
The characteristic formula for `h` unfolds it to the paper's stated odd-range
product, including its lower and upper endpoints.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of h.
-/
public theorem oddProductBlock_eq (m : ℕ) :
    oddProductBlock m = oddRangeProduct (2 ^ (m - 1) + 1) (2 ^ m - 1) := by
  rfl

/--
`unstableBits e d` extracts the `d` bits beginning at position `e+1` from
`od((2^e)!)`: natural division shifts right and remainder modulo `2^d` keeps
the requested window.  The paper assumes `e>d` only when asserting Theorem 1,
so the computational definition itself is total.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of uns.
-/
public def unstableBits (e d : ℕ) : ℕ :=
  oddPart (Nat.factorial (2 ^ e)) / 2 ^ (e + 1) % 2 ^ d

/--
The characteristic formula for `uns` explicitly identifies the shifted and
reduced odd factorial whose least-significant-first binary digits are the
paper's first `d` unstable bits.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of uns.
-/
public theorem unstableBits_eq (e d : ℕ) :
    unstableBits e d = oddPart (Nat.factorial (2 ^ e)) / 2 ^ (e + 1) % 2 ^ d := by
  rfl

/--
`stableBits s d` extracts positions `s,...,s+d-1` from
`od((2^(s+d-1))!)`.  Substituting `s=e+1` gives the paper's
`stab(e+1,d)`, namely positions `e+1,...,e+d` of `od((2^(e+d))!)`.
The total definition uses truncated natural subtraction only outside the
paper's applications, where `s=e+1`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of stab.
-/
public def stableBits (s d : ℕ) : ℕ :=
  oddPart (Nat.factorial (2 ^ (s + d - 1))) / 2 ^ s % 2 ^ d

/--
The characteristic formula for `stab` exposes the factorial exponent, right
shift, and modulus; at `s=e+1` these are respectively `e+d`, `e+1`, and `d`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of stab.
-/
public theorem stableBits_eq (s d : ℕ) :
    stableBits s d = oddPart (Nat.factorial (2 ^ (s + d - 1))) / 2 ^ s % 2 ^ d := by
  rfl

/--
The smaller executable unstable-window check `uns(4,2)=3` witnesses that the
definition extracts bits by first shifting and then reducing modulo `2^2`.
It replaces the paper's much larger `uns(17,7)=74` check, whose direct
factorial evaluation is impractical with the non-native kernel evaluator.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Worked example after Theorem 1.
-/
public theorem unstableBits_four_two : unstableBits 4 2 = 3 := by
  change Nat.factorial 16 / 2 ^ (Nat.factorial 16).factorization 2 / 32 % 4 = 3
  rw [Nat.factorization_factorial (p := 2) (n := 16) (b := 5)
    (by norm_num) (by norm_num [Nat.log])]
  norm_num [Finset.sum_Ico_succ_top]

/--
The smaller executable stable-window check `stab(5,2)=0` validates the same
factorial, shift, and remainder convention used in the paper's larger
`stab(18,7)=55` example, whose direct factorial evaluation is impractical with
the non-native kernel evaluator.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Worked example after Theorem 1.
-/
public theorem stableBits_five_two : stableBits 5 2 = 0 := by
  change Nat.factorial 64 / 2 ^ (Nat.factorial 64).factorization 2 / 32 % 4 = 0
  rw [Nat.factorization_factorial (p := 2) (n := 64) (b := 7)
    (by norm_num) (by norm_num [Nat.log])]
  norm_num [Finset.sum_Ico_succ_top]

/--
`dyadicUpperHalf e` is the finite interval `I_e={i | 2^(e-1)<i≤2^e}`.  The paper's
interval is represented by `Finset.Ioc`; Lemma 5 supplies `1≤e`, since the
displayed interval degenerates under natural subtraction at `e=0`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of I_e.
-/
public def dyadicUpperHalf (e : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ (e - 1)) (2 ^ e)

/--
Membership in `dyadicUpperHalf e` is precisely the conjunction
`2^(e-1)<i ∧ i≤2^e`, making the two inequalities defining `I_e` explicit.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of I_e.
-/
public theorem mem_dyadicUpperHalf (e i : ℕ) :
    i ∈ dyadicUpperHalf e ↔ 2 ^ (e - 1) < i ∧ i ≤ 2 ^ e := by
  simp [dyadicUpperHalf]

/--
`oddBelowTwoPow e` is `S_e`, the odd positive natural numbers strictly below `2^e`.
The bounds are encoded by `Ico 1 (2^e)` and oddness by a filter.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of S_e.
-/
public def oddBelowTwoPow (e : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (2 ^ e)).filter Odd

/--
Membership in `oddBelowTwoPow e` means simultaneously `1≤i`, `i<2^e`, and `Odd i`,
which are exactly the three clauses in the paper's definition of `S_e`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of S_e.
-/
public theorem mem_oddSet (e i : ℕ) :
    i ∈ oddBelowTwoPow e ↔ 1 ≤ i ∧ i < 2 ^ e ∧ Odd i := by
  simp [oddBelowTwoPow, and_assoc]

/--
`integerMultiset s` changes the elements of a natural-number finite set to
integers while preserving multiplicity.  This is the explicit coercion used
when the paper's products and symmetric functions enter integer congruences.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Convention for finite multisets.
-/
public def integerMultiset (s : Finset ℕ) : Multiset ℤ :=
  s.val.map fun n : ℕ => (n : ℤ)

/--
The characteristic cardinality formula states that casting a finite set to an
integer multiset neither adds nor removes entries.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Convention for finite multisets.
-/
public theorem integerMultiset_card (s : Finset ℕ) :
    (integerMultiset s).card = s.card := by
  simp [integerMultiset]

/--
`reverseESymm i s` is the elementary symmetric function of degree
`s.card-i`.  It formalizes the paper's reversed indexing
`σ̂_i(S)=σ_(n-i)(S)` for a multiset of cardinality `n`; truncated subtraction
is Mathlib's standard interpretation when `i>n`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of σ̂_i.
-/
public def reverseESymm {R : Type*} [CommSemiring R] (i : ℕ) (s : Multiset R) : R :=
  Multiset.esymm s (s.card - i)

/--
The characteristic formula for `reverseESymm` is the paper's reversal of the
elementary-symmetric degree from `i` to `s.card-i`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of σ̂_i.
-/
public theorem reverseESymm_eq {R : Type*} [CommSemiring R] (i : ℕ) (s : Multiset R) :
    reverseESymm i s = Multiset.esymm s (s.card - i) := by
  rfl

/--
`oddDoubleFactorial e` is `(2^e-1)!!`, represented through the paper's identity
as `odpr(1,2^e-1)`.  The parameter is the exponent `e`, not the odd endpoint.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of (2^e-1)!!.
-/
public def oddDoubleFactorial (e : ℕ) : ℕ :=
  oddRangeProduct 1 (2 ^ e - 1)

/--
The characteristic formula unfolds `oddDoubleFactorial e` to the odd-range
product from `1` through `2^e-1`, exactly as stated in the paper.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition of (2^e-1)!!.
-/
public theorem oddDoubleFactorial_eq (e : ℕ) :
    oddDoubleFactorial e = oddRangeProduct 1 (2 ^ e - 1) := by
  rfl

/--
`oneModEightBelowTwoPow e` is the finite set of natural numbers below `2^e` congruent to
`1` modulo `8`, i.e. the displayed sequence `{1,9,...,2^e-7}` in Lemma 21.
Using a filter avoids an endpoint subtraction at small `e`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21 notation.
-/
public def oneModEightBelowTwoPow (e : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ e)).filter fun n => n % 8 = 1

/--
Membership in `oneModEightBelowTwoPow e` is exactly the pair of clauses `n<2^e` and
`n≡1 (mod 8)`, with the congruence represented by natural remainder.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21 notation.
-/
public theorem mem_oneModEight (e n : ℕ) :
    n ∈ oneModEightBelowTwoPow e ↔ n < 2 ^ e ∧ n % 8 = 1 := by
  simp [oneModEightBelowTwoPow]

/--
`fourCopiesOneModEightBelowTwoPow e` is the multiset containing four copies of every
member of `{1,9,...,2^e-7}`.  Multiset scalar multiplication is the formal
counterpart of the paper's phrase “four copies”.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21.
-/
public def fourCopiesOneModEightBelowTwoPow (e : ℕ) : Multiset ℤ :=
  4 • integerMultiset (oneModEightBelowTwoPow e)

/--
The characteristic formula for `fourCopiesOneModEightBelowTwoPow` exposes the multiset
scalar multiplication used to create four occurrences of every integer in the
`1 mod 8` set.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21.
-/
public theorem fourCopiesOneModEight_eq (e : ℕ) :
    fourCopiesOneModEightBelowTwoPow e = 4 • integerMultiset (oneModEightBelowTwoPow e) := by
  rfl

/--
There is a 2-adic integer `K` such that for every `d<e`, adding `K` to the
unstable window `unstableBits e d` gives the stable window `stableBits (e+1) d` modulo `2^d`.
The congruence is represented by divisibility of the difference in `ℤ_[2]`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Theorem 1.
-/
public theorem_wanted exists_twoAdic_unstable_add_eq_stable :
    ∃ K : ℤ_[2], ∀ d e : ℕ, d < e →
      (2 : ℤ_[2]) ^ d ∣ (unstableBits e d : ℤ_[2]) + K - (stableBits (e + 1) d : ℤ_[2])

/--
For `e≥1`, the odd part of `(2^e)!` equals the product over `m=2,...,e` of
`h(m)^(e+1-m)`.  The finite range is `Finset.Icc 2 e`; all quantities remain
natural numbers because this is an exact factorial identity, not a congruence.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Proposition 3.
-/
public theorem_wanted oddPart_factorial_eq_prod_h (e : ℕ) (he : 1 ≤ e) :
    oddPart (Nat.factorial (2 ^ e)) =
      ∏ m ∈ Finset.Icc 2 e, oddProductBlock m ^ (e + 1 - m)

/--
For `4≤m` and `m-1≤B≤3m-7`, put `d=2+⌊(B-m)/2⌋`, written in `ℕ` as `(B+4-m)/2`
(so `d=1` when `B=m-1`); then `h(m)` is congruent modulo `2^B` to the stated initial
odd-range product raised to `2^(m-1-d)`.  Divisibility in `ℤ` represents the congruence.
The printed hypotheses `2≤m-1≤B≤3m-7` also allow `m=3`, whose only admissible case is
`(m,B)=(3,2)`; there `d=1`, `h(3)=35`, and the comparison value is `25`, whose difference
`10` is not divisible by `4`.  Requiring `4≤m` removes exactly that case and keeps every
other printed case, including `B=m-1` (e.g. `(m,B)=(4,3)`: `d=1`, `h(4)=19305`, `9^4=6561`,
`8∣12744`).

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
For `e≥1`, the map taking a number to its odd part is a bijection from
`I_e=(2^(e-1),2^e]` onto `S_e`, expressed as `Set.BijOn` between the coerced
finite sets.  The lower bound is added because natural subtraction makes the
paper's interval degenerate at `e=0`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 5.
-/
public theorem_wanted oddPart_bijOn_upperHalf_oddSet (e : ℕ) (he : 1 ≤ e) :
    Set.BijOn oddPart (↑(dyadicUpperHalf e) : Set ℕ) (↑(oddBelowTwoPow e) : Set ℕ)

/--
For `e≥3`, the product of all positive odd integers below `2^e` is congruent
to `2^e+1` modulo `2^(e+1)`.  Integer divisibility is used so subtraction does
not truncate, while the product itself is the natural-number product over
`S_e`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 6.
-/
public theorem_wanted oddSet_product_congr (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ (e + 1) ∣
      ((∏ i ∈ oddBelowTwoPow e, i : ℕ) : ℤ) - ((2 ^ e + 1 : ℕ) : ℤ)

/--
For `e≥3`, the odd parts of `(2^(e-1))!` and `(2^e)!` agree modulo `2^e`.
The factorial values are naturals, but their difference is taken in `ℤ` to
avoid truncated subtraction.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 7.
-/
public theorem_wanted oddPart_factorial_congr_previous (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ e ∣ (oddPart (Nat.factorial (2 ^ (e - 1))) : ℤ) -
      (oddPart (Nat.factorial (2 ^ e)) : ℤ)

/--
There is a 2-adic integer `z` congruent to `od((2^(e-1))!)` modulo `2^e` for
every `e≥1`.  The paper's limiting equality is represented by divisibility in
`ℤ_[2]`; the explicit lower bound avoids a truncated exponent in the factorial.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 8.
-/
public theorem_wanted exists_twoAdic_oddPart_factorial_limit :
    ∃ z : ℤ_[2], ∀ e : ℕ, 1 ≤ e →
      (2 : ℤ_[2]) ^ e ∣ z - (oddPart (Nat.factorial (2 ^ (e - 1))) : ℤ_[2])

/--
For `e≥2`, the product over `i∈S_e` of `i` agrees modulo `2^(2e)` with the
product of `2^e+i`.  Both natural products are cast to `ℤ` before subtraction,
so the divisibility formulation of congruence cannot truncate.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Proposition 9.
-/
public theorem_wanted oddSet_product_congr_shift (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (2 * e) ∣
      ((∏ i ∈ oddBelowTwoPow e, i : ℕ) : ℤ) -
        (∏ i ∈ oddBelowTwoPow e, ((2 ^ e + i : ℕ) : ℤ))

/--
For `e≥3`, the two normalized odd double-factorial differences are congruent modulo `2^(e-1)`. The
paper states `e≥2`, but at `e=2` the first quotient is not an integer: `(2^2-1)!! - 1 = 2` is not
divisible by `4`; the paper's proof takes integrality from Lemma 6, which needs `e≥3`. The
conjunction explicitly records that `2^e` and `2^(e+1)` divide the respective numerators, justifying
the two integer quotients; the final clause is the paper's congruence, represented in `ℤ`.

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
There is a 2-adic integer `w` agreeing modulo `2^(e-1)` with the normalized
odd double-factorial difference for every `e≥3` (the paper writes `e≥2`; at
`e=2` the quotient `(3-1)/4` is not an integer, see Corollary 10).  This packages the defining
property used later without introducing a global constant; the quotient is
integer division, whose exactness is supplied by Corollary 10.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition after Corollary 10.
-/
public theorem_wanted exists_twoAdic_oddDoubleFactorial_limit :
    ∃ w : ℤ_[2], ∀ e : ℕ, 3 ≤ e →
      (2 : ℤ_[2]) ^ (e - 1) ∣ w -
        (↑(((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e) : ℤ_[2])

/--
For `e≥3`, the normalized difference of consecutive odd factorial parts is
congruent to `z*w` modulo `2^(e-1)`.  Rather than defining global constants,
`z` and `w` are quantified together with exactly their Corollary 8 and
post-Corollary 10 congruence properties; the displayed quotient is formed in
`ℤ`, cast to `ℤ_[2]`, and compared there.

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
Any `K`, `z`, and `w` satisfying their defining properties obey `K=-z*w`.
The hypothesis on `K` reproduces the full Theorem 1 property for every
`d<e`; the other hypotheses reproduce Corollary 8 and the definition after
Corollary 10.  Quantification avoids choosing any of these 2-adic limits as a
global constant.

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
For every integer `A` and `e≥2`, shifting each `i∈S_e` by `A*2^e` leaves
their product unchanged modulo `2^(3e-1)`.  Products and the congruence are in
`ℤ`, permitting negative `A` and avoiding natural subtraction.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Theorem 16.
-/
public theorem_wanted oddSet_product_linear_shift_congr
    (A : ℤ) (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (3 * e - 1) ∣
      (∏ i ∈ oddBelowTwoPow e, (A * (2 : ℤ) ^ e + (i : ℤ))) -
        ∏ i ∈ oddBelowTwoPow e, (i : ℤ)

/--
For integers `A,B`, natural `j`, and `e≥2`, the `2^j` powers of the two shifted
products over `S_e` agree modulo `2^(3e-1+j)`.  The exponentiation applies to
each factor as printed, and integer products allow arbitrary signs of `A,B`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 17.
-/
public theorem_wanted oddSet_product_power_shift_congr
    (A B : ℤ) (j e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (3 * e - 1 + j) ∣
      (∏ i ∈ oddBelowTwoPow e, (A * (2 : ℤ) ^ e + (i : ℤ)) ^ (2 ^ j)) -
        ∏ i ∈ oddBelowTwoPow e, (B * (2 : ℤ) ^ e + (i : ℤ)) ^ (2 ^ j)

/--
For `e≥2`, the reversed elementary symmetric function `σ̂_1(S_e)` is
congruent to `2^(2e-2)` modulo `2^(2e-1)`.  `S_e` is cast to an integer
multiset and congruence is integer divisibility, so all subtractions are exact.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 18.
-/
public theorem_wanted reverseESymm_one_oddSet_congr (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (2 * e - 1) ∣
      reverseESymm 1 (integerMultiset (oddBelowTwoPow e)) - (2 : ℤ) ^ (2 * e - 2)

/--
For `e≥2`, the reversed elementary symmetric function `σ̂_2(S_e)` is
congruent to `2^(e-2)` modulo `2^(e-1)`.  As in Lemma 18, the multiset and
congruence are taken in `ℤ` rather than relying on truncated natural subtraction.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 19.
-/
public theorem_wanted reverseESymm_two_oddSet_congr (e : ℕ) (he : 2 ≤ e) :
    (2 : ℤ) ^ (e - 1) ∣
      reverseESymm 2 (integerMultiset (oddBelowTwoPow e)) - (2 : ℤ) ^ (e - 2)

/--
For `e≥3`, every `v<2^e` with `v≡1 (mod 8)` has exactly four preimages among
`i∈S_e` under `i↦i^2 mod 2^e`.  The cardinality of the explicitly filtered
finite set formalizes “occurs exactly four times”; the paper's count of
`2^(e-3)` possible values is represented by the quantified range of `v`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 20.
-/
public theorem_wanted square_mod_twoPower_fiber_card
    (e : ℕ) (he : 3 ≤ e) (v : ℕ) (hv : v < 2 ^ e) (hv8 : v % 8 = 1) :
    ({i ∈ oddBelowTwoPow e | i ^ 2 % 2 ^ e = v}).card = 4

/--
For `e≥3`, `σ̂_1` of the multiset with four copies of each number below `2^e`
congruent to `1 mod 8` is congruent to `2^(e-1)` modulo `2^e`.  The displayed
sequence `{1,9,...,2^e-7}` is represented by `oneModEightBelowTwoPow e`, and four copies
by multiset scalar multiplication.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Lemma 21.
-/
public theorem_wanted reverseESymm_fourCopies_oneModEight_congr
    (e : ℕ) (he : 3 ≤ e) :
    (2 : ℤ) ^ e ∣
      reverseESymm 1 (fourCopiesOneModEightBelowTwoPow e) - (2 : ℤ) ^ (e - 1)

/--
For `e≥1`, summing the squares of the products over `S_e\{i}` is congruent to
`2^(e-1)` modulo `2^e`.  Each erased product squared equals the paper's
`((2^e-1)!!)^2/i^2`; this equivalent exact-product form avoids adding an
integer exact-division side condition for every summand.

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
