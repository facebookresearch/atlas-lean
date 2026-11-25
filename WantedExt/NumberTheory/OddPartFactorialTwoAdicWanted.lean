/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import MathlibExt.NumberTheory.OddPartFactorialTwoAdic

/-!
# Statements on the odd part of dyadic factorials

Congruences in `ℤ` and `ℕ` are represented by divisibility of an integer difference, while
congruences in `ℤ_[2]` are represented by divisibility by a power of `2`.
-/

namespace MetaMathlibExt

@[expose] public section

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
number $e \ge 3$, where $\operatorname{od}(n)$ is the odd part of $n$.

The congruences start at $e = 3$: the one for $e = 2$, $z \equiv 1 \pmod 4$, contradicts the
one for $e = 3$, $z \equiv 3 \pmod 8$.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Corollary 8.
-/
public theorem_wanted exists_twoAdic_oddPart_factorial_limit :
    ∃ z : ℤ_[2], ∀ e : ℕ, 3 ≤ e →
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
for every $e \ge 3$ and $w \equiv \lfloor ((2^e-1)!! - 1)/2^e \rfloor \pmod{2^{e-1}}$ for every
$e \ge 3$. Then for every $e \ge 3$,
$$\lfloor (\mathrm{od}((2^e)!) - \mathrm{od}((2^{e-1})!))/2^e \rfloor \equiv zw \pmod{2^{e-1}}.$$

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Theorem 12.
-/
public theorem_wanted oddPart_factorial_difference_congr_product
    (z w : ℤ_[2])
    (hz : ∀ e : ℕ, 3 ≤ e →
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
numbers $d < e$, $z \equiv \operatorname{od}((2^{e-1})!) \pmod{2^e}$ for all $e \ge 3$, and
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
    (hz : ∀ e : ℕ, 3 ≤ e →
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
