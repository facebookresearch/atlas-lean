/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

/-!
# Congruences for `spt2‾(n)` (statements)

Statement-only targets from Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62.
`spt2‾(n)` is the number of smallest parts in the overpartitions of `n` whose smallest part is even
and not overlined, counted over the repo's `Nat.Overpartition`. The q-series dissections are
stated with `f_k = (q^k;q^k)_∞ = qPochhammerInfRaw (q^k) (q^k)` for complex `‖q‖ < 1`, with
Ramanujan's `ψ(q) = f_2^2/f_1`, `ψ(-q) = f_1 f_4/f_2`, `φ(-q) = f_1^2/f_2` substituted.
-/

namespace MetaMathlibExt

open QPochhammer

@[expose] public section

/-- **Smallest-even-part contribution of an overpartition.** For an overpartition $O$ of $n$,
let $s$ be the smallest part of $O$. The contribution of $O$ is the number of copies of $s$ in
$O$ if $s$ is even and not overlined, and $0$ otherwise; the empty overpartition, which has no
smallest part, contributes $0$.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Section 1 (definition of `spt2‾(n)`). -/
public def overpartitionSpt2Contribution {n : ℕ} (O : Nat.Overpartition n) : ℕ :=
  if h : O.toPartition.parts.toFinset.Nonempty then
    let s := O.toPartition.parts.toFinset.min' h
    if Even s ∧ s ∉ O.overlines then O.toPartition.parts.count s else 0
  else
    0

/-- **Number of smallest even parts in overpartitions.** For a natural number $n$,
$\overline{\mathrm{spt2}}(n)$ is the number of smallest parts in the overpartitions of $n$ whose
smallest part is even and not overlined: the sum, over all overpartitions $O$ of $n$, of the
smallest-even-part contribution of $O$, which is the number of copies of the smallest part $s$
of $O$ when $s$ is even and not overlined, and $0$ otherwise (in particular when $O$ is empty).
For example $\overline{\mathrm{spt2}}(4) = 3$, from $4$ and $2 + 2$, while $\overline{2} + 2$
does not count; the values for $n = 0, \dots, 8$ are $0, 0, 1, 0, 3, 2, 6, 6, 15$.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Section 1. -/
public def overpartitionSpt2 (n : ℕ) : ℕ :=
  ∑ O : Nat.Overpartition n, overpartitionSpt2Contribution O

/-- **$\overline{\mathrm{spt2}}$ vanishes at zero.** Let $\overline{\mathrm{spt2}}(n)$ be the
number of smallest parts in the overpartitions of $n$ whose smallest part is even and not
overlined. Then $\overline{\mathrm{spt2}}(0) = 0$: the only overpartition of $0$ is empty and has
no smallest part.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Section 1. -/
public theorem overpartitionSpt2_zero : overpartitionSpt2 0 = 0 := by
  refine Finset.sum_eq_zero fun O _ => ?_
  have h : O.toPartition.parts = 0 := by
    have := O.toPartition.parts_sum
    exact Multiset.eq_zero_of_forall_notMem fun a ha =>
      absurd (Multiset.le_sum_of_mem ha) (by have := O.toPartition.parts_pos ha; omega)
  simp [overpartitionSpt2Contribution]

/-- **Overpartitions with odd smallest part contribute nothing.** If $O$ is an overpartition of
$n$ with at least one part and the smallest part of $O$ is odd, then the smallest-even-part
contribution of $O$ is $0$.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Section 1. -/
public theorem overpartitionSpt2Contribution_eq_zero_of_odd {n : ℕ} (O : Nat.Overpartition n)
    (h : O.toPartition.parts.toFinset.Nonempty)
    (hodd : Odd (O.toPartition.parts.toFinset.min' h)) :
    overpartitionSpt2Contribution O = 0 := by
  simp [overpartitionSpt2Contribution, h, Nat.not_even_iff_odd.mpr hodd]

/--
**Three congruences modulo 4 for $\overline{\mathrm{spt2}}$.** Let $\overline{\mathrm{spt2}}(n)$
be the number of smallest parts in the overpartitions of $n$ whose smallest part is even and not
overlined. For every natural number $n$, each of $\overline{\mathrm{spt2}}(36n + 30)$,
$\overline{\mathrm{spt2}}(48n + 34)$ and $\overline{\mathrm{spt2}}(72n + 42)$ is divisible by $4$.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Theorem 1.
-/
public theorem_wanted overpartitionSpt2_basic_congruences (n : ℕ) :
    overpartitionSpt2 (36 * n + 30) % 4 = 0 ∧
      overpartitionSpt2 (48 * n + 34) % 4 = 0 ∧
      overpartitionSpt2 (72 * n + 42) % 4 = 0

/--
**Congruences modulo 4 for $\overline{\mathrm{spt2}}$ along powers of 2.** Let
$\overline{\mathrm{spt2}}(N)$ be the number of smallest parts in the overpartitions of $N$ whose
smallest part is even and not overlined. For all natural numbers $j$ and $n$,
$\overline{\mathrm{spt2}}(N)$ is divisible by $4$ for each of the six values
$N = 2^{j+4} n + 7 \cdot 2^{j+1}$, $N = 2^{j+2} \cdot 9 n + 15 \cdot 2^{j+1}$,
$N = 2^{j+4} \cdot 3 n + 17 \cdot 2^{j+1}$, $N = 2^{j+3} \cdot 9 n + 21 \cdot 2^{j+1}$,
$N = 2^{j+4} \cdot 5 n + 17 \cdot 2^{j+1}$ and $N = 2^{j+4} \cdot 5 n + 33 \cdot 2^{j+1}$.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Theorem 2.
-/
public theorem_wanted overpartitionSpt2_dyadic_congruences (j n : ℕ) :
    overpartitionSpt2 (2 ^ (j + 4) * n + 7 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 2) * 9 * n + 15 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 4) * 3 * n + 17 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 3) * 9 * n + 21 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 4) * 5 * n + 17 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 4) * 5 * n + 33 * 2 ^ (j + 1)) % 4 = 0

/--
**Congruences modulo 4 for $\overline{\mathrm{spt2}}$ at primes $p \equiv 5, 7 \pmod 8$.** Let
$\overline{\mathrm{spt2}}(N)$ be the number of smallest parts in the overpartitions of $N$ whose
smallest part is even and not overlined. Let $p > 3$ be a prime with $p \equiv 5 \pmod 8$ or
$p \equiv 7 \pmod 8$. Then for all natural numbers $k$ and $m$ with $p \nmid m$, the number
$\overline{\mathrm{spt2}}(32 p^{2k+1} m + 24 p^{2k+2})$ is divisible by $4$.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Theorem 3.
-/
public theorem_wanted overpartitionSpt2_prime_congruence
    (p k m : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p)
    (hp8 : p % 8 = 5 ∨ p % 8 = 7) (hm : ¬p ∣ m) :
    overpartitionSpt2 (32 * p ^ (2 * k + 1) * m + 24 * p ^ (2 * k + 2)) % 4 = 0

/--
**2-dissection of the square of Euler's product.** Let $q$ be a complex number with $|q| < 1$,
and for $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{n=0}^{\infty} (1 - q^k (q^k)^n)$ be the
raw infinite q-Pochhammer product. Then
$$f_1^2 = \frac{f_2 f_8^5}{f_4^2 f_{16}^2} - 2q \frac{f_2 f_{16}^2}{f_8}.$$

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 1.
-/
public theorem_wanted qPochhammer_two_dissection_square (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q ^ 2 =
      qPochhammerInfRaw (q ^ 2) (q ^ 2) *
          qPochhammerInfRaw (q ^ 8) (q ^ 8) ^ 5 /
        (qPochhammerInfRaw (q ^ 4) (q ^ 4) ^ 2 *
          qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2) -
      2 * q * qPochhammerInfRaw (q ^ 2) (q ^ 2) *
          qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2 /
        qPochhammerInfRaw (q ^ 8) (q ^ 8)

/--
**2-dissection of the reciprocal square of Euler's product.** Let $q$ be a complex number with
$|q| < 1$, and for $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{n=0}^{\infty} (1 - q^k (q^k)^n)$
be the raw infinite q-Pochhammer product. Then
$$\frac{1}{f_1^2} = \frac{f_8^5}{f_2^5 f_{16}^2} + 2q \frac{f_4^2 f_{16}^2}{f_2^5 f_8}.$$

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 1.
-/
public theorem_wanted qPochhammer_two_dissection_inverse_square (q : ℂ) (hq : ‖q‖ < 1) :
    1 / qPochhammerInfRaw q q ^ 2 =
      qPochhammerInfRaw (q ^ 8) (q ^ 8) ^ 5 /
          (qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 5 *
            qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2) +
        2 * q * qPochhammerInfRaw (q ^ 4) (q ^ 4) ^ 2 *
            qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2 /
          (qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 5 *
            qPochhammerInfRaw (q ^ 8) (q ^ 8))

/--
**The 3-dissection of $f_1^3$ for complex $q$.** Let $q$ be a complex number with $|q| < 1$, and
for $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{m \ge 1} (1 - q^{km})$ be the raw infinite
q-Pochhammer product with $a = q^k$ and base $q^k$. Then

$$
f_1^3 = \frac{f_6 f_9^6}{f_3 f_{18}^3} + 4 q^3 \frac{f_3^2 f_{18}^6}{f_6^2 f_9^3} - 3 q f_9^3.
$$

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 2.
-/
public theorem_wanted qPochhammer_three_dissection_cube (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q ^ 3 =
      qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 6 /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 3) +
      4 * q ^ 3 * qPochhammerInfRaw (q ^ 3) (q ^ 3) ^ 2 *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 6 /
        (qPochhammerInfRaw (q ^ 6) (q ^ 6) ^ 2 *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 3) -
      3 * q * qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 3

/--
**The 3-dissection of $f_4/f_1$ for complex $q$.** Let $q$ be a complex number with $|q| < 1$,
and for $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{m \ge 1} (1 - q^{km})$ be the raw
infinite q-Pochhammer product with $a = q^k$ and base $q^k$. Then

$$
\frac{f_4}{f_1} = \frac{f_{12} f_{18}^4}{f_3^3 f_{36}^2} +
q \frac{f_6^2 f_9^3 f_{36}}{f_3^4 f_{18}^2} + 2 q^2 \frac{f_6 f_{18} f_{36}}{f_3^3}.
$$

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 2.
-/
public theorem_wanted qPochhammer_three_dissection_ratio_four_one (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw (q ^ 4) (q ^ 4) / qPochhammerInfRaw q q =
      qPochhammerInfRaw (q ^ 12) (q ^ 12) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 4 /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) ^ 3 *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) ^ 2) +
      q * qPochhammerInfRaw (q ^ 6) (q ^ 6) ^ 2 *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 3 *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) ^ 4 *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2) +
      2 * q ^ 2 * qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) /
        qPochhammerInfRaw (q ^ 3) (q ^ 3) ^ 3

/--
**The 3-dissection of $f_1 f_2$ for complex $q$.** Let $q$ be a complex number with $|q| < 1$,
and for $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{m \ge 1} (1 - q^{km})$ be the raw
infinite q-Pochhammer product with $a = q^k$ and base $q^k$. Then

$$
f_1 f_2 = \frac{f_6 f_9^4}{f_3 f_{18}^2} - q f_9 f_{18} - 2 q^2 \frac{f_3 f_{18}^4}{f_6 f_9^2}.
$$

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 2.
-/
public theorem_wanted qPochhammer_three_dissection_product_one_two (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 2) (q ^ 2) =
      qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 4 /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2) -
      q * qPochhammerInfRaw (q ^ 9) (q ^ 9) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) -
      2 * q ^ 2 * qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 4 /
        (qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2)

/--
**3-dissection of the product form of Ramanujan's psi function.** Let $q$ be a complex number
with $|q| < 1$, and for $k \ge 1$ let
$f_k = (q^k; q^k)_\infty = \prod_{n=0}^{\infty} (1 - q^k (q^k)^n)$ be the raw infinite
q-Pochhammer product. Then
$$\frac{f_2^2}{f_1} = \frac{f_6 f_9^2}{f_3 f_{18}} + q \frac{f_{18}^2}{f_9}.$$

Here $f_2^2/f_1$ is the product form of Ramanujan's theta function
$\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 3.
-/
public theorem_wanted ramanujanPsi_three_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 2 / qPochhammerInfRaw q q =
      qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2 /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18)) +
      q * qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2 /
        qPochhammerInfRaw (q ^ 9) (q ^ 9)

/--
**3-dissection of the product form of Ramanujan's psi function at negated argument.** Let $q$ be
a complex number with $|q| < 1$, and for $k \ge 1$ let
$f_k = (q^k; q^k)_\infty = \prod_{n=0}^{\infty} (1 - q^k (q^k)^n)$ be the raw infinite
q-Pochhammer product. Then
$$\frac{f_1 f_4}{f_2} = \frac{f_3 f_{12} f_{18}^5}{f_6^2 f_9^2 f_{36}^2} -
q \frac{f_9 f_{36}}{f_{18}}.$$

Here $f_1 f_4/f_2$ is the product form of $\psi(-q)$, where
$\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$ is Ramanujan's theta function.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 4.
-/
public theorem_wanted ramanujanPsi_neg_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 4) (q ^ 4) /
        qPochhammerInfRaw (q ^ 2) (q ^ 2) =
      qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 12) (q ^ 12) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 5 /
        (qPochhammerInfRaw (q ^ 6) (q ^ 6) ^ 2 *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2 *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) ^ 2) -
      q * qPochhammerInfRaw (q ^ 9) (q ^ 9) *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) /
        qPochhammerInfRaw (q ^ 18) (q ^ 18)

/--
**3-dissection of the product form of Ramanujan's phi function at negated argument.** Let $q$ be
a complex number with $|q| < 1$, and for $k \ge 1$ let
$f_k = (q^k; q^k)_\infty = \prod_{n=0}^{\infty} (1 - q^k (q^k)^n)$ be the raw infinite
q-Pochhammer product. Then
$$\frac{f_1^2}{f_2} = \frac{f_9^2}{f_{18}} - 2q \frac{f_3 f_{18}^2}{f_6 f_9}.$$

Here $f_1^2/f_2$ is the product form of $\varphi(-q)$, where
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ is Ramanujan's theta function.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 5.
-/
public theorem_wanted ramanujanPhi_neg_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q ^ 2 / qPochhammerInfRaw (q ^ 2) (q ^ 2) =
      qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2 /
          qPochhammerInfRaw (q ^ 18) (q ^ 18) -
        2 * q * qPochhammerInfRaw (q ^ 3) (q ^ 3) *
            qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2 /
          (qPochhammerInfRaw (q ^ 6) (q ^ 6) *
            qPochhammerInfRaw (q ^ 9) (q ^ 9))

end

end MetaMathlibExt
