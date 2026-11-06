/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import Mathlib.Data.Nat.ModEq

/-!
# Congruences for POND and PEND partitions

Statements from James A. Sellers, *Elementary Proofs of Congruences for POND and PEND
Partitions*, Journal of Integer Sequences 27 (2024), Article 24.4.7 (arXiv:2308.09999).

A POND partition is an integer partition in which the odd parts cannot be distinct: every
odd part that occurs has multiplicity at least `2`; even parts are unrestricted. A PEND
partition is defined in the same way with the roles of odd and even parts exchanged.
The paper's shorthand `f_k = (q^k; q^k)_∞ = ∏_{m ≥ 1} (1 - q^{k m})` is `qEulerProduct k`,
written `𝔣 k` below. Quotients of `f_k` in the paper are stated with denominators cleared.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **The POND condition.** A multiset $s$ of natural numbers (the parts of a partition)
satisfies the POND condition when no odd number occurs in $s$ exactly once; equivalently,
every odd part that occurs in $s$ has multiplicity at least $2$, so the odd parts are not
distinct.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
def IsPondParts (s : Multiset ℕ) : Prop :=
  ∀ i ∈ s, Odd i → s.count i ≠ 1

/-- **The PEND condition.** A multiset $s$ of natural numbers (the parts of a partition)
satisfies the PEND condition when no even number occurs in $s$ exactly once; equivalently,
every even part that occurs in $s$ has multiplicity at least $2$, so the even parts are not
distinct.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
def IsPendParts (s : Multiset ℕ) : Prop :=
  ∀ i ∈ s, Even i → s.count i ≠ 1

instance : DecidablePred IsPondParts := fun s => by unfold IsPondParts; infer_instance

instance : DecidablePred IsPendParts := fun s => by unfold IsPendParts; infer_instance

/-- **Number of POND partitions.** For a natural number $n$, $\mathrm{pond}(n)$ is the number of
partitions of $n$ that are POND, that is, in which every odd part that occurs has multiplicity
at least $2$ (OEIS A265256).

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
def pondCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter fun p => IsPondParts p.parts).card

/-- **The PEND partition function.** For a natural number $n$, $\mathrm{pend}(n)$ is the number
of PEND partitions of $n$: partitions of $n$ in which every even part that occurs appears at
least twice (OEIS A265254).

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
def pendCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter fun p => IsPendParts p.parts).card

local notation "𝔣" => qEulerProduct

/-- **The number of POND partitions of zero.** The number $\mathrm{pond}(0)$ of POND
partitions of $0$ equals $1$: the only partition of $0$ is the empty partition, and it is POND.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1 (OEIS A265256). -/
theorem pondCount_zero : pondCount 0 = 1 := by
  decide

/-- **PEND partitions of zero.** The number of PEND partitions of $0$ is $1$, that is,
$\mathrm{pend}(0) = 1$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1 (OEIS A265254). -/
theorem pendCount_zero : pendCount 0 = 1 := by
  decide

/-- **Examples of POND and PEND parts.** The multisets of parts $\{1, 1\}$ and $\{2\}$ satisfy
the POND condition, while $\{1\}$ and $\{2, 1\}$ do not; the multisets $\{1\}$ and $\{2, 2\}$
satisfy the PEND condition, while $\{2\}$ and $\{2, 4\}$ do not.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
theorem isPondParts_isPendParts_examples :
    IsPondParts {1, 1} ∧ ¬ IsPondParts {1} ∧ ¬ IsPondParts {2, 1} ∧ IsPondParts {2} ∧
      IsPendParts {1} ∧ IsPendParts {2, 2} ∧ ¬ IsPendParts {2} ∧ ¬ IsPendParts {2, 4} := by
  decide

/-- **Congruences modulo 2, 3 and 4 for POND partitions.** Let $\mathrm{pond}(m)$ be the number
of POND partitions of $m$. For every natural number $n$, $\mathrm{pond}(3n + 2) \equiv 0 \pmod{2}$,
$\mathrm{pond}(27n + 26) \equiv 0 \pmod{3}$ and $\mathrm{pond}(3n + 1) \equiv 0 \pmod{4}$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 1 (`jis-2024-24.4.7-thm-1`). -/
public theorem_wanted pondCount_congruences (n : ℕ) :
    pondCount (3 * n + 2) ≡ 0 [MOD 2] ∧ pondCount (27 * n + 26) ≡ 0 [MOD 3] ∧
      pondCount (3 * n + 1) ≡ 0 [MOD 4]

/-- **Congruence modulo 3 for PEND partitions of 27n + 19.** Let $\mathrm{pend}(m)$ be the
number of PEND partitions of $m$. For every natural number $n$,
$\mathrm{pend}(27n + 19) \equiv 0 \pmod{3}$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 2 (`jis-2024-24.4.7-thm-2`). -/
public theorem_wanted pendCount_twentySeven_mul_add_nineteen (n : ℕ) :
    pendCount (27 * n + 19) ≡ 0 [MOD 3]

/-- **Internal congruence modulo 3 for POND partitions.** Let $\mathrm{pond}(m)$ be the number
of POND partitions of $m$. For every natural number $n$,
$\mathrm{pond}(27n + 17) \equiv \mathrm{pond}(3n + 2) \pmod{3}$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 3 (`jis-2024-24.4.7-thm-3`). -/
public theorem_wanted pondCount_internal_congruence (n : ℕ) :
    pondCount (27 * n + 17) ≡ pondCount (3 * n + 2) [MOD 3]

/-- **Internal congruence modulo 3 for PEND partitions.** Let $\mathrm{pend}(m)$ be the number
of PEND partitions of $m$. For every natural number $n$,
$\mathrm{pend}(27n + 10) \equiv \mathrm{pend}(3n + 1) \pmod{3}$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 4 (`jis-2024-24.4.7-thm-4`). -/
public theorem_wanted pendCount_internal_congruence (n : ℕ) :
    pendCount (27 * n + 10) ≡ pendCount (3 * n + 1) [MOD 3]

/-- **Infinite family of congruences modulo 3 for POND partitions.** Let $\mathrm{pond}(m)$ be
the number of POND partitions of $m$. For all natural numbers $\alpha \ge 1$ and $n$,
$\mathrm{pond}\left(3^{2\alpha+1} n + (23 \cdot 3^{2\alpha} + 1)/8\right) \equiv 0 \pmod{3}$.

The division by $8$ is exact, since $3^{2\alpha} \equiv 1 \pmod{8}$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 5 (`jis-2024-24.4.7-thm-5`). -/
public theorem_wanted pondCount_infinite_family (α n : ℕ) (hα : 1 ≤ α) :
    pondCount (3 ^ (2 * α + 1) * n + (23 * 3 ^ (2 * α) + 1) / 8) ≡ 0 [MOD 3]

/-- **Infinite family of congruences modulo 3 for PEND partitions.** Let $\mathrm{pend}(m)$ be
the number of PEND partitions of $m$. For all natural numbers $\alpha \ge 1$ and $n$,
$\mathrm{pend}\left(3^{2\alpha+1} n + (17 \cdot 3^{2\alpha} - 1)/8\right) \equiv 0 \pmod{3}$.

The division by $8$ is exact, since $3^{2\alpha} \equiv 1 \pmod{8}$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 6 (`jis-2024-24.4.7-thm-6`). -/
public theorem_wanted pendCount_infinite_family (α n : ℕ) (hα : 1 ≤ α) :
    pendCount (3 ^ (2 * α + 1) * n + (17 * 3 ^ (2 * α) - 1) / 8) ≡ 0 [MOD 3]

/-- **3-dissection of $f_2 / (f_1 f_4)$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the
Euler products in $\mathbb{Z}[[q]]$. Then
$f_2 f_3^4 f_9^3 f_{12}^4 f_{18}^3 f_{36}^3 = f_1 f_3^2 f_4 f_{12}^2 f_{18}^{12} +
q f_1 f_3 f_4 f_6^2 f_9^3 f_{12} f_{18}^6 f_{36}^3 + q^2 f_1 f_4 f_6^4 f_9^6 f_{36}^6$.

Since each $f_k$ with $k \ge 1$ has constant term $1$, dividing both sides by
$f_1 f_3^4 f_4 f_9^3 f_{12}^4 f_{18}^3 f_{36}^3$ shows that this is equivalent to
$f_2 / (f_1 f_4) = f_{18}^9 / (f_3^2 f_9^3 f_{12}^2 f_{36}^3) +
q f_6^2 f_{18}^3 / (f_3^3 f_{12}^3) + q^2 f_6^4 f_9^3 f_{36}^3 / (f_3^4 f_{12}^4 f_{18}^3)$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 7 (`jis-2024-24.4.7-lem-7`). -/
public theorem_wanted f2_div_f1_f4_dissection :
    𝔣 2 * 𝔣 3 ^ 4 * 𝔣 9 ^ 3 * 𝔣 12 ^ 4 * 𝔣 18 ^ 3 * 𝔣 36 ^ 3 =
      𝔣 1 * 𝔣 3 ^ 2 * 𝔣 4 * 𝔣 12 ^ 2 * 𝔣 18 ^ 12
      + X * 𝔣 1 * 𝔣 3 * 𝔣 4 * 𝔣 6 ^ 2 * 𝔣 9 ^ 3 * 𝔣 12 * 𝔣 18 ^ 6 * 𝔣 36 ^ 3
      + X ^ 2 * 𝔣 1 * 𝔣 4 * 𝔣 6 ^ 4 * 𝔣 9 ^ 6 * 𝔣 36 ^ 6

/-- **3-dissection of $f_1 f_2$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the Euler
products in $\mathbb{Z}[[q]]$. Then
$f_1 f_2 f_3 f_6 f_9^2 f_{18}^2 = f_6^2 f_9^6 - q f_3 f_6 f_9^3 f_{18}^3 -
2 q^2 f_3^2 f_{18}^6$.

Since each $f_k$ with $k \ge 1$ has constant term $1$, dividing both sides by
$f_3 f_6 f_9^2 f_{18}^2$ shows that this is equivalent to
$f_1 f_2 = f_6 f_9^4 / (f_3 f_{18}^2) - q f_9 f_{18} - 2 q^2 f_3 f_{18}^4 / (f_6 f_9^2)$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 8 (`jis-2024-24.4.7-lem-8`). -/
public theorem_wanted f1_f2_dissection :
    𝔣 1 * 𝔣 2 * 𝔣 3 * 𝔣 6 * 𝔣 9 ^ 2 * 𝔣 18 ^ 2 =
      𝔣 6 ^ 2 * 𝔣 9 ^ 6
      - X * 𝔣 3 * 𝔣 6 * 𝔣 9 ^ 3 * 𝔣 18 ^ 3
      - 2 * X ^ 2 * 𝔣 3 ^ 2 * 𝔣 18 ^ 6

/-- **3-dissection of $1 / (f_1 f_2)$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the
Euler products in $\mathbb{Z}[[q]]$. Then
$f_3^6 f_6^6 f_9^3 f_{18}^3 = f_1 f_2 f_6^4 f_9^{12} + q f_1 f_2 f_3 f_6^3 f_9^9 f_{18}^3 +
3 q^2 f_1 f_2 f_3^2 f_6^2 f_9^6 f_{18}^6 - 2 q^3 f_1 f_2 f_3^3 f_6 f_9^3 f_{18}^9 +
4 q^4 f_1 f_2 f_3^4 f_{18}^{12}$.

Since each $f_k$ with $k \ge 1$ has constant term $1$, dividing both sides by
$f_1 f_2 f_3^6 f_6^6 f_9^3 f_{18}^3$ shows that this is equivalent to
$1 / (f_1 f_2) = f_9^9 / (f_3^6 f_6^2 f_{18}^3) + q f_9^6 / (f_3^5 f_6^3) +
3 q^2 f_9^3 f_{18}^3 / (f_3^4 f_6^4) - 2 q^3 f_{18}^6 / (f_3^3 f_6^5) +
4 q^4 f_{18}^9 / (f_3^2 f_6^6 f_9^3)$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 9 (`jis-2024-24.4.7-lem-9`). -/
public theorem_wanted one_div_f1_f2_dissection :
    𝔣 3 ^ 6 * 𝔣 6 ^ 6 * 𝔣 9 ^ 3 * 𝔣 18 ^ 3 =
      𝔣 1 * 𝔣 2 * 𝔣 6 ^ 4 * 𝔣 9 ^ 12
      + X * 𝔣 1 * 𝔣 2 * 𝔣 3 * 𝔣 6 ^ 3 * 𝔣 9 ^ 9 * 𝔣 18 ^ 3
      + 3 * X ^ 2 * 𝔣 1 * 𝔣 2 * 𝔣 3 ^ 2 * 𝔣 6 ^ 2 * 𝔣 9 ^ 6 * 𝔣 18 ^ 6
      - 2 * X ^ 3 * 𝔣 1 * 𝔣 2 * 𝔣 3 ^ 3 * 𝔣 6 * 𝔣 9 ^ 3 * 𝔣 18 ^ 9
      + 4 * X ^ 4 * 𝔣 1 * 𝔣 2 * 𝔣 3 ^ 4 * 𝔣 18 ^ 12

/-- **3-dissection of $f_2^2 / f_1$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the
Euler products in $\mathbb{Z}[[q]]$. Then
$f_2^2 f_3 f_9 f_{18} = f_1 f_6 f_9^3 + q f_1 f_3 f_{18}^3$.

Since each $f_k$ with $k \ge 1$ has constant term $1$, dividing both sides by
$f_1 f_3 f_9 f_{18}$ shows that this is equivalent to
$f_2^2 / f_1 = f_6 f_9^2 / (f_3 f_{18}) + q f_{18}^2 / f_9$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 10 (`jis-2024-24.4.7-lem-10`). -/
public theorem_wanted f2_sq_div_f1_dissection :
    𝔣 2 ^ 2 * 𝔣 3 * 𝔣 9 * 𝔣 18 =
      𝔣 1 * 𝔣 6 * 𝔣 9 ^ 3
      + X * 𝔣 1 * 𝔣 3 * 𝔣 18 ^ 3

/-- **3-dissection of $f_2 / f_1^2$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the
Euler products in $\mathbb{Z}[[q]]$. Then
$f_2 f_3^8 f_{18}^3 = f_1^2 f_6^4 f_9^6 + 2 q f_1^2 f_3 f_6^3 f_9^3 f_{18}^3 +
4 q^2 f_1^2 f_3^2 f_6^2 f_{18}^6$.

Since each $f_k$ with $k \ge 1$ has constant term $1$, dividing both sides by
$f_1^2 f_3^8 f_{18}^3$ shows that this is equivalent to
$f_2 / f_1^2 = f_6^4 f_9^6 / (f_3^8 f_{18}^3) + 2 q f_6^3 f_9^3 / f_3^7 +
4 q^2 f_6^2 f_{18}^3 / f_3^6$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 11 (`jis-2024-24.4.7-lem-11`). -/
public theorem_wanted f2_div_f1_sq_dissection :
    𝔣 2 * 𝔣 3 ^ 8 * 𝔣 18 ^ 3 =
      𝔣 1 ^ 2 * 𝔣 6 ^ 4 * 𝔣 9 ^ 6
      + 2 * X * 𝔣 1 ^ 2 * 𝔣 3 * 𝔣 6 ^ 3 * 𝔣 9 ^ 3 * 𝔣 18 ^ 3
      + 4 * X ^ 2 * 𝔣 1 ^ 2 * 𝔣 3 ^ 2 * 𝔣 6 ^ 2 * 𝔣 18 ^ 6

/-- **3-dissection of $f_4 / f_1$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the
Euler products in $\mathbb{Z}[[q]]$. Then
$f_3^4 f_4 f_{18}^2 f_{36}^2 = f_1 f_3 f_{12} f_{18}^6 + q f_1 f_6^2 f_9^3 f_{36}^3 +
2 q^2 f_1 f_3 f_6 f_{18}^3 f_{36}^3$.

Since each $f_k$ with $k \ge 1$ has constant term $1$, dividing both sides by
$f_1 f_3^4 f_{18}^2 f_{36}^2$ shows that this is equivalent to
$f_4 / f_1 = f_{12} f_{18}^4 / (f_3^3 f_{36}^2) + q f_6^2 f_9^3 f_{36} / (f_3^4 f_{18}^2) +
2 q^2 f_6 f_{18} f_{36} / f_3^3$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 13 (`jis-2024-24.4.7-lem-13`). -/
public theorem_wanted f4_div_f1_dissection :
    𝔣 3 ^ 4 * 𝔣 4 * 𝔣 18 ^ 2 * 𝔣 36 ^ 2 =
      𝔣 1 * 𝔣 3 * 𝔣 12 * 𝔣 18 ^ 6
      + X * 𝔣 1 * 𝔣 6 ^ 2 * 𝔣 9 ^ 3 * 𝔣 36 ^ 3
      + 2 * X ^ 2 * 𝔣 1 * 𝔣 3 * 𝔣 6 * 𝔣 18 ^ 3 * 𝔣 36 ^ 3

/-- **2-dissection of $f_3^3 / f_1$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the
Euler products in $\mathbb{Z}[[q]]$. Then
$f_2^2 f_3^3 f_4 f_{12} - q f_1 f_2^2 f_{12}^4 = f_1 f_4^4 f_6^2$.

Since each $f_k$ with $k \ge 1$ has constant term $1$, dividing both sides by
$f_1 f_2^2 f_4 f_{12}$ shows that this is equivalent to
$f_3^3 / f_1 - q f_{12}^3 / f_4 = f_4^3 f_6^2 / (f_2^2 f_{12})$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 15 (`jis-2024-24.4.7-lem-15`). -/
public theorem_wanted f3_cube_div_f1_sub :
    𝔣 2 ^ 2 * 𝔣 3 ^ 3 * 𝔣 4 * 𝔣 12
      - X * 𝔣 1 * 𝔣 2 ^ 2 * 𝔣 12 ^ 4 =
      𝔣 1 * 𝔣 4 ^ 4 * 𝔣 6 ^ 2

/-- **Prime-power congruence for powers of Euler products.** Let $p$ be a prime, let
$j, k, m \ge 1$ be natural numbers, and let $f_m = \prod_{i \ge 1} (1 - q^{mi})$. Then for every
natural number $n$, the coefficient of $q^n$ in $f_m^{p^j k}$ is congruent modulo $p^j$ to the
coefficient of $q^n$ in $f_{pm}^{p^{j-1} k}$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 16
(`jis-2024-24.4.7-lem-16`). -/
public theorem_wanted qEulerProduct_pow_prime_pow_congruence (p j k m : ℕ) (hp : p.Prime)
    (hj : 1 ≤ j) (hk : 1 ≤ k) (hm : 1 ≤ m) (n : ℕ) :
    coeff n (𝔣 m ^ (p ^ j * k)) ≡ coeff n (𝔣 (p * m) ^ (p ^ (j - 1) * k)) [ZMOD (p : ℤ) ^ j]

/-- **Generating function for POND partitions.** Let $\mathrm{pond}(n)$ be the number of POND
partitions of $n$, and let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Then, as integer power series
in $q$, $f_2^2 f_3 f_{12} \sum_{n \ge 0} \mathrm{pond}(n) q^n = f_4 f_6^2$. This is the identity
$\sum_{n \ge 0} \mathrm{pond}(n) q^n = f_4 f_6^2 / (f_2^2 f_3 f_{12})$ with the denominator
cleared.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 17
(`jis-2024-24.4.7-thm-17`). -/
public theorem_wanted pondCount_generatingFunction :
    𝔣 2 ^ 2 * 𝔣 3 * 𝔣 12 * (PowerSeries.mk fun n => (pondCount n : ℤ)) =
      𝔣 4 * 𝔣 6 ^ 2

/-- **Generating function for PEND partitions.** Let $\mathrm{pend}(n)$ be the number of PEND
partitions of $n$, and let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Then, as integer power series
in $q$, $f_1 f_4 f_6 \sum_{n \ge 0} \mathrm{pend}(n) q^n = f_2 f_{12}$. This is the identity
$\sum_{n \ge 0} \mathrm{pend}(n) q^n = f_2 f_{12} / (f_1 f_4 f_6)$ with the denominator cleared.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 18
(`jis-2024-24.4.7-thm-18`). -/
public theorem_wanted pendCount_generatingFunction :
    𝔣 1 * 𝔣 4 * 𝔣 6 * (PowerSeries.mk fun n => (pendCount n : ℤ)) =
      𝔣 2 * 𝔣 12

end

end MetaMathlibExt
