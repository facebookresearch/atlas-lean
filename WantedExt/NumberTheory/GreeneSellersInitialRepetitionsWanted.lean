/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

namespace MetaMathlibExt

@[expose] public section

/-- **Residues that are squares modulo $2^{2k-1}$ but not modulo $2^{2k}$.** Let $k \ge 0$ and let
$x$ be an integer with $0 \le x < 2^{2k}$, where the exponents $2k - 1$ and $2k - 2$ are truncated
at $0$. Then $x$ is a square modulo $2^{2k-1}$ but not a square modulo $2^{2k}$ if and only if
$x = 2^{2k-1}$ or $x = 2^{2k-1} + 2^{2k-2}$.

For $k \ge 1$ these are exactly two residues; for $k = 0$ both sides of the equivalence are false.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 2
(`integers-2025-A32-lem-2`). -/
public theorem_wanted isSquare_mod_two_pow_odd_not_even_iff (k : ℕ) (x : ℕ)
    (hx : x < 2 ^ (2 * k)) :
    (IsSquare (x : ZMod (2 ^ (2 * k - 1))) ∧ ¬IsSquare (x : ZMod (2 ^ (2 * k)))) ↔
      x = 2 ^ (2 * k - 1) ∨ x = 2 ^ (2 * k - 1) + 2 ^ (2 * k - 2)

/-- **Residues that are squares modulo $2^{2k}$ but not modulo $2^{2k+1}$.** Let $k \ge 0$ and let
$x$ be an integer with $0 \le x < 2^{2k+1}$, where the exponent $2k - 2$ is truncated at $0$. Then
$x$ is a square modulo $2^{2k}$ but not a square modulo $2^{2k+1}$ if and only if
$x = 2^{2k} + 2^{2k-2}$.

For $k \ge 1$ this is the unique such residue; for $k = 0$ both sides of the equivalence are false.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 3
(`integers-2025-A32-lem-3`). -/
public theorem_wanted isSquare_mod_two_pow_even_not_odd_iff (k : ℕ) (x : ℕ)
    (hx : x < 2 ^ (2 * k + 1)) :
    (IsSquare (x : ZMod (2 ^ (2 * k))) ∧ ¬IsSquare (x : ZMod (2 ^ (2 * k + 1)))) ↔
      x = 2 ^ (2 * k) + 2 ^ (2 * k - 2)

open scoped Classical in
/-- **Residues $r$ with $16r + 1$ and $8r + 1$ both non-squares modulo $p$.** For every prime $p$,
the number of integers $r$ with $1 \le r \le p - 1$ such that neither $16r + 1$ nor $8r + 1$ is a
square modulo $p$ equals $\lfloor p/4 \rfloor$.

Here $0$ counts as a square modulo $p$, so "not a square" means "quadratic nonresidue". The paper
assumes $p \ge 5$; for $p = 2$ and $p = 3$ both sides are $0$. If $0$ were counted as a non-square,
the count at $p = 5$ would be $2$ instead of $1$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 5 (`integers-2025-A32-thm-5`). -/
public theorem_wanted card_not_isSquare_sixteen_mul_add_one_eight_mul_add_one (p : ℕ)
    (hp : p.Prime) :
    ((Finset.Icc 1 (p - 1)).filter fun r =>
        ¬IsSquare ((16 * r + 1 : ℕ) : ZMod p) ∧ ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card =
      p / 4

open scoped Classical in
/-- **Residues $r$ with $12r + 1$ and $8r + 1$ both non-squares modulo $p$.** For every prime $p$,
let $N$ be the number of integers $r$ with $1 \le r \le p - 1$ such that neither $12r + 1$ nor
$8r + 1$ is a square modulo $p$. Then $N = \lfloor p/4 \rfloor - 1$ if $p \equiv 5 \pmod{24}$,
$N = \lfloor p/4 \rfloor + 1$ if $p \equiv 11 \pmod{24}$, and $N = \lfloor p/4 \rfloor$ otherwise.

Here $0$ counts as a square modulo $p$, so "not a square" means "quadratic nonresidue". The paper
assumes $p \ge 5$; for $p = 2$ and $p = 3$ both sides are $0$. If $0$ were counted as a non-square,
the count at $p = 5$ would be $2$ instead of $0$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 8 (`integers-2025-A32-thm-8`). -/
public theorem_wanted card_not_isSquare_twelve_mul_add_one_eight_mul_add_one (p : ℕ)
    (hp : p.Prime) :
    ((Finset.Icc 1 (p - 1)).filter fun r =>
        ¬IsSquare ((12 * r + 1 : ℕ) : ZMod p) ∧ ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card =
      if p % 24 = 5 then p / 4 - 1 else if p % 24 = 11 then p / 4 + 1 else p / 4

/-- **Counting $r$ with $mr + 1$ and $nr + 1$ both quadratic nonresidues.** Let $p$ be an odd
prime, write $\left(\frac{a}{p}\right)$ for the Legendre symbol of an integer $a$, and let $m$ and
$n$ be integers with $p \nmid mn(n - m)$. If $N$ is the number of integers $r$ with
$0 \le r \le p - 1$ such that $\left(\frac{mr+1}{p}\right) = \left(\frac{nr+1}{p}\right) = -1$, then

$$4N = 4\left\lfloor \frac{p}{4} \right\rfloor -
\left(\left(\frac{m}{p}\right) - \left(\frac{n-m}{p}\right)\right)
\left(\left(\frac{n}{p}\right) - \left(\frac{m-n}{p}\right)\right).$$

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 1
(`integers-2025-A32-lem-1`). -/
public theorem_wanted four_mul_card_legendreSym_pair_eq_neg_one (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (m n : ℤ) (hmn : ¬ (p : ℤ) ∣ m * n * (n - m)) :
    4 * ((((Finset.range p).filter fun r : ℕ =>
        legendreSym p (m * r + 1) = -1 ∧ legendreSym p (n * r + 1) = -1).card : ℕ) : ℤ) =
      4 * ((p / 4 : ℕ) : ℤ) -
        (legendreSym p m - legendreSym p (n - m)) * (legendreSym p n - legendreSym p (m - n))

/-- **Andrews' theorem on partitions with initial repetitions.** Let $k \ge 1$ and $n \ge 0$ be
integers. Say that a partition has initial $k$-repetitions if, whenever a part $j$ appears at
least $k$ times, every integer $i$ with $1 \le i < j$ appears at least $k$ times. Then the number
of partitions of $n$ with initial $k$-repetitions equals the number of partitions of $n$ into parts
not divisible by $2k$, and this number equals the number of partitions of $n$ in which no part
appears more than $2k - 1$ times.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 1 (`integers-2025-A32-thm-1`), quoting Andrews. -/
public theorem_wanted card_initialRepetitions_eq_card_not_dvd_eq_card_count_le (n k : ℕ)
    (hk : 1 ≤ k) :
    ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
        ∀ j ∈ p.parts, k ≤ p.parts.count j → ∀ i ∈ Finset.Ico 1 j, k ≤ p.parts.count i).card =
      ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
        ∀ a ∈ p.parts, ¬ 2 * k ∣ a).card ∧
    ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
        ∀ a ∈ p.parts, ¬ 2 * k ∣ a).card =
      ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
        ∀ a ∈ p.parts, p.parts.count a ≤ 2 * k - 1).card

/-- **The partition function $c_2$ of Nyirenda and Mugwangwavari.** For an integer $n \ge 0$,
$c_2(n)$ is the number of partitions of $n$ for which there is an integer $j$ with
$1 \le j \le n$ such that $j$ appears exactly $j$ times, every part other than $j$ is at least
$2j + 1$, and every even part that is at least $2j + 2$ appears only once.

Odd parts that are at least $2j + 1$ may appear any number of times.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 3 (definition of `c₂`, from Nyirenda and Mugwangwavari). -/
public def initialRepetitionsC2 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
    ∃ j ∈ Finset.Icc 1 n, p.parts.count j = j ∧ (∀ a ∈ p.parts, a = j ∨ 2 * j + 1 ≤ a) ∧
      ∀ a ∈ p.parts, Even a → 2 * j + 2 ≤ a → p.parts.count a = 1).card

/-- **The initial-repetitions partition function $c_3$.** For $n \ge 0$, $c_3(n)$ is the number
of partitions of $n$ for which there is an integer $j$ with $1 \le j \le n$ such that the part $1$
appears exactly $j^2$ or $j^2 + 1$ times, every odd part larger than $1$ appears exactly once,
every even part appears exactly once, and every even part greater than $2j$ is at least $4j + 4$
and divisible by $4$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 3 (definition of `c₃`, from Nyirenda and Mugwangwavari). -/
public def initialRepetitionsC3 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
    ∃ j ∈ Finset.Icc 1 n, (p.parts.count 1 = j ^ 2 ∨ p.parts.count 1 = j ^ 2 + 1) ∧
      (∀ a ∈ p.parts, Odd a → 1 < a → p.parts.count a = 1) ∧
      (∀ a ∈ p.parts, Even a → p.parts.count a = 1) ∧
      ∀ a ∈ p.parts, Even a → 2 * j < a → 4 * j + 4 ≤ a ∧ 4 ∣ a).card

/-- **The partition function $c_8$.** For $n \ge 0$, $c_8(n)$ is the number of partitions of $n$
such that either (a) all parts are even and distinct, or (b) for some positive integer $j$, the
largest odd part is $2j - 1$, every positive odd integer $i \le j$ appears once or twice, every
odd integer $i$ with $j < i \le 2j - 1$ appears exactly once, all even parts are distinct, and
every even part greater than $j$ is at least $2j + 2$.

For $j = 1$ the paper's clauses "the largest odd part $2j - 1$ appears once" and "odd integers
$\le j$ appear once or twice" conflict; the second governs, as in the generating function
$(q^2;q^2)_\infty \sum_n q^{n^2}/(q;q)_n$ the paper uses (the other reading gives $c_8(2) = 1$,
contradicting Theorem 11 of the paper since $31$ is not a square).

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 3 (definition of `c₈`, from Nyirenda and Mugwangwavari). -/
public def initialRepetitionsC8 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
    (∀ a ∈ p.parts, Even a ∧ p.parts.count a = 1) ∨
      ∃ j ∈ Finset.Icc 1 n, 2 * j - 1 ∈ p.parts ∧ (∀ a ∈ p.parts, Odd a → a ≤ 2 * j - 1) ∧
        (∀ i ∈ Finset.Icc 1 j, Odd i → p.parts.count i = 1 ∨ p.parts.count i = 2) ∧
        (∀ i ∈ Finset.Ioc j (2 * j - 1), Odd i → p.parts.count i = 1) ∧
        (∀ a ∈ p.parts, Even a → p.parts.count a = 1) ∧
        ∀ a ∈ p.parts, Even a → j < a → 2 * j + 2 ≤ a).card

/-- **The initial-repetitions partition function $c_8'$.** For $n \ge 0$, $c_8'(n)$ is the number
of partitions of $n$ into distinct even parts plus the sum, over $m = 1, \dots, n$, of the number
of partitions of $n$ in which every even number $2i$ with $1 \le i \le m$ is a part, every even
part at most $m$ appears at most twice, every odd part at most $m$ appears exactly once, and every
part greater than $m$ is even and appears exactly once.

Equivalently, $c_8'(n)$ counts partitions of $n$ with a possibly distinguished part: either all
parts are even and distinct and no part is distinguished, or a part $2m$ is distinguished and the
conditions above hold for $m$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 4 (definition of `c₈'`). -/
public def initialRepetitionsC8Prime (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
      ∀ a ∈ p.parts, Even a ∧ p.parts.count a = 1).card +
    ∑ m ∈ Finset.Icc 1 n, ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
      (∀ i ∈ Finset.Icc 1 m, 2 * i ∈ p.parts) ∧
        (∀ a ∈ p.parts, Even a → a ≤ m → p.parts.count a ≤ 2) ∧
        (∀ a ∈ p.parts, Odd a → a ≤ m → p.parts.count a = 1) ∧
        ∀ a ∈ p.parts, m < a → Even a ∧ p.parts.count a = 1).card

/-- **Small values of the partition functions $c_2$, $c_3$, $c_8$ and $c_8'$.** We have
$c_2(0) = 0$, $c_2(1) = 1$, $c_3(1) = 1$, $c_8(0) = c_8(1) = 1$, $c_8'(0) = 1$ and $c_8'(1) = 0$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Sections 3 and 4 (definitions of `c₂`, `c₃`, `c₈`, `c₈'`). -/
public theorem initialRepetitions_values_zero_one :
    initialRepetitionsC2 0 = 0 ∧ initialRepetitionsC2 1 = 1 ∧ initialRepetitionsC3 1 = 1 ∧
      initialRepetitionsC8 0 = 1 ∧ initialRepetitionsC8 1 = 1 ∧
      initialRepetitionsC8Prime 0 = 1 ∧ initialRepetitionsC8Prime 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [initialRepetitionsC2, initialRepetitionsC3, initialRepetitionsC8,
      initialRepetitionsC8Prime, Finset.univ_unique, Finset.filter_singleton]
  all_goals decide

/-- **Parity of $c_2(5n + 2)$.** Let $c_2(m)$ be the number of partitions of $m$ for which there
is an integer $j$ with $1 \le j \le m$ such that $j$ appears exactly $j$ times, every part other
than $j$ is at least $2j + 1$, and every even part that is at least $2j + 2$ appears only once.
Nyirenda and Mugwangwavari: for every integer $n \ge 0$, the number $c_2(5n + 2)$ is even.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 3 (`integers-2025-A32-thm-3`). -/
public theorem_wanted initialRepetitionsC2_five_mul_add_two_even (n : ℕ) :
    Even (initialRepetitionsC2 (5 * n + 2))

/-- **Parity of $c_2(pn + r)$ for primes $p \ge 5$.** Let $c_2(m)$ be the number of partitions of
$m$ for which there is an integer $j$ with $1 \le j \le m$ such that $j$ appears exactly $j$
times, every part other than $j$ is at least $2j + 1$, and every even part that is at least
$2j + 2$ appears only once. Let $p \ge 5$ be a prime and let $r$ be an integer with
$1 \le r \le p - 1$ such that neither $16r + 1$ nor $8r + 1$ is a square modulo $p$. Then
$c_2(pn + r)$ is even for every integer $n \ge 0$.

Here $0$ counts as a square modulo $p$, so the hypothesis says that $16r + 1$ and $8r + 1$ are
quadratic nonresidues modulo $p$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 4 (`integers-2025-A32-thm-4`). -/
public theorem_wanted initialRepetitionsC2_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h16 : ¬ IsSquare ((16 * r + 1 : ℕ) : ZMod p)) (h8 : ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC2 (p * n + r))

/-- **Parity of $c_3(11n + 5)$, $c_3(11n + 7)$ and $c_3(11n + 9)$.** Let $c_3(m)$ be the number
of partitions of $m$ for which there is an integer $j$ with $1 \le j \le m$ such that the part $1$
appears exactly $j^2$ or $j^2 + 1$ times, the odd parts greater than $1$ are distinct, the even
parts are distinct, and every even part greater than $2j$ is divisible by $4$ and at least
$4j + 4$. Nyirenda and Mugwangwavari: for every integer $n \ge 0$, the numbers $c_3(11n + 5)$,
$c_3(11n + 7)$ and $c_3(11n + 9)$ are all even.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 6 (`integers-2025-A32-thm-6`). -/
public theorem_wanted initialRepetitionsC3_eleven_mul_add_even (n : ℕ) :
    Even (initialRepetitionsC3 (11 * n + 5)) ∧ Even (initialRepetitionsC3 (11 * n + 7)) ∧
      Even (initialRepetitionsC3 (11 * n + 9))

/-- **Parity of $c_3$ on residue classes modulo a prime.** Let $c_3$ be the initial-repetitions
partition function of Nyirenda and Mugwangwavari. Let $p \ge 5$ be a prime and let $r$ be an
integer with $1 \le r \le p - 1$ such that neither $12r + 1$ nor $8r + 1$ is a square modulo $p$.
Then $c_3(pn + r)$ is even for every integer $n \ge 0$.

Here $x$ is a square modulo $p$ when $x \equiv y^2 \pmod{p}$ for some integer $y$, so multiples
of $p$ count as squares.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 7 (`integers-2025-A32-thm-7`). -/
public theorem_wanted initialRepetitionsC3_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h12 : ¬ IsSquare ((12 * r + 1 : ℕ) : ZMod p)) (h8 : ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC3 (p * n + r))

/-- **$c_8$ is even on six residue classes modulo $49$.** Let $c_8$ be the initial-repetitions
partition function of Nyirenda and Mugwangwavari. For every integer $n \ge 0$ and every
$r \in \{6, 20, 27, 34, 41, 48\}$, the number $c_8(49n + r)$ is even.

This result is due to Nyirenda and Mugwangwavari.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 9 (`integers-2025-A32-thm-9`). -/
public theorem_wanted initialRepetitionsC8_fortyNine_mul_add_even (n r : ℕ)
    (hr : r ∈ ({6, 20, 27, 34, 41, 48} : Finset ℕ)) :
    Even (initialRepetitionsC8 (49 * n + r))

/-- **Andrews' identity for the first Rogers–Ramanujan series.** Let $q$ be a complex number with
$|q| < 1$, write $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$ for $j \ge 0$, and let
$(q^2;q^2)_\infty = \prod_{n=0}^{\infty} (1 - q^{2n+2})$ be the infinite q-Pochhammer symbol. Then

$$(q^2;q^2)_\infty \sum_{j=0}^{\infty} \frac{q^{j^2}}{(q;q)_j} = \sum_{\lambda \in \mathbb{Z}}
\left(q^{60\lambda^2+4\lambda} - q^{60\lambda^2+44\lambda+8} + q^{60\lambda^2+16\lambda+1} -
q^{60\lambda^2+64\lambda+17}\right).$$

All exponents on the right are nonnegative for integer $\lambda$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 10 (`integers-2025-A32-thm-10`), quoting Andrews. -/
public theorem_wanted andrews_rogersRamanujan_first_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInf (q ^ 2) (q ^ 2)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero) *
      ∑' j : ℕ, q ^ (j ^ 2) / ∏ i ∈ Finset.range j, (1 - q ^ (i + 1)) =
    ∑' l : ℤ, (q ^ (60 * l ^ 2 + 4 * l) - q ^ (60 * l ^ 2 + 44 * l + 8) +
      q ^ (60 * l ^ 2 + 16 * l + 1) - q ^ (60 * l ^ 2 + 64 * l + 17))

/-- **$c_8(N)$ is even when $15N + 1$ is not a square.** Let $c_8$ be the initial-repetitions
partition function of Nyirenda and Mugwangwavari. For every integer $N \ge 0$ such that $15N + 1$
is not a perfect square, $c_8(N)$ is even.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 11 (`integers-2025-A32-thm-11`). -/
public theorem_wanted initialRepetitionsC8_even_of_not_isSquare (N : ℕ)
    (hN : ¬ IsSquare (15 * N + 1)) :
    Even (initialRepetitionsC8 N)

/-- **Andrews' identity for the second Rogers–Ramanujan series.** Let $q$ be a complex number
with $|q| < 1$, write $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$ for $j \ge 0$, and let
$(q^2;q^2)_\infty = \prod_{n=0}^{\infty} (1 - q^{2n+2})$ be the infinite q-Pochhammer symbol. Then

$$(q^2;q^2)_\infty \sum_{j=0}^{\infty} \frac{q^{j^2+j}}{(q;q)_j} = \sum_{\lambda \in \mathbb{Z}}
\left(q^{60\lambda^2+8\lambda} - q^{60\lambda^2+32\lambda+4} + q^{60\lambda^2+28\lambda+3} -
q^{60\lambda^2+52\lambda+11}\right).$$

All exponents on the right are nonnegative for integer $\lambda$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 12 (`integers-2025-A32-thm-12`), quoting Andrews. -/
public theorem_wanted andrews_rogersRamanujan_second_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInf (q ^ 2) (q ^ 2)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero) *
      ∑' j : ℕ, q ^ (j ^ 2 + j) / ∏ i ∈ Finset.range j, (1 - q ^ (i + 1)) =
    ∑' l : ℤ, (q ^ (60 * l ^ 2 + 8 * l) - q ^ (60 * l ^ 2 + 32 * l + 4) +
      q ^ (60 * l ^ 2 + 28 * l + 3) - q ^ (60 * l ^ 2 + 52 * l + 11))

/-- **$c_8'(N)$ is even when $15N + 4$ is not a square.** Let $c_8'$ be the partition function
that counts partitions with a possibly distinguished part. For every integer $N \ge 0$ such that
$15N + 4$ is not a perfect square, $c_8'(N)$ is even.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 13 (`integers-2025-A32-thm-13`). -/
public theorem_wanted initialRepetitionsC8Prime_even_of_not_isSquare (N : ℕ)
    (hN : ¬ IsSquare (15 * N + 4)) :
    Even (initialRepetitionsC8Prime N)

/-- **Parity of $c_8$ on residue classes modulo powers of $2$.** Let $c_8$ be the
initial-repetitions partition function of Nyirenda and Mugwangwavari, and let $k \ge 1$,
$n \ge 0$ and $r \ge 0$ be integers. If $r < 2^{2k}$ and $15r \equiv 2^{2k-1} - 1 \pmod{2^{2k}}$,
then $c_8(2^{2k} n + r)$ is even. If $r < 2^{2k}$ and
$15r \equiv 2^{2k-1} + 2^{2k-2} - 1 \pmod{2^{2k}}$, then $c_8(2^{2k} n + r)$ is even. If
$r < 2^{2k+1}$ and $15r \equiv 2^{2k} + 2^{2k-2} - 1 \pmod{2^{2k+1}}$, then
$c_8(2^{2k+1} n + r)$ is even.

These $r$ are the paper's least nonnegative residues $r_{k,1}$, $r_{k,2}$, $r_{k,3}$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 1 (`integers-2025-A32-cor-1`). -/
public theorem_wanted initialRepetitionsC8_two_pow_mul_add_even (k n r : ℕ) (hk : 1 ≤ k) :
    (r < 2 ^ (2 * k) → (15 * r : ℤ) ≡ 2 ^ (2 * k - 1) - 1 [ZMOD 2 ^ (2 * k)] →
        Even (initialRepetitionsC8 (2 ^ (2 * k) * n + r))) ∧
      (r < 2 ^ (2 * k) → (15 * r : ℤ) ≡ 2 ^ (2 * k - 1) + 2 ^ (2 * k - 2) - 1 [ZMOD 2 ^ (2 * k)] →
        Even (initialRepetitionsC8 (2 ^ (2 * k) * n + r))) ∧
      (r < 2 ^ (2 * k + 1) →
        (15 * r : ℤ) ≡ 2 ^ (2 * k) + 2 ^ (2 * k - 2) - 1 [ZMOD 2 ^ (2 * k + 1)] →
        Even (initialRepetitionsC8 (2 ^ (2 * k + 1) * n + r)))

/-- **Parity of $c_8$ on residue classes modulo a prime.** Let $c_8$ be the initial-repetitions
partition function of Nyirenda and Mugwangwavari. Let $p \ge 7$ be a prime and let $r$ be an
integer with $1 \le r \le p - 1$ such that $15r + 1$ is not a square modulo $p$. Then
$c_8(pn + r)$ is even for every integer $n \ge 0$.

Here $x$ is a square modulo $p$ when $x \equiv y^2 \pmod{p}$ for some integer $y$, so multiples
of $p$ count as squares.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 2 (`integers-2025-A32-cor-2`). -/
public theorem_wanted initialRepetitionsC8_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h15 : ¬ IsSquare ((15 * r + 1 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC8 (p * n + r))

/-- **Parity of $c_8'$ on residue classes modulo powers of $2$.** Let $c_8'$ be the partition
function that counts partitions with a possibly distinguished part, and let $k \ge 1$, $n \ge 0$
and $r \ge 0$ be integers. If $r < 2^{2k}$ and $15r \equiv 2^{2k-1} - 4 \pmod{2^{2k}}$, then
$c_8'(2^{2k} n + r)$ is even. If $r < 2^{2k}$ and
$15r \equiv 2^{2k-1} + 2^{2k-2} - 4 \pmod{2^{2k}}$, then $c_8'(2^{2k} n + r)$ is even. If
$r < 2^{2k+1}$ and $15r \equiv 2^{2k} + 2^{2k-2} - 4 \pmod{2^{2k+1}}$, then
$c_8'(2^{2k+1} n + r)$ is even.

These $r$ are the paper's least nonnegative residues $r'_{k,1}$, $r'_{k,2}$, $r'_{k,3}$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 3 (`integers-2025-A32-cor-3`). -/
public theorem_wanted initialRepetitionsC8Prime_two_pow_mul_add_even (k n r : ℕ) (hk : 1 ≤ k) :
    (r < 2 ^ (2 * k) → (15 * r : ℤ) ≡ 2 ^ (2 * k - 1) - 4 [ZMOD 2 ^ (2 * k)] →
        Even (initialRepetitionsC8Prime (2 ^ (2 * k) * n + r))) ∧
      (r < 2 ^ (2 * k) → (15 * r : ℤ) ≡ 2 ^ (2 * k - 1) + 2 ^ (2 * k - 2) - 4 [ZMOD 2 ^ (2 * k)] →
        Even (initialRepetitionsC8Prime (2 ^ (2 * k) * n + r))) ∧
      (r < 2 ^ (2 * k + 1) →
        (15 * r : ℤ) ≡ 2 ^ (2 * k) + 2 ^ (2 * k - 2) - 4 [ZMOD 2 ^ (2 * k + 1)] →
        Even (initialRepetitionsC8Prime (2 ^ (2 * k + 1) * n + r)))

/-- **Parity of $c_8'$ on residue classes modulo a prime.** Let $c_8'$ be the partition function
that counts partitions with a possibly distinguished part. Let $p \ge 7$ be a prime and let $r$ be
an integer with $1 \le r \le p - 1$ such that $15r + 4$ is not a square modulo $p$. Then
$c_8'(pn + r)$ is even for every integer $n \ge 0$.

Here $x$ is a square modulo $p$ when $x \equiv y^2 \pmod{p}$ for some integer $y$, so multiples
of $p$ count as squares.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 4 (`integers-2025-A32-cor-4`). -/
public theorem_wanted initialRepetitionsC8Prime_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h15 : ¬ IsSquare ((15 * r + 4 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC8Prime (p * n + r))

end

end MetaMathlibExt
