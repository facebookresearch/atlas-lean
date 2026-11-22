/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.NumberTheory.CoveringSystem
public import MathlibExt.NumberTheory.PrimitiveDivisor

/-!
# Sierpiński and Riesel repdigits, repintegers and repstrings

Statements from Chris Bispels, Matthew Cohen, Joshua Harrington, Joshua Lowrance, Kaelyn Pontes,
Leif Schaumann and Tony W. H. Wong, *On Sierpiński and Riesel Repdigits and Repintegers*,
INTEGERS 26 (2026), Article A12 (arXiv `2505.00778`, TeX source read).

A Sierpiński (Riesel) number is an odd `k` with `k·2^n + 1` (`k·2^n - 1`) composite for every
`n ≥ 1`. For `b ≥ 2`, `k ≥ 1`, `z ≥ 0`, `t ≥ 1` and `ℓ` the number of base-`b` digits of `k`, the
*`b`-repstring* is `k_b^{(z;t)} = k (b^{(z+ℓ)t} - 1)/(b^{z+ℓ} - 1)` (`k` written `t` times with `z`
zeros between copies); `z = 0` gives the *`b`-repinteger* `k_b^{(t)}`, `k < b` the *`b`-repdigit*
`k (b^t - 1)/(b - 1)`, and `k = 1` the *`b`-repunit*.

The *covering system method* (Section 2) produces `k` from triples `(r_j, m_j, p_j)` such that
the classes `r_j mod m_j` cover `ℤ`, the `p_j` are distinct primes with `p_j ∣ 2^{m_j} - 1`, and
`k ≡ -2^{-r_j}` (Sierpiński) or `k ≡ 2^{-r_j}` (Riesel) modulo `p_j`, i.e. `p_j ∣ k·2^{r_j} ± 1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sierpiński number.** A natural number $k$ is a Sierpiński number if $k$ is odd and,
for every integer $n \ge 1$, the number $k \cdot 2^n + 1$ is not prime.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, abstract and Section 1. -/
public def IsSierpinskiNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ (k * 2 ^ n + 1).Prime

/-- **Riesel number.** A natural number $k$ is a Riesel number if $k$ is odd and, for every
integer $n \ge 1$, the number $k \cdot 2^n - 1$ is not prime.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, abstract and Section 1. -/
public def IsRieselNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ (k * 2 ^ n - 1).Prime

/-- **$1$ is not a Sierpiński number.** The number $1$ is not a Sierpiński number, since
$1 \cdot 2 + 1 = 3$ is prime.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 1. -/
public theorem not_isSierpinskiNumber_one : ¬ IsSierpinskiNumber 1 := fun h =>
  h.2 1 le_rfl (by simpa using Nat.prime_three)

/-- **One is not a Riesel number.** The number $1$ is not a Riesel number, since
$1 \cdot 2^2 - 1 = 3$ is prime.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 1. -/
public theorem not_isRieselNumber_one : ¬ IsRieselNumber 1 := fun h =>
  h.2 2 (by norm_num) (by simpa using Nat.prime_three)

/-- **Repstrings.** For natural numbers $b$, $k$, $z$ and $t$, let $\ell$ be the number of base-$b$
digits of $k$. The $b$-repstring is

$$k_b^{(z;t)} = \left\lfloor \frac{k\,(b^{(z+\ell)t} - 1)}{b^{z+\ell} - 1} \right\rfloor,$$

where subtraction is truncated at $0$ and the integer division gives $0$ when the denominator is
$0$. For $z = 0$ it is the $b$-repinteger $k_b^{(t)}$.

For $b \ge 2$ and $k \ge 1$ the division is exact, and $k_b^{(z;t)}$ is the number whose base-$b$
expansion is $k$ written $t$ times with $z$ zeros between consecutive copies.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Sections 1 and 4. -/
public def repstring (b k z t : ℕ) : ℕ :=
  k * (b ^ ((z + (Nat.digits b k).length) * t) - 1) / (b ^ (z + (Nat.digits b k).length) - 1)

/-- **A $10$-repstring.** The $10$-repstring with $k = 1$, $z = 2$ and $t = 3$ is
$1_{10}^{(2;3)} = 1001001$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 4. -/
public theorem repstring_ten_one_two_three : repstring 10 1 2 3 = 1001001 := by
  norm_num [repstring]

/-- **The three-digit $2$-repunit.** The $2$-repstring with $k = 1$, $z = 0$ and $t = 3$, that is,
the $2$-repunit $1_2^{(3)}$ with three digits, equals $7$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 1. -/
public theorem repstring_two_one_zero_three : repstring 2 1 0 3 = 7 := by
  norm_num [repstring]

/-- **Sierpiński covering data.** Let $k$ be a natural number and $S$ a finite set of triples
$(r, m, p)$ of natural numbers. Then $S$ is Sierpiński covering data for $k$ if every integer is
congruent to $r$ modulo $m$ for some $(r, m, p) \in S$, distinct triples in $S$ have distinct
third entries, and every $(r, m, p) \in S$ has $m \ge 1$, $p$ prime, $p \mid 2^m - 1$ and
$p \mid k \cdot 2^r + 1$.

This is the input of the covering system method for Sierpiński numbers; the last condition says
that $k \equiv -2^{-r} \pmod{p}$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 2, Equation (2). -/
public def IsSierpinskiCoveringData (k : ℕ) (S : Finset (ℕ × ℕ × ℕ)) : Prop :=
  Int.IsCoveringSystem (S.image fun s => ((s.1 : ℤ), s.2.1)) ∧
    Set.InjOn (fun s : ℕ × ℕ × ℕ => s.2.2) (S : Set (ℕ × ℕ × ℕ)) ∧
    ∀ s ∈ S, 1 ≤ s.2.1 ∧ s.2.2.Prime ∧ s.2.2 ∣ 2 ^ s.2.1 - 1 ∧ s.2.2 ∣ k * 2 ^ s.1 + 1

/-- **Riesel covering data.** Let $k$ be a natural number and let $S$ be a finite set of triples
$(r, m, p)$ of natural numbers. Then $S$ is Riesel covering data for $k$ (data producing $k$ as a
Riesel number by the covering system method) when every integer is congruent to $r$ modulo $m$
for some $(r, m, p) \in S$, distinct triples in $S$ have distinct third entries $p$, and every
$(r, m, p) \in S$ has $m \ge 1$, $p$ prime, $p \mid 2^m - 1$ and $p \mid k \cdot 2^r - 1$ (for
$k \ge 1$ the last condition says $k \equiv 2^{-r} \pmod p$).

Subtraction is in the natural numbers, so for $k = 0$ the condition $p \mid k \cdot 2^r - 1$ reads
$p \mid 0$ and holds trivially.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 2, Equation (3). -/
public def IsRieselCoveringData (k : ℕ) (S : Finset (ℕ × ℕ × ℕ)) : Prop :=
  Int.IsCoveringSystem (S.image fun s => ((s.1 : ℤ), s.2.1)) ∧
    Set.InjOn (fun s : ℕ × ℕ × ℕ => s.2.2) (S : Set (ℕ × ℕ × ℕ)) ∧
    ∀ s ∈ S, 1 ≤ s.2.1 ∧ s.2.2.Prime ∧ s.2.2 ∣ 2 ^ s.2.1 - 1 ∧ s.2.2 ∣ k * 2 ^ s.1 - 1

/-- **Empty Sierpiński covering data.** For every natural number $k$, the empty set is not
Sierpiński covering data for $k$: the empty family of residue classes does not cover $\mathbb{Z}$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 2. -/
public theorem not_isSierpinskiCoveringData_empty (k : ℕ) : ¬ IsSierpinskiCoveringData k ∅ :=
  fun h => by simpa using h.1 0

/-- **The empty set is not Riesel covering data.** For every natural number $k$, the empty set is
not Riesel covering data for $k$, because its residue classes do not cover $\mathbb{Z}$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 2. -/
public theorem not_isRieselCoveringData_empty (k : ℕ) : ¬ IsRieselCoveringData k ∅ :=
  fun h => by simpa using h.1 0

/-- **Theorem 3.2 (no Sierpiński $2$-repdigits from coverings).** For every natural number
$t \ge 1$, the covering system method cannot produce the $2$-repdigit $2^t - 1$ as a
Sierpiński number: no finite set of triples $(r_j, m_j, p_j)$ is Sierpiński covering data
for $2^t - 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.2
(`integers-2026-A12-thm-3-2`). -/
public theorem_wanted not_isSierpinskiCoveringData_two_pow_sub_one {t : ℕ} (ht : 1 ≤ t)
    (S : Finset (ℕ × ℕ × ℕ)) : ¬ IsSierpinskiCoveringData (2 ^ t - 1) S

/-- **Covering-produced Sierpiński numbers give infinitely many Sierpiński repintegers.** Let $k$
be a Sierpiński number that has Sierpiński covering data, so that $k$ is produced as a Sierpiński
number by the covering system method. Then for every natural number $b \ge 2$ there are infinitely
many $t \ge 1$ such that the $b$-repinteger $k_b^{(t)} = k\,(b^{\ell t} - 1)/(b^{\ell} - 1)$, where
$\ell$ is the number of base-$b$ digits of $k$ (so $k_b^{(t)}$ is $k$ written $t$ times in base
$b$), is a Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.3
(`integers-2026-A12-thm-3-3`). -/
public theorem_wanted infinite_sierpinski_repintegers {k : ℕ} (hk : IsSierpinskiNumber k)
    {S : Finset (ℕ × ℕ × ℕ)} (hS : IsSierpinskiCoveringData k S) {b : ℕ} (hb : 2 ≤ b) :
    {t : ℕ | 1 ≤ t ∧ IsSierpinskiNumber (repstring b k 0 t)}.Infinite

/-- **Covering-produced Riesel numbers give infinitely many Riesel repintegers.** Let $k$ be a
Riesel number that has Riesel covering data, so that $k$ is produced as a Riesel number by the
covering system method. Then for every natural number $b \ge 2$ there are infinitely many $t \ge 1$
such that the $b$-repinteger $k_b^{(t)} = k\,(b^{\ell t} - 1)/(b^{\ell} - 1)$, where $\ell$ is the
number of base-$b$ digits of $k$ (so $k_b^{(t)}$ is $k$ written $t$ times in base $b$), is a Riesel
number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.4 (stated in record
`integers-2026-A12-thm-3-3`). -/
public theorem_wanted infinite_riesel_repintegers {k : ℕ} (hk : IsRieselNumber k)
    {S : Finset (ℕ × ℕ × ℕ)} (hS : IsRieselCoveringData k S) {b : ℕ} (hb : 2 ≤ b) :
    {t : ℕ | 1 ≤ t ∧ IsRieselNumber (repstring b k 0 t)}.Infinite

/-- **Binary repintegers of 18107 that are Sierpiński numbers.** For every natural number
$t \equiv 25 \pmod{56}$, the binary repinteger $18107_2^{(t)} = 18107\,(2^{15t} - 1)/(2^{15} - 1)$,
whose binary expansion is that of $18107$ (fifteen binary digits) written $t$ times, is a
Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.5
(`integers-2026-A12-thm-3-5`). -/
public theorem_wanted isSierpinskiNumber_repstring_18107 {t : ℕ} (ht : t ≡ 25 [MOD 56]) :
    IsSierpinskiNumber (repstring 2 18107 0 t)

/-- **Binary repintegers of 18107 that are Riesel numbers.** For every natural number
$t \equiv 31 \pmod{56}$, the binary repinteger $18107_2^{(t)} = 18107\,(2^{15t} - 1)/(2^{15} - 1)$,
whose binary expansion is that of $18107$ (fifteen binary digits) written $t$ times, is a Riesel
number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.6
(`integers-2026-A12-thm-3-6`). -/
public theorem_wanted isRieselNumber_repstring_18107 {t : ℕ} (ht : t ≡ 31 [MOD 56]) :
    IsRieselNumber (repstring 2 18107 0 t)

/-- **Infinitely many Sierpiński repdigits in every base $b > 78557$.** Let $b > 78557$ be a
natural number. Then there are infinitely many Sierpiński numbers of the form $k(b^t - 1)/(b - 1)$
with $1 \le k < b$ and $t \ge 1$, that is, $b$-repdigits: the digit $k$ written $t$ times in
base $b$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.7
(`integers-2026-A12-cor-3-7`). -/
public theorem_wanted infinite_sierpinski_repdigits {b : ℕ} (hb : 78557 < b) :
    {N : ℕ | ∃ k t : ℕ, 1 ≤ k ∧ k < b ∧ 1 ≤ t ∧ N = repstring b k 0 t ∧
      IsSierpinskiNumber N}.Infinite

/-- **Infinitely many Riesel repdigits in every base $b > 509203$.** Let $b > 509203$ be a
natural number. Then there are infinitely many Riesel numbers of the form $k(b^t - 1)/(b - 1)$ with
$1 \le k < b$ and $t \ge 1$, that is, $b$-repdigits: the digit $k$ written $t$ times in base $b$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.8
(`integers-2026-A12-cor-3-8`). -/
public theorem_wanted infinite_riesel_repdigits {b : ℕ} (hb : 509203 < b) :
    {N : ℕ | ∃ k t : ℕ, 1 ≤ k ∧ k < b ∧ 1 ≤ t ∧ N = repstring b k 0 t ∧
      IsRieselNumber N}.Infinite

/-- **Repdigits with digit 41 that are Sierpiński numbers.** Let $b$ and $t$ be natural numbers
with $b \equiv 87 \pmod{11184810}$ and $t \equiv 59 \pmod{120}$. Then the base-$b$ repdigit
$41_b^{(t)} = 41\,(b^t - 1)/(b - 1)$ is a Sierpiński number. Since $b \ge 87 > 41$, its $t$
base-$b$ digits all equal $41$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.9
(`integers-2026-A12-thm-3-9`). -/
public theorem_wanted isSierpinskiNumber_repstring_41 {b t : ℕ} (hb : b ≡ 87 [MOD 11184810])
    (ht : t ≡ 59 [MOD 120]) : IsSierpinskiNumber (repstring b 41 0 t)

/-- **Riesel repdigits with digit $101$ in bases $b \equiv 180 \pmod{11184810}$.** Let $b$ and $t$
be natural numbers with $b \equiv 180 \pmod{11184810}$ and $t \equiv 171 \pmod{240}$. Then the
$b$-repinteger $101_b^{(t)}$, which is the repdigit $101\,(b^t - 1)/(b - 1)$ because $101 < b$, is
a Riesel number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.10
(`integers-2026-A12-thm-3-10`). -/
public theorem_wanted isRieselNumber_repstring_101 {b t : ℕ} (hb : b ≡ 180 [MOD 11184810])
    (ht : t ≡ 171 [MOD 240]) : IsRieselNumber (repstring b 101 0 t)

/-- **Infinitely many Sierpiński repunits from primitive divisors of $2^{2^j} - 1$.** Let $\tau$
be a natural number. For $1 \le j \le \tau$ let $p_j$ be a primitive prime divisor of
$2^{2^j} - 1$ in the sequence $(2^m - 1)_{m \ge 0}$, and let $q \ne p_\tau$ be a primitive prime
divisor of $2^{2^\tau} - 1$ in the same sequence. Let $b > 2$ be a natural number with $q \nmid b$.
For $1 \le j \le \tau$ put $\ell_j = 1$ if $p_j \mid b$, $\ell_j = p_j$ if $p_j \nmid b$ and
$b \equiv 1 \pmod{p_j}$, and otherwise $\ell_j = \operatorname{ord}_{p_j}(b)$, the multiplicative
order of $b$ modulo $p_j$; let $L = \operatorname{lcm}(2, \ell_1, \dots, \ell_\tau)$. Suppose that
either (i) $b \equiv 1 \pmod q$ and $q \nmid L$, or (ii) $b \not\equiv 1 \pmod q$ and there is a
natural number $s \equiv 1 \pmod L$ with $(b^s - 1)/(b - 1) \equiv -1 \pmod q$. Then there are
infinitely many Sierpiński numbers among the $b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.11
(`integers-2026-A12-thm-3-11`). -/
public theorem_wanted infinite_sierpinski_repunits_of_primitive_divisors (τ : ℕ) (p : ℕ → ℕ)
    (hp : ∀ j ∈ Finset.Icc 1 τ,
      IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) (2 ^ j) (p j))
    (q : ℕ) (hq : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) (2 ^ τ) q)
    (hqp : q ≠ p τ) (b : ℕ) (hb : 2 < b) (hbq : ¬ q ∣ b)
    (hcase :
      let ℓ : ℕ → ℕ := fun j =>
        if p j ∣ b then 1 else if b ≡ 1 [MOD p j] then p j else orderOf (b : ZMod (p j))
      let L : ℕ := Nat.lcm 2 ((Finset.Icc 1 τ).lcm ℓ)
      (b ≡ 1 [MOD q] ∧ ¬ q ∣ L) ∨
        (¬ b ≡ 1 [MOD q] ∧ ∃ t : ℕ, (((b ^ t - 1) / (b - 1) : ℕ) : ℤ) ≡ -1 [ZMOD q] ∧
          t ≡ 1 [MOD L])) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsSierpinskiNumber N}.Infinite

/-- **Infinitely many Sierpiński repunits in bases $b \equiv 1, 147, 265, 378 \pmod{641}$ with
$b \not\equiv 1 \pmod 5$.** Let $b > 2$ be a natural number with $b \equiv c \pmod{641}$ for some
$c \in \{1, 147, 265, 378\}$ and $b \not\equiv 1 \pmod 5$. Then there are infinitely many
Sierpiński numbers among the $b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.12
(`integers-2026-A12-cor-3-12`). -/
public theorem_wanted infinite_sierpinski_repunits_mod_641 {b : ℕ} (hb : 2 < b)
    (h641 : ∃ c ∈ ({1, 147, 265, 378} : Finset ℕ), b ≡ c [MOD 641]) (h5 : ¬ b ≡ 1 [MOD 5]) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsSierpinskiNumber N}.Infinite

/-- **Infinitely many Riesel repunits from primitive divisors of $2^{2^j} - 1$.** Let $\tau$ be a
natural number. For $1 \le j \le \tau$ let $p_j$ be a primitive prime divisor of $2^{2^j} - 1$ in
the sequence $(2^m - 1)_{m \ge 0}$, let $q \ne p_\tau$ be a primitive prime divisor of
$2^{2^\tau} - 1$ in the same sequence, and put $P = p_1 \cdots p_\tau$. Let $b > 2$ be a natural
number with $b \equiv 1 \pmod P$, and suppose that (i) $q \mid b$, or (ii) $b \equiv 1 \pmod q$, or
(iii) $q \nmid b$, $b \not\equiv 1 \pmod q$ and $\gcd(P, \operatorname{ord}_q(b)) = 1$, where
$\operatorname{ord}_q(b)$ is the multiplicative order of $b$ modulo $q$. Then there are infinitely
many Riesel numbers among the $b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.13
(`integers-2026-A12-thm-3-13`). -/
public theorem_wanted infinite_riesel_repunits_of_primitive_divisors (τ : ℕ) (p : ℕ → ℕ)
    (hp : ∀ j ∈ Finset.Icc 1 τ,
      IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) (2 ^ j) (p j))
    (q : ℕ) (hq : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) (2 ^ τ) q)
    (hqp : q ≠ p τ) (b : ℕ) (hb : 2 < b) (hbP : b ≡ 1 [MOD ∏ j ∈ Finset.Icc 1 τ, p j])
    (hcase : q ∣ b ∨ b ≡ 1 [MOD q] ∨
      (¬ q ∣ b ∧ ¬ b ≡ 1 [MOD q] ∧
        Nat.Coprime (∏ j ∈ Finset.Icc 1 τ, p j) (orderOf (b : ZMod q)))) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsRieselNumber N}.Infinite

/-- **Infinitely many Riesel repunits in bases $b \equiv 16518444216571 \pmod{2^{64} - 1}$.**
Let $b$ be a natural number with $b \equiv 16518444216571 \pmod{18446744073709551615}$, where
$18446744073709551615 = 2^{64} - 1$. Then there are infinitely many Riesel numbers among the
$b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.14
(`integers-2026-A12-cor-3-14`). -/
public theorem_wanted infinite_riesel_repunits_mod_two_pow_64_sub_one {b : ℕ}
    (hb : b ≡ 16518444216571 [MOD 18446744073709551615]) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsRieselNumber N}.Infinite

/-- **Binary repstrings of 659 that are Sierpiński numbers.** For every natural number $t$ with
$t \equiv 131 \pmod{2730}$ or $t \equiv 1361 \pmod{2730}$, the binary repstring
$659_2^{(2;t)} = 659\,(2^{12t} - 1)/(2^{12} - 1)$ is a Sierpiński number. Its binary expansion is
that of $659$ (ten binary digits) written $t$ times with two zeros between consecutive copies.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 4.3
(`integers-2026-A12-thm-4-3`). -/
public theorem_wanted isSierpinskiNumber_repstring_659 {t : ℕ}
    (ht : t ≡ 131 [MOD 2730] ∨ t ≡ 1361 [MOD 2730]) : IsSierpinskiNumber (repstring 2 659 2 t)

/-- **Binary repstrings of 659 that are Riesel numbers.** For every natural number $t$ with
$t \equiv 1369 \pmod{2730}$ or $t \equiv 2599 \pmod{2730}$, the binary repstring
$659_2^{(2;t)} = 659\,(2^{12t} - 1)/(2^{12} - 1)$ is a Riesel number. Its binary expansion is that
of $659$ (ten binary digits) written $t$ times with two zeros between consecutive copies.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 4.4
(`integers-2026-A12-thm-4-4`). -/
public theorem_wanted isRieselNumber_repstring_659 {t : ℕ}
    (ht : t ≡ 1369 [MOD 2730] ∨ t ≡ 2599 [MOD 2730]) : IsRieselNumber (repstring 2 659 2 t)

/-- **Theorem 4.6 (Sierpiński and Riesel repstring coverings correspond).** Let $k \ge 1$,
$\mathfrak{t} \ge 1$, $w \ge 1$ and $z \ge 0$ be natural numbers. There is a single finite set
of triples that is Sierpiński covering data for the $2$-repstring $k_2^{(z;t)}$ for every
$t \ge 1$ with $t \equiv \mathfrak{t} \pmod{w}$ if and only if there is a single finite set
of triples that is Riesel covering data for $k_2^{(z;t')}$ for every $t' \ge 1$ with
$t' \equiv -\mathfrak{t} \pmod{w}$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 4.6
(`integers-2026-A12-thm-4-6`). -/
public theorem_wanted sierpinskiCoveringData_repstring_iff_riesel {k 𝔱 w : ℕ} (hk : 1 ≤ k)
    (h𝔱 : 1 ≤ 𝔱) (hw : 1 ≤ w) (z : ℕ) :
    (∃ S : Finset (ℕ × ℕ × ℕ), ∀ t : ℕ, 1 ≤ t → t ≡ 𝔱 [MOD w] →
        IsSierpinskiCoveringData (repstring 2 k z t) S) ↔
      ∃ S' : Finset (ℕ × ℕ × ℕ), ∀ t' : ℕ, 1 ≤ t' → (t' : ℤ) ≡ -(𝔱 : ℤ) [ZMOD w] →
        IsRieselCoveringData (repstring 2 k z t') S'

end

end MetaMathlibExt
