/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.CoveringSystem

/-!
# Sierpiński and Riesel repdigits, repintegers and repstrings

Statements from Chris Bispels, Matthew Cohen, Joshua Harrington, Joshua Lowrance, Kaelyn Pontes,
Leif Schaumann and Tony W. H. Wong, *On Sierpiński and Riesel Repdigits and Repintegers*,
INTEGERS 26 (2026), Article A12 (arXiv `2505.00778`).

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
public theorem not_isSierpinskiCoveringData_two_pow_sub_one {t : ℕ} (ht : 1 ≤ t)
    (S : Finset (ℕ × ℕ × ℕ)) : ¬ IsSierpinskiCoveringData (2 ^ t - 1) S := by
  intro ⟨hcover, _, hdata⟩
  obtain ⟨c, hc, hzero⟩ := hcover 0
  obtain ⟨⟨r, m, p⟩, hs, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hm, hp, hperiod, hfactor⟩ := hdata (r, m, p) hs
  -- A representative of the class covering zero can be any multiple of its modulus.
  have hmr : m ∣ r := Int.natCast_dvd_natCast.mp (Int.modEq_zero_iff_dvd.mp hzero.symm)
  have hmod : 1 ≡ 2 ^ m [MOD p] := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 hperiod
  have hres : 1 ≡ 2 ^ r [MOD p] := by
    obtain ⟨d, rfl⟩ := hmr
    simpa only [pow_mul, one_pow] using hmod.pow d
  have hpow : p ∣ 2 ^ t := by
    have h := (hres.mul_left (2 ^ t - 1)).add_right 1
    simpa only [mul_one, Nat.sub_add_cancel Nat.one_le_two_pow] using
      (h.dvd_iff dvd_rfl).2 hfactor
  have hpTwo : p ∣ 2 := (hp.prime.dvd_pow_iff_dvd (Nat.ne_of_gt ht)).1 hpow
  have hpm : p ∣ 2 ^ m := hpTwo.trans (dvd_pow_self 2 (Nat.ne_of_gt hm))
  exact hp.not_dvd_one ((hmod.dvd_iff dvd_rfl).2 hpm)

end

end MetaMathlibExt
