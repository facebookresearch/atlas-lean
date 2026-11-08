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

/-- A Sierpiński number: an odd `k` such that `k·2^n + 1` is composite for every `n ≥ 1`.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, abstract and Section 1. -/
public def IsSierpinskiNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ (k * 2 ^ n + 1).Prime

/-- A Riesel number: an odd `k` such that `k·2^n - 1` is composite for every `n ≥ 1`.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, abstract and Section 1. -/
public def IsRieselNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ (k * 2 ^ n - 1).Prime

/-- `1` is not a Sierpiński number: `1·2 + 1 = 3` is prime.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 1. -/
public theorem not_isSierpinskiNumber_one : ¬ IsSierpinskiNumber 1 := fun h =>
  h.2 1 le_rfl (by simpa using Nat.prime_three)

/-- `1` is not a Riesel number: `1·2^2 - 1 = 3` is prime.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 1. -/
public theorem not_isRieselNumber_one : ¬ IsRieselNumber 1 := fun h =>
  h.2 2 (by norm_num) (by simpa using Nat.prime_three)

/-- The `b`-repstring `k_b^{(z;t)} = k (b^{(z+ℓ)t} - 1)/(b^{z+ℓ} - 1)`, `ℓ` the number of base-`b`
digits of `k`; `repstring b k 0 t` is the repinteger `k_b^{(t)}`.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Sections 1 and 4. -/
public def repstring (b k z t : ℕ) : ℕ :=
  k * (b ^ ((z + (Nat.digits b k).length) * t) - 1) / (b ^ (z + (Nat.digits b k).length) - 1)

/-- The paper's example: `1001001` is the repstring with `b = 10`, `k = 1`, `z = 2`, `t = 3`.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 4. -/
public theorem repstring_ten_one_two_three : repstring 10 1 2 3 = 1001001 := by
  norm_num [repstring]

/-- The `2`-repunit with three digits is `7`.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 1. -/
public theorem repstring_two_one_zero_three : repstring 2 1 0 3 = 7 := by
  norm_num [repstring]

/-- Covering data `{(r_j, m_j, p_j)}` producing `k` as a Sierpiński number by the covering
system method: the classes `r_j mod m_j` cover `ℤ`, the `p_j` are distinct primes,
`p_j ∣ 2^{m_j} - 1` with `m_j ≥ 1`, and `p_j ∣ k·2^{r_j} + 1` (that is, `k ≡ -2^{-r_j}`).

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 2, Equation (2). -/
public def IsSierpinskiCoveringData (k : ℕ) (S : Finset (ℕ × ℕ × ℕ)) : Prop :=
  Int.IsCoveringSystem (S.image fun s => ((s.1 : ℤ), s.2.1)) ∧
    Set.InjOn (fun s : ℕ × ℕ × ℕ => s.2.2) (S : Set (ℕ × ℕ × ℕ)) ∧
    ∀ s ∈ S, 1 ≤ s.2.1 ∧ s.2.2.Prime ∧ s.2.2 ∣ 2 ^ s.2.1 - 1 ∧ s.2.2 ∣ k * 2 ^ s.1 + 1

/-- Covering data `{(r_j, m_j, p_j)}` producing `k` as a Riesel number by the covering system
method: as for `IsSierpinskiCoveringData`, with `p_j ∣ k·2^{r_j} - 1` (that is, `k ≡ 2^{-r_j}`).

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 2, Equation (3). -/
public def IsRieselCoveringData (k : ℕ) (S : Finset (ℕ × ℕ × ℕ)) : Prop :=
  Int.IsCoveringSystem (S.image fun s => ((s.1 : ℤ), s.2.1)) ∧
    Set.InjOn (fun s : ℕ × ℕ × ℕ => s.2.2) (S : Set (ℕ × ℕ × ℕ)) ∧
    ∀ s ∈ S, 1 ≤ s.2.1 ∧ s.2.2.Prime ∧ s.2.2 ∣ 2 ^ s.2.1 - 1 ∧ s.2.2 ∣ k * 2 ^ s.1 - 1

/-- Empty data never covers `ℤ`.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 2. -/
public theorem not_isSierpinskiCoveringData_empty (k : ℕ) : ¬ IsSierpinskiCoveringData k ∅ :=
  fun h => by simpa using h.1 0

/-- Empty data never covers `ℤ`.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Section 2. -/
public theorem not_isRieselCoveringData_empty (k : ℕ) : ¬ IsRieselCoveringData k ∅ :=
  fun h => by simpa using h.1 0

/-- **Theorem 3.2.** The covering system method cannot produce a `2`-repdigit
`2^t - 1` (`t ≥ 1`) as a Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.2
(`integers-2026-A12-thm-3-2`). -/
public theorem_wanted not_isSierpinskiCoveringData_two_pow_sub_one {t : ℕ} (ht : 1 ≤ t)
    (S : Finset (ℕ × ℕ × ℕ)) : ¬ IsSierpinskiCoveringData (2 ^ t - 1) S

/-- **Theorem 3.3.** If `k` is a Sierpiński number produced by the covering system method, then
for every `b ≥ 2` there are infinitely many `t ≥ 1` with `k_b^{(t)}` a Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.3
(`integers-2026-A12-thm-3-3`). -/
public theorem_wanted infinite_sierpinski_repintegers {k : ℕ} (hk : IsSierpinskiNumber k)
    {S : Finset (ℕ × ℕ × ℕ)} (hS : IsSierpinskiCoveringData k S) {b : ℕ} (hb : 2 ≤ b) :
    {t : ℕ | 1 ≤ t ∧ IsSierpinskiNumber (repstring b k 0 t)}.Infinite

/-- **Theorem 3.4.** If `k` is a Riesel number produced by the covering system method, then for
every `b ≥ 2` there are infinitely many `t ≥ 1` with `k_b^{(t)}` a Riesel number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.4 (stated in record
`integers-2026-A12-thm-3-3`). -/
public theorem_wanted infinite_riesel_repintegers {k : ℕ} (hk : IsRieselNumber k)
    {S : Finset (ℕ × ℕ × ℕ)} (hS : IsRieselCoveringData k S) {b : ℕ} (hb : 2 ≤ b) :
    {t : ℕ | 1 ≤ t ∧ IsRieselNumber (repstring b k 0 t)}.Infinite

/-- **Theorem 3.5.** For `t ≡ 25 (mod 56)`, `18107_2^{(t)}` is a Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.5
(`integers-2026-A12-thm-3-5`). -/
public theorem_wanted isSierpinskiNumber_repstring_18107 {t : ℕ} (ht : t ≡ 25 [MOD 56]) :
    IsSierpinskiNumber (repstring 2 18107 0 t)

/-- **Theorem 3.6.** For `t ≡ 31 (mod 56)`, `18107_2^{(t)}` is a Riesel number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.6
(`integers-2026-A12-thm-3-6`). -/
public theorem_wanted isRieselNumber_repstring_18107 {t : ℕ} (ht : t ≡ 31 [MOD 56]) :
    IsRieselNumber (repstring 2 18107 0 t)

/-- **Corollary 3.7.** For every `b > 78557` there are infinitely many `b`-repdigit Sierpiński
numbers.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.7
(`integers-2026-A12-cor-3-7`). -/
public theorem_wanted infinite_sierpinski_repdigits {b : ℕ} (hb : 78557 < b) :
    {N : ℕ | ∃ k t : ℕ, 1 ≤ k ∧ k < b ∧ 1 ≤ t ∧ N = repstring b k 0 t ∧
      IsSierpinskiNumber N}.Infinite

/-- **Corollary 3.8.** For every `b > 509203` there are infinitely many `b`-repdigit Riesel
numbers.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.8
(`integers-2026-A12-cor-3-8`). -/
public theorem_wanted infinite_riesel_repdigits {b : ℕ} (hb : 509203 < b) :
    {N : ℕ | ∃ k t : ℕ, 1 ≤ k ∧ k < b ∧ 1 ≤ t ∧ N = repstring b k 0 t ∧
      IsRieselNumber N}.Infinite

/-- **Theorem 3.9.** If `b ≡ 87 (mod 11184810)` and `t ≡ 59 (mod 120)`, then `41_b^{(t)}` is a
Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.9
(`integers-2026-A12-thm-3-9`). -/
public theorem_wanted isSierpinskiNumber_repstring_41 {b t : ℕ} (hb : b ≡ 87 [MOD 11184810])
    (ht : t ≡ 59 [MOD 120]) : IsSierpinskiNumber (repstring b 41 0 t)

/-- **Theorem 3.10.** If `b ≡ 180 (mod 11184810)` and `t ≡ 171 (mod 240)`, then `101_b^{(t)}` is
a Riesel number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.10
(`integers-2026-A12-thm-3-10`). -/
public theorem_wanted isRieselNumber_repstring_101 {b t : ℕ} (hb : b ≡ 180 [MOD 11184810])
    (ht : t ≡ 171 [MOD 240]) : IsRieselNumber (repstring b 101 0 t)

/-- **Theorem 3.11.** For `1 ≤ j ≤ τ` let `p_j` be a primitive prime divisor of `2^{2^j} - 1`, and
let `q ≠ p_τ` be another primitive prime divisor of `2^{2^τ} - 1`. Put `ℓ_j = 1` if
`b ≡ 0 (mod p_j)`, `ℓ_j = p_j` if `b ≡ 1 (mod p_j)`, `ℓ_j = ord_{p_j}(b)` otherwise, and
`L = lcm(2, ℓ_1, …, ℓ_τ)`. If `b > 2`, `q ∤ b`, and either (i) `b ≡ 1 (mod q)` and `q ∤ L`, or
(ii) `b ≢ 1 (mod q)` and some `t ≡ 1 (mod L)` has `(b^t - 1)/(b - 1) ≡ -1 (mod q)`, then there
are infinitely many `b`-repunit Sierpiński numbers.

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

/-- **Corollary 3.12.** If `b > 2`, `b ≡ 𝔟 (mod 641)` for some `𝔟 ∈ {1, 147, 265, 378}`, and
`b ≢ 1 (mod 5)`, there are infinitely many `b`-repunit Sierpiński numbers.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.12
(`integers-2026-A12-cor-3-12`). -/
public theorem_wanted infinite_sierpinski_repunits_mod_641 {b : ℕ} (hb : 2 < b)
    (h641 : ∃ c ∈ ({1, 147, 265, 378} : Finset ℕ), b ≡ c [MOD 641]) (h5 : ¬ b ≡ 1 [MOD 5]) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsSierpinskiNumber N}.Infinite

/-- **Theorem 3.13.** For `1 ≤ j ≤ τ` let `p_j` be a primitive prime divisor of `2^{2^j} - 1`,
`q ≠ p_τ` another primitive prime divisor of `2^{2^τ} - 1`, and `P = p_1 ⋯ p_τ`. If `b > 2`,
`b ≡ 1 (mod P)`, and (i) `b ≡ 0 (mod q)`, or (ii) `b ≡ 1 (mod q)`, or (iii) `b ≢ 0, 1 (mod q)` and
`gcd(P, ord_q(b)) = 1`, then there are infinitely many `b`-repunit Riesel numbers.

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

/-- **Corollary 3.14.** If `b ≡ 16518444216571 (mod 18446744073709551615)`, there are infinitely
many `b`-repunit Riesel numbers.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.14
(`integers-2026-A12-cor-3-14`). -/
public theorem_wanted infinite_riesel_repunits_mod_two_pow_64_sub_one {b : ℕ}
    (hb : b ≡ 16518444216571 [MOD 18446744073709551615]) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsRieselNumber N}.Infinite

/-- **Theorem 4.3.** If `t ≡ 131` or `t ≡ 1361 (mod 2730)`, then the `2`-repstring
`659_2^{(2;t)}` is a Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 4.3
(`integers-2026-A12-thm-4-3`). -/
public theorem_wanted isSierpinskiNumber_repstring_659 {t : ℕ}
    (ht : t ≡ 131 [MOD 2730] ∨ t ≡ 1361 [MOD 2730]) : IsSierpinskiNumber (repstring 2 659 2 t)

/-- **Theorem 4.4.** If `t ≡ 1369` or `t ≡ 2599 (mod 2730)`, then the `2`-repstring
`659_2^{(2;t)}` is a Riesel number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 4.4
(`integers-2026-A12-thm-4-4`). -/
public theorem_wanted isRieselNumber_repstring_659 {t : ℕ}
    (ht : t ≡ 1369 [MOD 2730] ∨ t ≡ 2599 [MOD 2730]) : IsRieselNumber (repstring 2 659 2 t)

/-- **Theorem 4.6.** For `k, 𝔱, w ≥ 1` and `z ≥ 0`: one fixed set of covering data produces
`k_2^{(z;t)}` as a Sierpiński number by the covering system method for every `t ≥ 1` with
`t ≡ 𝔱 (mod w)` if and only if one fixed set of covering data produces `k_2^{(z;t')}` as a Riesel
number for every `t' ≥ 1` with `t' ≡ -𝔱 (mod w)`.

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
