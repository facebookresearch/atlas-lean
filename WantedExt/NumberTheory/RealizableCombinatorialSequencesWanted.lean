/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.Schroder
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import MathlibExt.Combinatorics.Enumerative.ZagierNumber
public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace MetaMathlibExt

@[expose] public section

/-- A sequence of non-negative integers is almost realizable if some positive integer multiple
of it is realizable (Miska and Ward). Realizability is `MetaMathlibExt.doldRealizable` of the
integer cast: `(μ * a)(n)` is non-negative and divisible by `n` for every `n ≥ 1` (the paper's
Definition 1 (2); the divisor involution `d ↦ n / d` turns the paper's `∑_{d ∣ n} μ(n/d) a(d)`
into `doldRealizable`'s `∑_{d ∣ n} μ(d) a(n/d)`). The value `a 0` is not used.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 3. -/
def IsAlmostRealizableSeq (a : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ doldRealizable fun n => ((m * a n : ℕ) : ℤ)

/-- The zero sequence is almost realizable (by the self-map of the empty set, with `m = 1`).

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 3. -/
theorem isAlmostRealizableSeq_zero : IsAlmostRealizableSeq fun _ => 0 :=
  ⟨1, one_pos, fun n _ => by simp⟩

/-- A realizable sequence is almost realizable (take `m = 1`); for example the binomial-power
sequences `A(n,r,s)` of Theorem 13 (`MetaMathlibExt.binomial_power_sequence_dold_realizable`).

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 3 and Theorem 13. -/
theorem isAlmostRealizableSeq_binomialPowerSeq (r s : ℕ) (hr : 0 < r) :
    IsAlmostRealizableSeq fun n => binomialPowerSeq r s n :=
  ⟨1, one_pos, by simpa using binomial_power_sequence_dold_realizable r s hr⟩

/-- For every `s, t ≥ 0` and `r ≥ 1`, the sequence `(D(n, r, s, t))_{n ≥ 1}` is realizable, with
`D(n,r,s,t) = ∑_k C(n,k)^r C(2k,k)^s C(2(n-k),n-k)^t` (`MetaMathlibExt.dombTypeSum`, Definition 7)
and realizability `MetaMathlibExt.doldRealizable`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Theorem 15 (`jis-2024-24.3.3-thm-15`). -/
public theorem_wanted doldRealizable_dombTypeSum (r s t : ℕ) (hr : 1 ≤ r) :
    doldRealizable fun n => ((dombTypeSum n r s t : ℕ) : ℤ)

/-- The Catalan numbers, the Motzkin numbers, and the large Schröder numbers (Mathlib's
`largeSchroder`, OEIS A006318) are not almost realizable; the Motzkin numbers are
`MetaMathlibExt.motzkinNumber`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Theorem 21 (`jis-2024-24.3.3-thm-21`). -/
public theorem_wanted not_isAlmostRealizableSeq_catalan_motzkin_schroder :
    ¬ IsAlmostRealizableSeq catalan ∧ ¬ IsAlmostRealizableSeq motzkinNumber ∧
      ¬ IsAlmostRealizableSeq Nat.largeSchroder

/-- Helou and Terjanian, prime `p ≥ 5`: for `0 < m < n`,
`C(np, mp) ≡ C(n, m) (mod p^{3 + max(ν_p(m), ν_p(n-m)) + ν_p(C(n,m))})`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 26 (1) (`jis-2024-24.3.3-lem-26`). -/
public theorem_wanted choose_mul_prime_modEq_of_five_le (p n m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 0 < m) (hmn : m < n) :
    (n * p).choose (m * p) ≡ n.choose m
      [MOD p ^ (3 + max (padicValNat p m) (padicValNat p (n - m)) +
        padicValNat p (n.choose m))]

/-- Helou and Terjanian, `p = 3`: for `0 < m < n`,
`C(3n, 3m) ≡ C(n, m) (mod 3^{2 + max(ν_3(m), ν_3(n-m)) + ν_3(C(n,m))})`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 26 (2) (`jis-2024-24.3.3-lem-26`). -/
public theorem_wanted choose_three_mul_modEq (n m : ℕ) (hm : 0 < m) (hmn : m < n) :
    (3 * n).choose (3 * m) ≡ n.choose m
      [MOD 3 ^ (2 + max (padicValNat 3 m) (padicValNat 3 (n - m)) +
        padicValNat 3 (n.choose m))]

/-- Helou and Terjanian, `p = 2`: for `0 < m < n`,
`C(2n, 2m) ≡ C(n, m) (mod 2^{1 + max(ν_2(m), ν_2(n-m)) + ν_2(C(n,m))})`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 26 (3) (`jis-2024-24.3.3-lem-26`). -/
public theorem_wanted choose_two_mul_modEq (n m : ℕ) (hm : 0 < m) (hmn : m < n) :
    (2 * n).choose (2 * m) ≡ n.choose m
      [MOD 2 ^ (1 + max (padicValNat 2 m) (padicValNat 2 (n - m)) +
        padicValNat 2 (n.choose m))]

/-- For a prime `p` dividing `n > 0` and every `λ ≥ 0` with `λ p ≠ n`,
`C(n, λp) ≡ C(n/p, λ) (mod p^{max(ν_p(n), ν_p(n - λp))})`, where `ν_p(n - λp)` is the valuation
of the integer `n - λp`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 27 (`jis-2024-24.3.3-lem-27`). -/
public theorem_wanted choose_mul_prime_modEq_choose_div (n p l : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (hn : 0 < n) (hl : l * p ≠ n) :
    (n.choose (l * p) : ℤ) ≡ ((n / p).choose l : ℤ)
      [ZMOD (p : ℤ) ^ max (padicValNat p n) (padicValInt p ((n : ℤ) - l * p))]

/-- If `b(n) ≥ 0` and `b(n+1) ≥ C b(n)` for all `n ≥ 1`, with a constant `C ≥ 1.221`, then
`(μ * b)(n) ≥ 0` for every `n ≥ 1`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 28 (`jis-2024-24.3.3-lem-28`). -/
public theorem_wanted moebius_conv_nonneg_of_geometric_growth (b : ℕ → ℝ)
    (hb : ∀ n, 1 ≤ n → 0 ≤ b n) (C : ℝ) (hC : (1221 / 1000 : ℝ) ≤ C)
    (hgrowth : ∀ n, 1 ≤ n → C * b n ≤ b (n + 1)) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) * b d

/-- For an integer sequence `(V(n))_{n ≥ 1}`, the congruences
`V(n p^m) ≡ V(n p^{m-1}) (mod p^m)` for all `n, m ≥ 1` and primes `p` hold if and only if `V`
satisfies the Dold condition `(μ * V)(n) ≡ 0 (mod n)` for all `n ≥ 1`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 30 (`jis-2024-24.3.3-lem-30`). -/
public theorem_wanted prime_power_congruence_iff_dold (V : ℕ → ℤ) :
    (∀ n m p : ℕ, 1 ≤ n → 1 ≤ m → p.Prime →
        V (n * p ^ m) ≡ V (n * p ^ (m - 1)) [ZMOD (p : ℤ) ^ m]) ↔
      ∀ n : ℕ, 1 ≤ n →
        (n : ℤ) ∣ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * V d

/-- For `r ≥ 1` and `s, t, u ≥ 0` with `t + u ≥ 1`, the sequence `(T(n,r,s,t,u))_{n ≥ 1}` is
realizable (`MetaMathlibExt.doldRealizable`), where
`T(n,r,s,t,u) = ∑_{k=0}^n C(n,2k)^r C(n+k,k)^s C(2k,k)^t C(2(n-k),n-k)^u`. Added hypothesis
`t + u ≥ 1`: for `t = u = 0`, `(μ * T)(2) = T(2) - T(1) = 3^s` is odd, so the sequence is not
realizable.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Theorem 18 (`jis-2024-24.3.3-thm-18`). -/
public theorem_wanted doldRealizable_evenBinomialTypeSum (r s t u : ℕ) (hr : 1 ≤ r)
    (htu : 1 ≤ t + u) :
    doldRealizable fun n => ((∑ k ∈ Finset.range (n + 1),
      n.choose (2 * k) ^ r * (n + k).choose k ^ s * (2 * k).choose k ^ t *
        (2 * (n - k)).choose (n - k) ^ u : ℕ) : ℤ)

end

end MetaMathlibExt
