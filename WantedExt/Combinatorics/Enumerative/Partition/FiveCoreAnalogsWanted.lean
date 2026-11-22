/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import MathlibExt.Data.Set.Density
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Arithmetic identities for analogs of the 5-core partition function

Statements from Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for
Some Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5 (arXiv:2409.02034).

Notation (Section 1 of the paper): `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` is Ramanujan's
general theta function, `φ(q) = f(q, q)`, `ψ(q) = f(q, q^3)`, `f(-q) = f_1` and
`f_k = (q^k; q^k)_∞ = qEulerProduct k`; the substitution `q ↦ -q` is `PowerSeries.rescale (-1)`
and `q ↦ q^k` is `PowerSeries.expand k`. The paper's sequences are defined by their generating
functions `∑ c_5(n) q^n = f_5^5 / f_1`, `∑ ā_5(n) q^n = φ^5(-q^5) / φ(-q)` and
`∑ b̄_5(n) q^n = ψ^5(-q^5) / ψ(-q)`. Identities between quotients of power series are stated
with denominators cleared.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- Ramanujan's general theta function `f(q^i, q^j) = ∑_{n ∈ ℤ} q^{i n(n+1)/2 + j n(n-1)/2}`
as an integer power series. The exponents are positive (`ℕ+`): then every `n` contributing to
`q^m` has `|n| ≤ m`, which the finite search uses (`f(1, q)` and `f(q^0, q^0)` are excluded).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1 (definition of `f(a, b)`). -/
def ramanujanThetaPow (i j : ℕ+) : ℤ⟦X⟧ :=
  mk fun m => (((Finset.Icc (-(m : ℤ)) m).filter fun n =>
    ((i : ℕ) : ℤ) * (n * (n + 1) / 2) + ((j : ℕ) : ℤ) * (n * (n - 1) / 2) = m).card : ℤ)

/-- `c_5(n)`, the coefficients of `f_5^5 / f_1` (the generating function of 5-core
partitions).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation for `∑ c_t(n) q^n` with `t = 5` (OEIS A053723). -/
noncomputable def fiveCoreCount (n : ℕ) : ℤ :=
  coeff n (qEulerProduct 5 ^ 5 * invOfUnit (pentagonalSeries ℤ) 1)

/-- `ā_5(n)`, the coefficients of `φ^5(-q^5) / φ(-q)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (at) (OEIS A368490). -/
noncomputable def phiFiveCoreAnalog (n : ℕ) : ℤ :=
  coeff n (expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 *
    invOfUnit (rescale (-1) (ramanujanThetaPow 1 1)) 1)

/-- `b̄_5(n)`, the coefficients of `ψ^5(-q^5) / ψ(-q)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (bt) (OEIS A368495). -/
noncomputable def psiFiveCoreAnalog (n : ℕ) : ℤ :=
  coeff n (expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 *
    invOfUnit (rescale (-1) (ramanujanThetaPow 1 3)) 1)

/-- The theta series `f(q^i, q^j)` has constant term `1` (only `n = 0` contributes).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1. -/
theorem constantCoeff_ramanujanThetaPow (i j : ℕ+) : constantCoeff (ramanujanThetaPow i j) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ramanujanThetaPow, coeff_mk]
  simp [Finset.filter_singleton]

/-- Generating function of `c_5`: `(∑ c_5(n) q^n) f_1 = f_5^5`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1. -/
theorem mk_fiveCoreCount_mul : mk fiveCoreCount * pentagonalSeries ℤ = qEulerProduct 5 ^ 5 := by
  have h0 : constantCoeff (pentagonalSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
    have := coeff_pentagonalSeries_pentagonal (R := ℤ) 0
    rw [show pentagonal 0 = 0 by simp [pentagonal_def], coeff_zero_eq_constantCoeff_apply] at this
    simpa using this
  have hmk : mk fiveCoreCount = qEulerProduct 5 ^ 5 * invOfUnit (pentagonalSeries ℤ) 1 := by
    ext n; simp [fiveCoreCount]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]

/-- Generating function of `ā_5`: `(∑ ā_5(n) q^n) φ(-q) = φ^5(-q^5)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (at). -/
theorem mk_phiFiveCoreAnalog_mul :
    mk phiFiveCoreAnalog * rescale (-1) (ramanujanThetaPow 1 1) =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 := by
  have h0 : constantCoeff (rescale (-1) (ramanujanThetaPow 1 1)) = ((1 : ℤˣ) : ℤ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ramanujanThetaPow]
    simp
  have hmk : mk phiFiveCoreAnalog =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 *
      invOfUnit (rescale (-1) (ramanujanThetaPow 1 1)) 1 := by
    ext n; simp [phiFiveCoreAnalog]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]

/-- Generating function of `b̄_5`: `(∑ b̄_5(n) q^n) ψ(-q) = ψ^5(-q^5)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (bt). -/
theorem mk_psiFiveCoreAnalog_mul :
    mk psiFiveCoreAnalog * rescale (-1) (ramanujanThetaPow 1 3) =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 := by
  have h0 : constantCoeff (rescale (-1) (ramanujanThetaPow 1 3)) = ((1 : ℤˣ) : ℤ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ramanujanThetaPow]
    simp
  have hmk : mk psiFiveCoreAnalog =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 *
      invOfUnit (rescale (-1) (ramanujanThetaPow 1 3)) 1 := by
    ext n; simp [psiFiveCoreAnalog]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]


local notation "𝔣" => qEulerProduct
local notation "Φ" => ramanujanThetaPow 1 1
local notation "Ψ" => ramanujanThetaPow 1 3

/-- Theorem 2 identities: for every `n ≥ 0`, `ā_5(5n+2) = 4 c_5(5n+1)`,
`ā_5(5n+3) = 4 c_5(5n+2)`, `ā_5(10n+1) = 2 c_5(10n)`, `ā_5(10n+9) = 2 c_5(10n+8)`,
`ā_5(20n+6) = 10 c_5(10n+2)` and `ā_5(20n+14) = 10 c_5(10n+6)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 2 (`jis-2024-24.4.5-thm-2`). -/
public theorem_wanted phiFiveCoreAnalog_eq_fiveCoreCount (n : ℕ) :
    phiFiveCoreAnalog (5 * n + 2) = 4 * fiveCoreCount (5 * n + 1) ∧
      phiFiveCoreAnalog (5 * n + 3) = 4 * fiveCoreCount (5 * n + 2) ∧
      phiFiveCoreAnalog (10 * n + 1) = 2 * fiveCoreCount (10 * n) ∧
      phiFiveCoreAnalog (10 * n + 9) = 2 * fiveCoreCount (10 * n + 8) ∧
      phiFiveCoreAnalog (20 * n + 6) = 10 * fiveCoreCount (10 * n + 2) ∧
      phiFiveCoreAnalog (20 * n + 14) = 10 * fiveCoreCount (10 * n + 6)

/-- Theorem 2 recurrence: for `k ≥ 2` and `n ≥ 0`,
`ā_5(5^k n) = ((5^k - 1)/4) ā_5(5n) - ((5^k - 5)/4) ā_5(n)` (both divisions are exact).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 2 (`jis-2024-24.4.5-thm-2`). -/
public theorem_wanted phiFiveCoreAnalog_five_pow_mul {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    phiFiveCoreAnalog (5 ^ k * n) =
      ((5 ^ k - 1) / 4 : ℤ) * phiFiveCoreAnalog (5 * n) -
        ((5 ^ k - 5) / 4 : ℤ) * phiFiveCoreAnalog n

/-- Corollary 3: `ā_5(20n+6) ≡ ā_5(20n+14) ≡ 0 (mod 10)` and, for `k ≥ 2`,
`4 ā_5(5^k n) ≡ 5 ā_5(n) - ā_5(5n) (mod 5^k)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Corollary 3 (`jis-2024-24.4.5-cor-3`). -/
public theorem_wanted phiFiveCoreAnalog_congruences {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    phiFiveCoreAnalog (20 * n + 6) ≡ 0 [ZMOD 10] ∧
      phiFiveCoreAnalog (20 * n + 14) ≡ 0 [ZMOD 10] ∧
      4 * phiFiveCoreAnalog (5 ^ k * n) ≡ 5 * phiFiveCoreAnalog n - phiFiveCoreAnalog (5 * n)
        [ZMOD 5 ^ k]

/-- Theorem 4, first identity: `b̄_5(4n+3) = 2 b̄_5(2n)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 4 (`jis-2024-24.4.5-thm-4`). -/
public theorem_wanted psiFiveCoreAnalog_four_mul_add_three (n : ℕ) :
    psiFiveCoreAnalog (4 * n + 3) = 2 * psiFiveCoreAnalog (2 * n)

/-- Theorem 4, second identity: for `k ≥ 2`,
`b̄_5(5^k(n+3) - 3) = ((5^k - 1)/4) b̄_5(5n+12) - ((5^k - 5)/4) b̄_5(n)` (exact divisions).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 4 (`jis-2024-24.4.5-thm-4`). -/
public theorem_wanted psiFiveCoreAnalog_five_pow_mul {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    psiFiveCoreAnalog (5 ^ k * (n + 3) - 3) =
      ((5 ^ k - 1) / 4 : ℤ) * psiFiveCoreAnalog (5 * n + 12) -
        ((5 ^ k - 5) / 4 : ℤ) * psiFiveCoreAnalog n

/-- Theorem 5: identities connecting `b̄_5` with `ā_5` and `c_5`, with the halves and quarters
cleared and the convention `b̄_5(-1) = 0` written out for `n = 0`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 5 (`jis-2024-24.4.5-thm-5`). -/
public theorem_wanted psiFiveCoreAnalog_identities (n : ℕ) :
    psiFiveCoreAnalog (4 * n + 1) =
        fiveCoreCount n - 2 * (if n = 0 then 0 else psiFiveCoreAnalog (2 * n - 1)) ∧
      2 * psiFiveCoreAnalog (10 * n) = fiveCoreCount (10 * n + 2) ∧
      psiFiveCoreAnalog (10 * n + 1) = fiveCoreCount (5 * n + 1) ∧
      4 * psiFiveCoreAnalog (10 * n + 2) =
        phiFiveCoreAnalog (2 * n + 1) + 2 * fiveCoreCount (2 * n) ∧
      psiFiveCoreAnalog (10 * n + 3) = fiveCoreCount (5 * n + 2) ∧
      2 * psiFiveCoreAnalog (10 * n + 4) = fiveCoreCount (10 * n + 6) ∧
      psiFiveCoreAnalog (10 * n + 6) = 0 ∧
      psiFiveCoreAnalog (10 * n + 8) = 0 ∧
      psiFiveCoreAnalog (20 * n + 5) = -fiveCoreCount (5 * n + 1) ∧
      2 * psiFiveCoreAnalog (20 * n + 7) =
        phiFiveCoreAnalog (2 * n + 1) + 2 * fiveCoreCount (2 * n) ∧
      psiFiveCoreAnalog (20 * n + 9) = -fiveCoreCount (5 * n + 2) ∧
      psiFiveCoreAnalog (20 * n + 15) = 0 ∧
      psiFiveCoreAnalog (20 * n + 19) = 0

/-- Corollary 6: among the positive integers, `b̄_5(n)` is `0` with lower density at least
`30%`, positive with lower density at least `52%` and negative with lower density at least
`10%` (`Set.lowerDensity` of the corresponding sets of positive integers).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Corollary 6 (`jis-2024-24.4.5-cor-6`). -/
public theorem_wanted psiFiveCoreAnalog_sign_densities :
    3 / 10 ≤ {n : ℕ | 0 < n ∧ psiFiveCoreAnalog n = 0}.lowerDensity ∧
      52 / 100 ≤ {n : ℕ | 0 < n ∧ 0 < psiFiveCoreAnalog n}.lowerDensity ∧
      1 / 10 ≤ {n : ℕ | 0 < n ∧ psiFiveCoreAnalog n < 0}.lowerDensity

/-- Corollary 7: `ā_5(20n+6) = 20 b̄_5(10n)` and `ā_5(20n+14) = 20 b̄_5(10n+4)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Corollary 7 (`jis-2024-24.4.5-cor-7`). -/
public theorem_wanted phiFiveCoreAnalog_eq_twenty_mul_psiFiveCoreAnalog (n : ℕ) :
    phiFiveCoreAnalog (20 * n + 6) = 20 * psiFiveCoreAnalog (10 * n) ∧
      phiFiveCoreAnalog (20 * n + 14) = 20 * psiFiveCoreAnalog (10 * n + 4)

/-- Corollary 8: for `k ≥ 2`, `4 b̄_5(5^k(n+3) - 3) ≡ 5 b̄_5(n) - b̄_5(5n+12) (mod 5^k)`,
and `b̄_5(5^k(20n+18) - 3) ≡ b̄_5(5^k(20n+22) - 3) ≡ 0 (mod (5^k - 1)/4)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Corollary 8 (`jis-2024-24.4.5-cor-8`). -/
public theorem_wanted psiFiveCoreAnalog_congruences {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    4 * psiFiveCoreAnalog (5 ^ k * (n + 3) - 3) ≡
        5 * psiFiveCoreAnalog n - psiFiveCoreAnalog (5 * n + 12) [ZMOD 5 ^ k] ∧
      psiFiveCoreAnalog (5 ^ k * (20 * n + 18) - 3) ≡ 0 [ZMOD (5 ^ k - 1) / 4] ∧
      psiFiveCoreAnalog (5 ^ k * (20 * n + 22) - 3) ≡ 0 [ZMOD (5 ^ k - 1) / 4]

/-- Lemma 9: six theta-function identities, with `f(q) = f_1(-q)`, `χ(-q) = (q; q^2)_∞`,
`χ(q) = χ(-(-q))`, stated with denominators cleared:
`φ^5(q^5)/φ(q) + 4q f^5(q^5)/f(q) = φ(q) φ^3(q^5)`; `φ^2(q) - φ^2(q^5) = 4q χ(q) f_5 f_20`;
`ψ^5(-q^5)/ψ(-q) - ψ^5(q^5)/ψ(q) = 4q^3 ψ^5(q^10)/ψ(q^2) + 2q f_20^5/f_4`;
`ψ^2(q) - q ψ^2(q^5) = f(-q^5) φ(-q^5)/χ(-q) = f(q, q^4) f(q^2, q^3)`;
`f_5^5/f_1 - 4q^3 f_20^5/f_4 = f^5(q^5)/f(q) + 2q f_10^5/f_2`;
`f_2^2/f_1^4 = f_10^2/f_5^4 + 4q f_2 f_10^5/(f_1^3 f_5^5)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Lemma 9 (`jis-2024-24.4.5-lem-9`). -/
public theorem_wanted theta_level_five_identities :
    expand 5 (by norm_num) Φ ^ 5 * rescale (-1) (𝔣 1) +
        4 * X * expand 5 (by norm_num) (rescale (-1) (𝔣 1)) ^ 5 * Φ =
      Φ ^ 2 * expand 5 (by norm_num) Φ ^ 3 * rescale (-1) (𝔣 1) ∧
    Φ ^ 2 - expand 5 (by norm_num) Φ ^ 2 =
      4 * X * rescale (-1) (∏' m : ℕ, (1 - X ^ (2 * m + 1)) : ℤ⟦X⟧) * 𝔣 5 * 𝔣 20 ∧
    expand 5 (by norm_num) (rescale (-1) Ψ) ^ 5 * Ψ * expand 2 (by norm_num) Ψ * 𝔣 4 -
        expand 5 (by norm_num) Ψ ^ 5 * rescale (-1) Ψ * expand 2 (by norm_num) Ψ * 𝔣 4 =
      4 * X ^ 3 * expand 10 (by norm_num) Ψ ^ 5 * rescale (-1) Ψ * Ψ * 𝔣 4 +
        2 * X * 𝔣 20 ^ 5 * rescale (-1) Ψ * Ψ * expand 2 (by norm_num) Ψ ∧
    (Ψ ^ 2 - X * expand 5 (by norm_num) Ψ ^ 2) * (∏' m : ℕ, (1 - X ^ (2 * m + 1)) : ℤ⟦X⟧) =
      𝔣 5 * expand 5 (by norm_num) (rescale (-1) Φ) ∧
    Ψ ^ 2 - X * expand 5 (by norm_num) Ψ ^ 2 = ramanujanThetaPow 1 4 * ramanujanThetaPow 2 3 ∧
    𝔣 5 ^ 5 * 𝔣 4 * rescale (-1) (𝔣 1) * 𝔣 2 -
        4 * X ^ 3 * 𝔣 20 ^ 5 * 𝔣 1 * rescale (-1) (𝔣 1) * 𝔣 2 =
      expand 5 (by norm_num) (rescale (-1) (𝔣 1)) ^ 5 * 𝔣 1 * 𝔣 4 * 𝔣 2 +
        2 * X * 𝔣 10 ^ 5 * 𝔣 1 * 𝔣 4 * rescale (-1) (𝔣 1) ∧
    𝔣 2 ^ 2 * 𝔣 5 ^ 5 = 𝔣 10 ^ 2 * 𝔣 5 * 𝔣 1 ^ 4 + 4 * X * 𝔣 2 * 𝔣 10 ^ 5 * 𝔣 1

/-- Lemma 10, 5-dissections of `φ` and `ψ`:
`φ(q) = φ(q^25) + 2q f(q^15, q^35) + 2q^4 f(q^5, q^45)` and
`ψ(q) = f(q^10, q^15) + q f(q^5, q^20) + q^3 ψ(q^25)`. The 5-dissection of `1/f_1` via the
Rogers–Ramanujan continued fraction is not included.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Lemma 10 (`jis-2024-24.4.5-lem-10`). -/
public theorem_wanted theta_five_dissections :
    Φ = expand 25 (by norm_num) Φ + 2 * X * ramanujanThetaPow 15 35 +
        2 * X ^ 4 * ramanujanThetaPow 5 45 ∧
      Ψ = ramanujanThetaPow 10 15 + X * ramanujanThetaPow 5 20 + X ^ 3 * expand 25 (by norm_num) Ψ

/-- Lemma 11: `c_5(4n+1) = c_5(2n)` and `c_5(5n+4) = 5 c_5(n)`.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Lemma 11 (`jis-2024-24.4.5-lem-11`). -/
public theorem_wanted fiveCoreCount_identities (n : ℕ) :
    fiveCoreCount (4 * n + 1) = fiveCoreCount (2 * n) ∧
      fiveCoreCount (5 * n + 4) = 5 * fiveCoreCount n

end

end MetaMathlibExt
