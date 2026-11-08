/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct

/-!
# Coefficients of the mock theta functions `v(q)`, `σ(q)`, `λ(q)`

Statements from Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of
Some Mock Theta Functions*, INTEGERS 25 (2025), Article A72.

`f_k = (q^k; q^k)_∞` is `qEulerProduct k`, written `𝔣 k` (the paper's `ℓ_k`). Quotients of
Euler products use `invOfUnit` (every `f_k`, `k ≥ 1`, has constant coefficient `1`);
identities between them are stated with denominators cleared. The paper's restricted
partition functions `b_k^r(n)` and `p̄_r(n)` are, by its equations (7) and (8), the
coefficients of `(f_k / f_1)^r` and `(f_2 / f_1^2)^r`, and are written that way. A
congruence `F ≡ G (mod M)` of power series is stated coefficientwise.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- The eighth-order mock theta function
`v(q) = ∑_{n ≥ 0} q^{(n+1)^2} (-q; q^2)_n / (q; q^2)_{n+1}` as an integer power series. The
`n`th summand has order `(n+1)^2`, so the coefficient of `q^m` only involves the summands
`n ≤ m`, which is how it is computed here.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (4). -/
public noncomputable def mockThetaV : ℤ⟦X⟧ :=
  PowerSeries.mk fun m => coeff m (∑ n ∈ Finset.range (m + 1),
    X ^ ((n + 1) ^ 2) * (∏ k ∈ Finset.range n, (1 + X ^ (2 * k + 1))) *
      invOfUnit (∏ k ∈ Finset.range (n + 1), (1 - X ^ (2 * k + 1))) 1)

/-- The sixth-order mock theta function
`σ(q) = ∑_{n ≥ 0} q^{(n+1)(n+2)/2} (-q; q)_n / (q; q^2)_{n+1}` as an integer power series;
the `n`th summand has order `(n+1)(n+2)/2 > n`, so the coefficient of `q^m` only involves
the summands `n ≤ m`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (2). -/
public noncomputable def mockThetaSigma : ℤ⟦X⟧ :=
  PowerSeries.mk fun m => coeff m (∑ n ∈ Finset.range (m + 1),
    X ^ ((n + 1) * (n + 2) / 2) * (∏ k ∈ Finset.range n, (1 + X ^ (k + 1))) *
      invOfUnit (∏ k ∈ Finset.range (n + 1), (1 - X ^ (2 * k + 1))) 1)

/-- The sixth-order mock theta function
`λ(q) = ∑_{n ≥ 0} (-1)^n q^n (q; q^2)_n / (-q; q)_n` as an integer power series; the `n`th
summand has order `n`, so the coefficient of `q^m` only involves the summands `n ≤ m`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (3). -/
public noncomputable def mockThetaLambda : ℤ⟦X⟧ :=
  PowerSeries.mk fun m => coeff m (∑ n ∈ Finset.range (m + 1),
    (-1) ^ n * X ^ n * (∏ k ∈ Finset.range n, (1 - X ^ (2 * k + 1))) *
      invOfUnit (∏ k ∈ Finset.range n, (1 + X ^ (k + 1))) 1)

/-- Characteristic values `P_v(0) = 0` and `P_v(1) = 1` (`v(q) = q + q^2 + q^3 + ⋯`).

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (4). -/
public theorem coeff_mockThetaV_zero_one :
    coeff 0 mockThetaV = 0 ∧ coeff 1 mockThetaV = 1 := by
  constructor
  · simp [mockThetaV]
  · simp [mockThetaV, Finset.sum_range_succ, coeff_X_pow_mul', pow_succ, mul_assoc]

/-- Characteristic values `P_σ(0) = 0` and `P_σ(1) = 1` (`σ(q) = q + q^2 + 2q^3 + ⋯`).

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (2). -/
public theorem coeff_mockThetaSigma_zero_one :
    coeff 0 mockThetaSigma = 0 ∧ coeff 1 mockThetaSigma = 1 := by
  constructor
  · simp [mockThetaSigma]
  · simp [mockThetaSigma, Finset.sum_range_succ, coeff_X_pow_mul', mul_assoc]

/-- Characteristic values `P_λ(0) = 1` and `P_λ(1) = -1` (`λ(q) = 1 - q + 3q^2 - ⋯`).

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (3). -/
public theorem coeff_mockThetaLambda_zero_one :
    coeff 0 mockThetaLambda = 1 ∧ coeff 1 mockThetaLambda = -1 := by
  constructor
  · simp [mockThetaLambda]
  · have h1 : invOfUnit (1 : ℤ⟦X⟧) 1 = 1 := by
      simpa using mul_invOfUnit (1 : ℤ⟦X⟧) 1 (by simp)
    simp [mockThetaLambda, Finset.sum_range_succ, mul_assoc, coeff_succ_X_mul, h1]

/-- Ramanujan's general theta function at monomial arguments,
`f(ε q^a, ε q^b) = ∑_{m ∈ ℤ} ε^{m^2} q^{a m(m+1)/2 + b m(m-1)/2}` (since
`(εq^a)^{m(m+1)/2} (εq^b)^{m(m-1)/2} = ε^{m^2} q^{a m(m+1)/2 + b m(m-1)/2}`). For
`a + b ≥ 1` the exponent of the `m`th term is at least `|m|(|m|-1)/2`, so the coefficient of
`q^n` only involves `|m| ≤ n + 1`, which is how it is computed here (the definition is
meant for `a + b ≥ 1`). In particular `ψ(q) = f(q, q^3)` and `f(-q) = f(-q, -q^2)`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Section 2 (definition of `f(c, d)`,
Equations (10) and (11)). -/
public def ramanujanThetaMonomial (ε : ℤ) (a b : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ∑ m ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
    if (a : ℤ) * (m * (m + 1) / 2) + (b : ℤ) * (m * (m - 1) / 2) = n then
      ε ^ (m.natAbs ^ 2) else 0

/-- Characteristic values of `ψ(q) = f(q, q^3) = 1 + q + q^3 + ⋯`: the coefficients of `q^0`,
`q^1`, `q^2`, `q^3` are `1, 1, 0, 1`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (10). -/
public theorem coeff_ramanujanThetaMonomial_one_one_three :
    coeff 0 (ramanujanThetaMonomial 1 1 3) = 1 ∧ coeff 1 (ramanujanThetaMonomial 1 1 3) = 1 ∧
      coeff 2 (ramanujanThetaMonomial 1 1 3) = 0 ∧
      coeff 3 (ramanujanThetaMonomial 1 1 3) = 1 := by
  simp only [ramanujanThetaMonomial, coeff_mk]
  decide

/-- Lemma 1: for an odd prime `p`,
`ψ(q) = ∑_{m=0}^{(p-3)/2} q^{(m^2+m)/2} f(q^{(p^2+(2m+1)p)/2}, q^{(p^2-(2m+1)p)/2}) +
q^{(p^2-1)/8} ψ(q^{p^2})`, with `ψ(q) = f(q, q^3)`; furthermore
`(m^2+m)/2 ≢ (p^2-1)/8 (mod p)` for `0 ≤ m ≤ (p-3)/2`. (Quoted by the paper from
Cui and Gu, Theorem 2.1.)

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Lemma 1 (`integers-2025-A72-lem-1`). -/
public theorem_wanted ramanujanPsi_p_dissection (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ramanujanThetaMonomial 1 1 3 =
        ∑ m ∈ Finset.range ((p - 3) / 2 + 1),
          X ^ ((m ^ 2 + m) / 2) *
            ramanujanThetaMonomial 1 ((p ^ 2 + (2 * m + 1) * p) / 2)
              ((p ^ 2 - (2 * m + 1) * p) / 2) +
          X ^ ((p ^ 2 - 1) / 8) * ramanujanThetaMonomial 1 (p ^ 2) (3 * p ^ 2) ∧
      ∀ m ≤ (p - 3) / 2, ¬ (m ^ 2 + m) / 2 ≡ (p ^ 2 - 1) / 8 [MOD p]

/-- Lemma 2: for a prime `p ≥ 5`, with `c = (±p-1)/6` equal to `(p-1)/6` if `p ≡ 1 (mod 6)`
and `(-p-1)/6` if `p ≡ -1 (mod 6)`,
`f_1 = ∑_{t = -(p-1)/2, t ≠ c}^{(p-1)/2} (-1)^t q^{(3t^2+t)/2}
f(-q^{(3p^2+(6t+1)p)/2}, -q^{(3p^2-(6t+1)p)/2}) + (-1)^c q^{(p^2-1)/24} f_{p^2}`;
furthermore `(3t^2+t)/2 ≢ (p^2-1)/24 (mod p)` for those `t ≠ c`. Exponents are integers
(nonnegative for these `t`), converted with `Int.toNat`. (Quoted by the paper from Cui and
Gu, Theorem 2.2.)

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Lemma 2 (`integers-2025-A72-lem-2`). -/
public theorem_wanted eulerProduct_p_dissection (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    let c : ℤ := if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6
    𝔣 1 =
        ∑ t ∈ (Finset.Icc (-(((p : ℤ) - 1) / 2)) (((p : ℤ) - 1) / 2)).erase c,
          (-1) ^ t.natAbs * X ^ ((3 * t ^ 2 + t) / 2).toNat *
            ramanujanThetaMonomial (-1) ((3 * (p : ℤ) ^ 2 + (6 * t + 1) * p) / 2).toNat
              ((3 * (p : ℤ) ^ 2 - (6 * t + 1) * p) / 2).toNat +
          (-1) ^ c.natAbs * X ^ ((p ^ 2 - 1) / 24) * 𝔣 (p ^ 2) ∧
      ∀ t ∈ (Finset.Icc (-(((p : ℤ) - 1) / 2)) (((p : ℤ) - 1) / 2)).erase c,
        ¬ (3 * t ^ 2 + t) / 2 ≡ ((p : ℤ) ^ 2 - 1) / 24 [ZMOD p]

/-- Lemma 3: for an odd prime `p`,
`f_1^3 = ∑_{k=0, k ≠ (p-1)/2}^{p-1} (-1)^k q^{k(k+1)/2}
∑_{n ≥ 0} (-1)^n (2pn+2k+1) q^{pn(pn+2k+1)/2} + p (-1)^{(p-1)/2} q^{(p^2-1)/8} f_{p^2}^3`;
furthermore `(k^2+k)/2 ≢ (p^2-1)/8 (mod p)` for `0 ≤ k ≤ p-1`, `k ≠ (p-1)/2`. The inner
series is written coefficientwise (its `n`th exponent is at least `n`). (Quoted by the paper
from reference [2], Lemma 2.3.)

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Lemma 3 (`integers-2025-A72-lem-3`). -/
public theorem_wanted eulerProduct_cube_p_dissection (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    𝔣 1 ^ 3 =
        ∑ k ∈ (Finset.range p).erase ((p - 1) / 2),
          (-1) ^ k * X ^ (k * (k + 1) / 2) *
            PowerSeries.mk (fun e => ∑ n ∈ Finset.range (e + 1),
              if p * n * (p * n + 2 * k + 1) / 2 = e then
                (-1) ^ n * ((2 * p * n + 2 * k + 1 : ℕ) : ℤ) else 0) +
          (p : ℤ⟦X⟧) * (-1) ^ ((p - 1) / 2) * X ^ ((p ^ 2 - 1) / 8) * 𝔣 (p ^ 2) ^ 3 ∧
      ∀ k ∈ (Finset.range p).erase ((p - 1) / 2),
        ¬ (k ^ 2 + k) / 2 ≡ (p ^ 2 - 1) / 8 [MOD p]

/-- Theorem 1: `∑_{n ≥ 0} P_v(2n+1) q^n = f_4^3/(f_1 f_2)`, stated with the denominator
cleared, where `∑ P_v(n) q^n = v(q)`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 1 (`integers-2025-A72-thm-1`). -/
public theorem_wanted mockThetaV_odd_generatingFunction :
    𝔣 1 * 𝔣 2 * PowerSeries.mk (fun n => coeff (2 * n + 1) mockThetaV) = 𝔣 4 ^ 3

/-- Theorem 2 (i): `P_v(6n+5) ≡ 0 (mod 3)` for all `n ≥ 0`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 2 (i) (`integers-2025-A72-thm-2`). -/
public theorem_wanted mockThetaV_coeff_six_mul_add_five_mod_three (n : ℕ) :
    coeff (6 * n + 5) mockThetaV ≡ 0 [ZMOD 3]

/-- Theorem 2 (ii): for a prime `p ≥ 3` with `(-2/p) = -1`, every `α ≥ 0` and
`1 ≤ j ≤ p - 1`,
`∑_n P_v(2 p^{2α} n + (3 p^{2α} + 1)/4) q^n ≡ ψ(q) ψ(q^2) (mod 2)` and
`P_v(2 p^{2α+2} n + 2 p^{2α+1} j + (3 p^{2α+2} + 1)/4) ≡ 0 (mod 2)`. The product
`ψ(q)ψ(q^2) = f_2 f_4^2 / f_1` (Equation (10)) is used with `f_1` cleared; the division by
`4` is exact since `p^2 ≡ 1 (mod 8)`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 2 (ii), Equations (21) and (22)
(`integers-2025-A72-thm-2`). -/
public theorem_wanted mockThetaV_congruences_mod_two (p α : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hleg : legendreSym p (-2) = -1) :
    (∀ i, coeff i (𝔣 1 * PowerSeries.mk (fun n =>
        coeff (2 * p ^ (2 * α) * n + (3 * p ^ (2 * α) + 1) / 4) mockThetaV)) ≡
      coeff i (𝔣 2 * 𝔣 4 ^ 2) [ZMOD 2]) ∧
    ∀ j n, 1 ≤ j → j ≤ p - 1 →
      coeff (2 * p ^ (2 * α + 2) * n + 2 * p ^ (2 * α + 1) * j + (3 * p ^ (2 * α + 2) + 1) / 4)
        mockThetaV ≡ 0 [ZMOD 2]

/-- Theorem 2 (iii): for a prime `p ≥ 5` with `(-18/p) = -1`, every `α ≥ 0` and
`1 ≤ j ≤ p - 1`,
`∑_n P_v(6 p^{2α} n + (19 p^{2α} + 1)/4) q^n ≡ 3 f_1 f_6^3 (mod 6)` and
`P_v(6 p^{2α+2} n + 6 p^{2α+1} j + (19 p^{2α+2} + 1)/4) ≡ 0 (mod 6)`; the division by `4`
is exact since `p^2 ≡ 1 (mod 8)`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 2 (iii), Equations (23) and (24)
(`integers-2025-A72-thm-2`). -/
public theorem_wanted mockThetaV_congruences_mod_six (p α : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hleg : legendreSym p (-18) = -1) :
    (∀ i, coeff (6 * p ^ (2 * α) * i + (19 * p ^ (2 * α) + 1) / 4) mockThetaV ≡
      coeff i (3 * 𝔣 1 * 𝔣 6 ^ 3) [ZMOD 6]) ∧
    ∀ j n, 1 ≤ j → j ≤ p - 1 →
      coeff (6 * p ^ (2 * α + 2) * n + 6 * p ^ (2 * α + 1) * j +
        (19 * p ^ (2 * α + 2) + 1) / 4) mockThetaV ≡ 0 [ZMOD 6]

/-- Theorem 3: `P_v(2n+1) = ∑_{m ≥ 0} b_4^1(n - m(m+1))`, where `b_4^1(k)` is the
coefficient of `q^k` in `f_4/f_1` (Equation (8)) and vanishes for `k < 0` (the sum runs over
`m(m+1) ≤ n`).

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 3 (`integers-2025-A72-thm-3`). -/
public theorem_wanted mockThetaV_odd_eq_sum_regular (n : ℕ) :
    coeff (2 * n + 1) mockThetaV =
      ∑ m ∈ (Finset.range (n + 1)).filter (fun m => m * (m + 1) ≤ n),
        coeff (n - m * (m + 1)) (𝔣 4 * invOfUnit (𝔣 1) 1)

/-- Theorem 4: `P_v(6n+5) = 3 b_6^3(n) + 3 ∑_{m ≥ 1} (-1)^m b_6^3(n - 2m(3m+1)) +
3 ∑_{m ≥ 1} (-1)^m b_6^3(n - 2m(3m-1))`, where `b_6^3(k)` is the coefficient of `q^k` in
`(f_6/f_1)^3` (Equation (8)) and vanishes for `k < 0` (the sums run over nonnegative
arguments).

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 4 (`integers-2025-A72-thm-4`). -/
public theorem_wanted mockThetaV_six_mul_add_five_eq_sum_regular (n : ℕ) :
    coeff (6 * n + 5) mockThetaV =
      3 * coeff n ((𝔣 6 * invOfUnit (𝔣 1) 1) ^ 3) +
        3 * ∑ m ∈ (Finset.Icc 1 n).filter (fun m => 2 * m * (3 * m + 1) ≤ n),
          (-1) ^ m * coeff (n - 2 * m * (3 * m + 1)) ((𝔣 6 * invOfUnit (𝔣 1) 1) ^ 3) +
        3 * ∑ m ∈ (Finset.Icc 1 n).filter (fun m => 2 * m * (3 * m - 1) ≤ n),
          (-1) ^ m * coeff (n - 2 * m * (3 * m - 1)) ((𝔣 6 * invOfUnit (𝔣 1) 1) ^ 3)

/-- Theorem 5: `∑_{n ≥ 0} P_σ(2n+1) q^n = f_2^2 f_6^2/(f_1^2 f_3)`, stated with the
denominator cleared, where `∑ P_σ(n) q^n = σ(q)`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 5 (`integers-2025-A72-thm-5`). -/
public theorem_wanted mockThetaSigma_odd_generatingFunction :
    𝔣 1 ^ 2 * 𝔣 3 * PowerSeries.mk (fun n => coeff (2 * n + 1) mockThetaSigma) =
      𝔣 2 ^ 2 * 𝔣 6 ^ 2

/-- Theorem 6: for a prime `p ≥ 5` with `(-2/p) = -1`, every `α ≥ 0` and `1 ≤ j ≤ p - 1`,
`∑_n P_σ(2 p^{2α} n + (11 p^{2α} + 1)/12) q^n ≡ f_2 ψ(q^3) (mod 2)` and
`P_σ(2 p^{2α+2} n + 2 p^{2α+1} j + (11 p^{2α+2} + 1)/12) ≡ 0 (mod 2)`. The product
`f_2 ψ(q^3) = f_2 f_6^2 / f_3` (Equation (10)) is used with `f_3` cleared; the division by
`12` is exact since `p^2 ≡ 1 (mod 24)`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 6 (`integers-2025-A72-thm-6`). -/
public theorem_wanted mockThetaSigma_congruences_mod_two (p α : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hleg : legendreSym p (-2) = -1) :
    (∀ i, coeff i (𝔣 3 * PowerSeries.mk (fun n =>
        coeff (2 * p ^ (2 * α) * n + (11 * p ^ (2 * α) + 1) / 12) mockThetaSigma)) ≡
      coeff i (𝔣 2 * 𝔣 6 ^ 2) [ZMOD 2]) ∧
    ∀ j n, 1 ≤ j → j ≤ p - 1 →
      coeff (2 * p ^ (2 * α + 2) * n + 2 * p ^ (2 * α + 1) * j +
        (11 * p ^ (2 * α + 2) + 1) / 12) mockThetaSigma ≡ 0 [ZMOD 2]

/-- Theorem 7: `P_σ(2n+1) = ∑_{m ≥ 0} b_2^2(n - (3m^2+3m)/2)`, where `b_2^2(k)` is the
coefficient of `q^k` in `(f_2/f_1)^2` (Equation (8)) and vanishes for `k < 0`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 7 (`integers-2025-A72-thm-7`). -/
public theorem_wanted mockThetaSigma_odd_eq_sum_regular (n : ℕ) :
    coeff (2 * n + 1) mockThetaSigma =
      ∑ m ∈ (Finset.range (n + 1)).filter (fun m => (3 * m ^ 2 + 3 * m) / 2 ≤ n),
        coeff (n - (3 * m ^ 2 + 3 * m) / 2) ((𝔣 2 * invOfUnit (𝔣 1) 1) ^ 2)

/-- Theorem 8: `P_λ(2n) = b_2^3(n) + 2 ∑_{k ≥ 1} (-1)^k b_2^3(n - 3k^2)`, where `b_2^3(m)` is
the coefficient of `q^m` in `(f_2/f_1)^3` (Equation (8)) and vanishes for `m < 0`, and
`∑ P_λ(n) q^n = λ(q)`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 8 (`integers-2025-A72-thm-8`). -/
public theorem_wanted mockThetaLambda_even_eq_sum_regular (n : ℕ) :
    coeff (2 * n) mockThetaLambda =
      coeff n ((𝔣 2 * invOfUnit (𝔣 1) 1) ^ 3) +
        2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 3 * k ^ 2 ≤ n),
          (-1) ^ k * coeff (n - 3 * k ^ 2) ((𝔣 2 * invOfUnit (𝔣 1) 1) ^ 3)

/-- Theorem 9: `P_λ(6n+2) = 3 ∑_{m ≥ 0} (-1)^m (2m+1) p̄_3(n - 3m(m+1)/2) +
6 ∑_{m ≥ 0} ∑_{k ≥ 1} (-1)^{m+k} (2m+1) p̄_3(n - 3k^2 - 3m(m+1)/2)`, where `p̄_3(j)` is the
coefficient of `q^j` in `(f_2/f_1^2)^3` (Equation (7)) and vanishes for `j < 0`.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 9 (`integers-2025-A72-thm-9`). -/
public theorem_wanted mockThetaLambda_six_mul_add_two_eq_sum_overpartition (n : ℕ) :
    coeff (6 * n + 2) mockThetaLambda =
      3 * ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 3 * m * (m + 1) / 2 ≤ n),
          (-1) ^ m * (2 * m + 1 : ℤ) *
            coeff (n - 3 * m * (m + 1) / 2) ((𝔣 2 * invOfUnit (𝔣 1 ^ 2) 1) ^ 3) +
        6 * ∑ m ∈ Finset.range (n + 1), ∑ k ∈ (Finset.Icc 1 n).filter
            (fun k => 3 * k ^ 2 + 3 * m * (m + 1) / 2 ≤ n),
          (-1) ^ (m + k) * (2 * m + 1 : ℤ) *
            coeff (n - 3 * k ^ 2 - 3 * m * (m + 1) / 2) ((𝔣 2 * invOfUnit (𝔣 1 ^ 2) 1) ^ 3)

end

end MetaMathlibExt
