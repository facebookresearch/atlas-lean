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

/-- **The eighth-order mock theta function $v(q)$.** The mock theta function
$v(q) = \sum_{n \ge 0} q^{(n+1)^2} (-q; q^2)_n / (q; q^2)_{n+1}$, where
$(-q; q^2)_n = \prod_{k=0}^{n-1} (1 + q^{2k+1})$ and
$(q; q^2)_{n+1} = \prod_{k=0}^{n} (1 - q^{2k+1})$, is taken as a power series in $q$ with integer
coefficients.

The $n$th summand has order $(n+1)^2$, so the coefficient of $q^m$ only involves the summands
with $n \le m$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (4). -/
public noncomputable def mockThetaV : ℤ⟦X⟧ :=
  PowerSeries.mk fun m => coeff m (∑ n ∈ Finset.range (m + 1),
    X ^ ((n + 1) ^ 2) * (∏ k ∈ Finset.range n, (1 + X ^ (2 * k + 1))) *
      invOfUnit (∏ k ∈ Finset.range (n + 1), (1 - X ^ (2 * k + 1))) 1)

/-- **The sixth-order mock theta function $\sigma(q)$.** The mock theta function
$\sigma(q) = \sum_{n \ge 0} q^{(n+1)(n+2)/2} (-q; q)_n / (q; q^2)_{n+1}$, where
$(-q; q)_n = \prod_{k=1}^{n} (1 + q^k)$ and $(q; q^2)_{n+1} = \prod_{k=0}^{n} (1 - q^{2k+1})$, is
taken as a power series in $q$ with integer coefficients.

The $n$th summand has order $(n+1)(n+2)/2 > n$, so the coefficient of $q^m$ only involves the
summands with $n \le m$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (2). -/
public noncomputable def mockThetaSigma : ℤ⟦X⟧ :=
  PowerSeries.mk fun m => coeff m (∑ n ∈ Finset.range (m + 1),
    X ^ ((n + 1) * (n + 2) / 2) * (∏ k ∈ Finset.range n, (1 + X ^ (k + 1))) *
      invOfUnit (∏ k ∈ Finset.range (n + 1), (1 - X ^ (2 * k + 1))) 1)

/-- **The sixth-order mock theta function $\lambda$.** With
$(a; b)_n = \prod_{k=0}^{n-1} (1 - a b^k)$, the mock theta function $\lambda$ is the integer
power series
$$
\lambda(q) = \sum_{n \ge 0} \frac{(-1)^n q^n (q; q^2)_n}{(-q; q)_n}.
$$
The $n$th summand has order $n$, so the coefficient of $q^m$ only involves the summands with
$n \le m$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (3). -/
public noncomputable def mockThetaLambda : ℤ⟦X⟧ :=
  PowerSeries.mk fun m => coeff m (∑ n ∈ Finset.range (m + 1),
    (-1) ^ n * X ^ n * (∏ k ∈ Finset.range n, (1 - X ^ (2 * k + 1))) *
      invOfUnit (∏ k ∈ Finset.range n, (1 + X ^ (k + 1))) 1)

/-- **First coefficients of the mock theta function $v$.** Write
$v(q) = \sum_{n \ge 0} P_v(n) q^n$ for the eighth-order mock theta function $v$. Then
$P_v(0) = 0$ and $P_v(1) = 1$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (4). -/
public theorem coeff_mockThetaV_zero_one :
    coeff 0 mockThetaV = 0 ∧ coeff 1 mockThetaV = 1 := by
  constructor
  · simp [mockThetaV]
  · simp [mockThetaV, Finset.sum_range_succ, coeff_X_pow_mul', pow_succ, mul_assoc]

/-- **First coefficients of the mock theta function $\sigma$.** Write
$\sigma(q) = \sum_{n \ge 0} P_\sigma(n) q^n$ for the sixth-order mock theta function $\sigma$.
Then $P_\sigma(0) = 0$ and $P_\sigma(1) = 1$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (2). -/
public theorem coeff_mockThetaSigma_zero_one :
    coeff 0 mockThetaSigma = 0 ∧ coeff 1 mockThetaSigma = 1 := by
  constructor
  · simp [mockThetaSigma]
  · simp [mockThetaSigma, Finset.sum_range_succ, coeff_X_pow_mul', mul_assoc]

/-- **First coefficients of the mock theta function $\lambda$.** Write
$\lambda(q) = \sum_{n \ge 0} P_\lambda(n) q^n$ for the sixth-order mock theta function $\lambda$.
Then $P_\lambda(0) = 1$ and $P_\lambda(1) = -1$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (3). -/
public theorem coeff_mockThetaLambda_zero_one :
    coeff 0 mockThetaLambda = 1 ∧ coeff 1 mockThetaLambda = -1 := by
  constructor
  · simp [mockThetaLambda]
  · have h1 : invOfUnit (1 : ℤ⟦X⟧) 1 = 1 := by
      simpa using mul_invOfUnit (1 : ℤ⟦X⟧) 1 (by simp)
    simp [mockThetaLambda, Finset.sum_range_succ, mul_assoc, coeff_succ_X_mul, h1]

/-- **Ramanujan's theta function at monomial arguments.** For an integer $\varepsilon$ and natural
numbers $a$ and $b$, $f(\varepsilon q^a, \varepsilon q^b)$ is the integer power series in $q$
whose coefficient of $q^n$ is the sum of $\varepsilon^{m^2}$ over the integers $m$ with
$|m| \le n + 1$ and $a \cdot m(m+1)/2 + b \cdot m(m-1)/2 = n$.

When $a + b \ge 1$ the exponent $a \cdot m(m+1)/2 + b \cdot m(m-1)/2$ is at least
$|m|(|m|-1)/2$, so the bound $|m| \le n + 1$ excludes no term and this is Ramanujan's
$f(c, d) = \sum_{m \in \mathbb{Z}} c^{m(m+1)/2} d^{m(m-1)/2}$ at $c = \varepsilon q^a$ and
$d = \varepsilon q^b$; the definition is meant for $a + b \ge 1$. Special cases are
$\psi(q) = f(q, q^3)$ and $f(-q) = f(-q, -q^2)$, which equals
$(q; q)_\infty = \prod_{k \ge 1} (1 - q^k)$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Section 2 (definition of `f(c, d)`,
Equations (10) and (11)). -/
public def ramanujanThetaMonomial (ε : ℤ) (a b : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ∑ m ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
    if (a : ℤ) * (m * (m + 1) / 2) + (b : ℤ) * (m * (m - 1) / 2) = n then
      ε ^ (m.natAbs ^ 2) else 0

/-- **First coefficients of Ramanujan's theta function $\psi$.** Let
$\psi(q) = f(q, q^3) = \sum_{m \in \mathbb{Z}} q^{m(m+1)/2 + 3m(m-1)/2}$, where $f$ is
Ramanujan's general theta function. The coefficients of $q^0$, $q^1$, $q^2$, $q^3$ in $\psi(q)$
are $1$, $1$, $0$, $1$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Equation (10). -/
public theorem coeff_ramanujanThetaMonomial_one_one_three :
    coeff 0 (ramanujanThetaMonomial 1 1 3) = 1 ∧ coeff 1 (ramanujanThetaMonomial 1 1 3) = 1 ∧
      coeff 2 (ramanujanThetaMonomial 1 1 3) = 0 ∧
      coeff 3 (ramanujanThetaMonomial 1 1 3) = 1 := by
  simp only [ramanujanThetaMonomial, coeff_mk]
  decide

/-- **The p-dissection of Ramanujan's psi function.** Let $p$ be an odd prime, let $f(c, d)$ be
Ramanujan's theta function and $\psi(q) = f(q, q^3)$. Then, as integer power series,
$\psi(q) = \sum_{m=0}^{(p-3)/2} q^{(m^2+m)/2} f(q^{(p^2+(2m+1)p)/2}, q^{(p^2-(2m+1)p)/2}) +
q^{(p^2-1)/8} f(q^{p^2}, q^{3p^2})$, where the last factor is $\psi(q^{p^2})$. Moreover
$(m^2+m)/2 \not\equiv (p^2-1)/8 \pmod p$ for every integer $m$ with $0 \le m \le (p-3)/2$.

The paper quotes this from Cui and Gu, Theorem 2.1.

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

/-- **The $p$-dissection of $f_1$.** Let $p \ge 5$ be a prime, let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for $k \ge 1$, and let
$f(a, b) = \sum_{m \in \mathbb{Z}} a^{m(m+1)/2} b^{m(m-1)/2}$ be Ramanujan's general theta
function. Put $c = (p-1)/6$ if $p \equiv 1 \pmod 6$ and $c = (-p-1)/6$ otherwise. Then, as
integer power series,
$$
f_1 = \sum_{t=-(p-1)/2,\ t \ne c}^{(p-1)/2} (-1)^t q^{(3t^2+t)/2}
f\bigl(-q^{(3p^2+(6t+1)p)/2}, -q^{(3p^2-(6t+1)p)/2}\bigr) +
(-1)^c q^{(p^2-1)/24} f_{p^2}.
$$
Moreover, $(3t^2 + t)/2 \not\equiv (p^2 - 1)/24 \pmod p$ for every integer $t$ with
$-(p-1)/2 \le t \le (p-1)/2$ and $t \ne c$.

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

/-- **The $p$-dissection of $f_1^3$.** Let $p$ be an odd prime and, for $k \ge 1$, let
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Then, as integer power series,
$$
f_1^3 = \sum_{k=0,\ k \ne (p-1)/2}^{p-1} (-1)^k q^{k(k+1)/2}
\sum_{n \ge 0} (-1)^n (2pn + 2k + 1) q^{pn(pn+2k+1)/2} +
p (-1)^{(p-1)/2} q^{(p^2-1)/8} f_{p^2}^3.
$$
Moreover, $(k^2 + k)/2 \not\equiv (p^2 - 1)/8 \pmod p$ for every integer $k$ with
$0 \le k \le p - 1$ and $k \ne (p-1)/2$.

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

/-- **Generating function for the odd-indexed coefficients of $v(q)$.** Let $P_v(n)$ be the
coefficient of $q^n$ in the eighth-order mock theta function $v(q)$, and for $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Then, as integer power series,
$f_1 f_2 \sum_{n \ge 0} P_v(2n+1) q^n = f_4^3$, that is,
$\sum_{n \ge 0} P_v(2n+1) q^n = f_4^3 / (f_1 f_2)$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 1 (`integers-2025-A72-thm-1`). -/
public theorem_wanted mockThetaV_odd_generatingFunction :
    𝔣 1 * 𝔣 2 * PowerSeries.mk (fun n => coeff (2 * n + 1) mockThetaV) = 𝔣 4 ^ 3

/-- **The coefficients of $q^{6n+5}$ in $v(q)$ are divisible by 3.** Let $P_v(n)$ be the
coefficient of $q^n$ in the eighth-order mock theta function $v(q)$. Then
$P_v(6n+5) \equiv 0 \pmod 3$ for every $n \ge 0$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 2 (i) (`integers-2025-A72-thm-2`). -/
public theorem_wanted mockThetaV_coeff_six_mul_add_five_mod_three (n : ℕ) :
    coeff (6 * n + 5) mockThetaV ≡ 0 [ZMOD 3]

/-- **Infinite family of congruences modulo 2 for $v(q)$.** Let $P_v(n)$ be the coefficient of
$q^n$ in the eighth-order mock theta function $v(q)$, and for $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Let $p \ge 3$ be a prime whose Legendre symbol
$\left(\frac{-2}{p}\right)$ equals $-1$, and let $\alpha \ge 0$ be an integer. Then the integer
power series $f_1 \sum_{n \ge 0} P_v\bigl(2 p^{2\alpha} n + (3 p^{2\alpha} + 1)/4\bigr) q^n$ and
$f_2 f_4^2$ have congruent coefficients modulo $2$. Moreover, for every $n \ge 0$ and every $j$
with $1 \le j \le p - 1$,
$P_v\bigl(2 p^{2\alpha+2} n + 2 p^{2\alpha+1} j + (3 p^{2\alpha+2} + 1)/4\bigr) \equiv 0 \pmod 2$.

The divisions by $4$ are exact since $p^2 \equiv 1 \pmod 8$. Since $f_1$ has an inverse with
integer coefficients, the first congruence says that
$\sum_{n \ge 0} P_v(2 p^{2\alpha} n + (3 p^{2\alpha} + 1)/4) q^n \equiv \psi(q) \psi(q^2) \pmod 2$,
where $\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$, so that $\psi(q) \psi(q^2) = f_2 f_4^2 / f_1$.

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

/-- **Infinite family of congruences modulo 6 for $v(q)$.** Let $P_v(n)$ be the coefficient of
$q^n$ in the eighth-order mock theta function $v(q)$, and for $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Let $p \ge 5$ be a prime whose Legendre symbol
$\left(\frac{-18}{p}\right)$ equals $-1$, and let $\alpha \ge 0$ be an integer. Then for every
$n \ge 0$, $P_v\bigl(6 p^{2\alpha} n + (19 p^{2\alpha} + 1)/4\bigr)$ is congruent modulo $6$ to
the coefficient of $q^n$ in $3 f_1 f_6^3$. Moreover, for every $n \ge 0$ and every $j$ with
$1 \le j \le p - 1$,
$P_v\bigl(6 p^{2\alpha+2} n + 6 p^{2\alpha+1} j + (19 p^{2\alpha+2} + 1)/4\bigr) \equiv 0 \pmod 6$.

The divisions by $4$ are exact since $p^2 \equiv 1 \pmod 8$.

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

/-- **Sum formula for the odd-indexed coefficients of $v(q)$.** Let $P_v(n)$ be the coefficient
of $q^n$ in the eighth-order mock theta function $v(q)$, for $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, and let $b_4^1(k)$ be the coefficient of $q^k$ in the
integer power series $f_4 / f_1$. Then for every $n \ge 0$,
$P_v(2n+1) = \sum_{m \ge 0,\ m(m+1) \le n} b_4^1\bigl(n - m(m+1)\bigr)$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 3 (`integers-2025-A72-thm-3`). -/
public theorem_wanted mockThetaV_odd_eq_sum_regular (n : ℕ) :
    coeff (2 * n + 1) mockThetaV =
      ∑ m ∈ (Finset.range (n + 1)).filter (fun m => m * (m + 1) ≤ n),
        coeff (n - m * (m + 1)) (𝔣 4 * invOfUnit (𝔣 1) 1)

/-- **Sum formula for the coefficients of $q^{6n+5}$ in $v(q)$.** Let $P_v(n)$ be the
coefficient of $q^n$ in the eighth-order mock theta function $v(q)$, for $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, and let $b_6^3(k)$ be the coefficient of $q^k$ in the
integer power series $(f_6 / f_1)^3$. Then for every $n \ge 0$,
$P_v(6n+5) = 3 b_6^3(n) + 3 \sum_{m \ge 1,\ 2m(3m+1) \le n} (-1)^m b_6^3\bigl(n - 2m(3m+1)\bigr) +
3 \sum_{m \ge 1,\ 2m(3m-1) \le n} (-1)^m b_6^3\bigl(n - 2m(3m-1)\bigr)$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 4 (`integers-2025-A72-thm-4`). -/
public theorem_wanted mockThetaV_six_mul_add_five_eq_sum_regular (n : ℕ) :
    coeff (6 * n + 5) mockThetaV =
      3 * coeff n ((𝔣 6 * invOfUnit (𝔣 1) 1) ^ 3) +
        3 * ∑ m ∈ (Finset.Icc 1 n).filter (fun m => 2 * m * (3 * m + 1) ≤ n),
          (-1) ^ m * coeff (n - 2 * m * (3 * m + 1)) ((𝔣 6 * invOfUnit (𝔣 1) 1) ^ 3) +
        3 * ∑ m ∈ (Finset.Icc 1 n).filter (fun m => 2 * m * (3 * m - 1) ≤ n),
          (-1) ^ m * coeff (n - 2 * m * (3 * m - 1)) ((𝔣 6 * invOfUnit (𝔣 1) 1) ^ 3)

/-- **Generating function for the odd-indexed coefficients of $\sigma(q)$.** Let $P_\sigma(n)$
be the coefficient of $q^n$ in the sixth-order mock theta function $\sigma(q)$, and for
$k \ge 1$ let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Then, as integer power series,
$f_1^2 f_3 \sum_{n \ge 0} P_\sigma(2n+1) q^n = f_2^2 f_6^2$, that is,
$\sum_{n \ge 0} P_\sigma(2n+1) q^n = f_2^2 f_6^2 / (f_1^2 f_3)$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 5 (`integers-2025-A72-thm-5`). -/
public theorem_wanted mockThetaSigma_odd_generatingFunction :
    𝔣 1 ^ 2 * 𝔣 3 * PowerSeries.mk (fun n => coeff (2 * n + 1) mockThetaSigma) =
      𝔣 2 ^ 2 * 𝔣 6 ^ 2

/-- **Congruences modulo 2 for the mock theta function $\sigma$.** Write
$\sigma(q) = \sum_{n \ge 0} P_\sigma(n) q^n$ for the sixth-order mock theta function $\sigma$ and
let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Let $p \ge 5$ be a prime with Legendre symbol
$\left(\frac{-2}{p}\right) = -1$ and let $\alpha \ge 0$ be an integer. Then, coefficientwise,
$$
f_3 \sum_{n \ge 0} P_\sigma\Bigl(2 p^{2\alpha} n + \frac{11 p^{2\alpha} + 1}{12}\Bigr) q^n
\equiv f_2 f_6^2 \pmod 2,
$$
and for all integers $n \ge 0$ and all integers $j$ with $1 \le j \le p - 1$,
$$
P_\sigma\Bigl(2 p^{2\alpha+2} n + 2 p^{2\alpha+1} j + \frac{11 p^{2\alpha+2} + 1}{12}\Bigr)
\equiv 0 \pmod 2.
$$

Since $f_2 f_6^2 / f_3 = f_2 \psi(q^3)$ with $\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$, the first
congruence says that the series of $P_\sigma(2 p^{2\alpha} n + (11 p^{2\alpha} + 1)/12)$ is
congruent to $f_2 \psi(q^3)$ modulo $2$. The division by $12$ is exact since
$p^2 \equiv 1 \pmod{24}$.

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

/-- **Sum formula for the odd-indexed coefficients of $\sigma(q)$.** Let $P_\sigma(n)$ be the
coefficient of $q^n$ in the sixth-order mock theta function $\sigma(q)$, for $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, and let $b_2^2(k)$ be the coefficient of $q^k$ in the
integer power series $(f_2 / f_1)^2$. Then for every $n \ge 0$,
$P_\sigma(2n+1) = \sum_{m \ge 0,\ (3m^2+3m)/2 \le n} b_2^2\bigl(n - (3m^2+3m)/2\bigr)$.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 7 (`integers-2025-A72-thm-7`). -/
public theorem_wanted mockThetaSigma_odd_eq_sum_regular (n : ℕ) :
    coeff (2 * n + 1) mockThetaSigma =
      ∑ m ∈ (Finset.range (n + 1)).filter (fun m => (3 * m ^ 2 + 3 * m) / 2 ≤ n),
        coeff (n - (3 * m ^ 2 + 3 * m) / 2) ((𝔣 2 * invOfUnit (𝔣 1) 1) ^ 2)

/-- **Even-index coefficients of the mock theta function $\lambda$.** Write
$\lambda(q) = \sum_{n \ge 0} P_\lambda(n) q^n$ for the sixth-order mock theta function $\lambda$,
let $f_k = \prod_{m \ge 1} (1 - q^{km})$, and let $b_2^3(m)$ be the coefficient of $q^m$ in
$(f_2/f_1)^3$. Then for every $n \ge 0$,
$$
P_\lambda(2n) = b_2^3(n) + 2 \sum_{k \ge 1,\ 3k^2 \le n} (-1)^k b_2^3(n - 3k^2).
$$

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 8 (`integers-2025-A72-thm-8`). -/
public theorem_wanted mockThetaLambda_even_eq_sum_regular (n : ℕ) :
    coeff (2 * n) mockThetaLambda =
      coeff n ((𝔣 2 * invOfUnit (𝔣 1) 1) ^ 3) +
        2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 3 * k ^ 2 ≤ n),
          (-1) ^ k * coeff (n - 3 * k ^ 2) ((𝔣 2 * invOfUnit (𝔣 1) 1) ^ 3)

/-- **Coefficients of the mock theta function $\lambda$ at indices $6n+2$.** Write
$\lambda(q) = \sum_{n \ge 0} P_\lambda(n) q^n$ for the sixth-order mock theta function $\lambda$,
let $f_k = \prod_{m \ge 1} (1 - q^{km})$, and let $\overline{p}_3(j)$ be the coefficient of
$q^j$ in $(f_2/f_1^2)^3$. Then for every $n \ge 0$,
$$
P_\lambda(6n+2) = 3 \sum_{m \ge 0,\ 3m(m+1)/2 \le n} (-1)^m (2m+1)\,
\overline{p}_3\bigl(n - 3m(m+1)/2\bigr) +
6 \sum_{m \ge 0} \sum_{k \ge 1,\ 3k^2 + 3m(m+1)/2 \le n} (-1)^{m+k} (2m+1)\,
\overline{p}_3\bigl(n - 3k^2 - 3m(m+1)/2\bigr).
$$

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
