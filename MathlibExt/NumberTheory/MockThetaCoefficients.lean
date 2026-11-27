/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Mock theta coefficients and the p-dissection of Ramanujan's psi function

This module defines the mock theta functions $v$, $\sigma$, and $\lambda$ and computes their
first coefficients. For each odd prime $p$, it proves the $p$-dissection of Ramanujan's
$\psi$ and distinguishes its central offset from the other offsets modulo $p$.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

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

namespace ramanujanPsi_p_dissection

open Function

-- The doubled triangular degree avoids division when matching exponents.
private def hit (n : ℕ) (t : ℤ) : ℤ := if t * (t + 1) = 2 * n then 1 else 0

private theorem hit_reflect (n : ℕ) (t : ℤ) : hit n (-1 - t) = hit n t := by
  simp only [hit, show (-1 - t) * (-1 - t + 1) = t * (t + 1) by ring]

private theorem hit_finite (n : ℕ) : HasFiniteSupport (hit n) := by
  apply (Finset.Icc (-(2 * n : ℤ) - 1) (2 * n : ℤ)).finite_toSet.subset
  intro t ht
  have h : t * (t + 1) = 2 * n := by
    by_contra h
    exact ht (ite_eq_right h)
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor <;> nlinarith [sq_nonneg t, sq_nonneg (t + 1)]

private def degree (a b : ℕ) (j : ℤ) : ℤ :=
  a * (j * (j + 1) / 2) + b * (j * (j - 1) / 2)

private theorem twice_halves (j : ℤ) :
    2 * (j * (j + 1) / 2) = j * (j + 1) ∧
    2 * (j * (j - 1) / 2) = j * (j - 1) := by
  have h := Int.two_dvd_mul_add_one j
  have h' := Int.two_dvd_mul_add_one (j - 1)
  rw [sub_add_cancel, mul_comm (j - 1)] at h'
  exact ⟨Int.mul_ediv_cancel' h, Int.mul_ediv_cancel' h'⟩

private theorem twice_degree (a b : ℕ) (j : ℤ) :
    2 * degree a b j = a * (j * (j + 1)) + b * (j * (j - 1)) := by
  obtain ⟨h, h'⟩ := twice_halves j
  unfold degree
  linear_combination (a : ℤ) * h + (b : ℤ) * h'

private theorem sq_le_degree {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (j : ℤ) :
    j ^ 2 ≤ degree a b j := by
  have h₁ : 0 ≤ j * (j + 1) := by
    rcases le_or_gt 0 j with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have h₂ : 0 ≤ j * (j - 1) := by
    rcases le_or_gt j 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [twice_degree a b j, mul_nonneg (sub_nonneg.mpr ha') h₁,
    mul_nonneg (sub_nonneg.mpr hb') h₂]

private theorem coeff_theta {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    coeff n (ramanujanThetaMonomial 1 a b) =
      ∑ᶠ j : ℤ, if degree a b j = n then (1 : ℤ) else 0 := by
  simp only [ramanujanThetaMonomial, coeff_mk, one_pow]
  symm
  apply finsum_eq_finsetSum_of_support_subset
  intro j hj
  have he : degree a b j = n := by
    by_contra h
    exact hj (ite_eq_right h)
  simp only [Finset.mem_coe, Finset.mem_Icc]
  have h := sq_le_degree ha hb j
  constructor <;> nlinarith [sq_nonneg (j + 1), sq_nonneg (j - 1)]

private theorem coeff_shift {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (s n : ℕ)
    (k : ℤ → ℤ) (hk : ∀ j, 2 * (s + degree a b j) = k j * (k j + 1)) :
    coeff n (X ^ s * ramanujanThetaMonomial 1 a b) = ∑ᶠ j, hit n (k j) := by
  rw [coeff_X_pow_mul']
  split_ifs with hs
  · rw [coeff_theta ha hb]
    apply finsum_congr
    intro j
    simp only [hit, Int.natCast_sub hs, ← hk]
    congr 1
    exact propext (by omega)
  · symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    simp only [hit, ← hk]
    apply ite_eq_right
    have h := sq_le_degree ha hb j
    nlinarith [sq_nonneg j]

-- The contribution of the residue class m modulo p.
private noncomputable def row (f : ℤ → ℤ) (p m : ℕ) : ℤ :=
  ∑ᶠ j : ℤ, f (j * p + m)

private theorem sum_rows (f : ℤ → ℤ) (hf : HasFiniteSupport f) (p : ℕ) [NeZero p] :
    ∑ᶠ t, f t = ∑ m ∈ Finset.range p, row f p m := by
  let e := (Equiv.prodComm (Fin p) ℤ).trans (Int.divModEquiv p).symm
  rw [← finsum_comp_equiv e, finsum_curry _ (hf.fun_comp_of_injective e.injective),
    finsum_eq_sum_of_fintype]
  exact Fin.sum_univ_eq_sum_range (row f p) p

private theorem row_reflect (f : ℤ → ℤ) (hs : ∀ t, f (-1 - t) = f t)
    {p m : ℕ} (hm : m < p) : row f p (p - 1 - m) = row f p m := by
  apply finsum_eq_of_bijective (fun j : ℤ ↦ -1 - j)
    (show Involutive (fun j : ℤ ↦ -1 - j) from fun j ↦ by dsimp; omega).bijective
  intro j
  rw [← hs (j * p + (↑(p - 1 - m) : ℤ))]
  congr 1
  push_cast [Int.natCast_sub (show m ≤ p - 1 by omega), Int.natCast_sub (show 1 ≤ p by omega)]
  ring

-- Reflection exchanges the two parity classes, so each contributes half the total.
private theorem sum_even (f : ℤ → ℤ) (hf : HasFiniteSupport f)
    (hs : ∀ t, f (-1 - t) = f t) :
    ∑ᶠ t, f t = 2 * ∑ᶠ j : ℤ, f (-2 * j) := by
  have he : row f 2 0 = ∑ᶠ j : ℤ, f (-2 * j) := by
    apply finsum_eq_of_bijective (Equiv.neg ℤ) (Equiv.neg ℤ).bijective
    intro j
    change f (j * 2 + 0) = f (-2 * -j)
    congr 1
    ring
  have hr : row f 2 1 = row f 2 0 := row_reflect f hs (p := 2) (m := 0) (by decide)
  rw [sum_rows f hf 2]
  simp [Finset.sum_range_succ, hr, he, two_mul]

-- For odd p the reflected rows agree in pairs, with a single fixed central row.
private theorem sum_paired_rows (f : ℤ → ℤ) (hf : HasFiniteSupport f)
    (hs : ∀ t, f (-1 - t) = f t) {p h : ℕ} (hp : p = 2 * h + 1) :
    ∑ᶠ t, f t = 2 * (∑ m ∈ Finset.range h, row f p m) + row f p h := by
  have : NeZero p := ⟨by omega⟩
  rw [sum_rows f hf p]
  conv_lhs => arg 1; rw [show p = (h + 1) + h by omega]
  rw [Finset.sum_range_add, Finset.sum_range_succ]
  have htail : (∑ m ∈ Finset.range h, row f p (h + 1 + m)) =
      ∑ m ∈ Finset.range h, row f p m := by
    rw [← Finset.sum_range_reflect (row f p) h]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' := Finset.mem_range.mp hm
    rw [show h + 1 + m = p - 1 - (h - 1 - m) by omega]
    exact row_reflect f hs (by omega)
  rw [htail]
  ring

private theorem twice_offset (m : ℕ) : 2 * ((m ^ 2 + m) / 2) = m ^ 2 + m := by
  rw [show m ^ 2 + m = m * (m + 1) by ring, Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one m)]

private theorem eight_central {p : ℕ} (ho : Odd p) :
    8 * ((p ^ 2 - 1) / 8) + 1 = p ^ 2 := by
  rw [Nat.mul_div_cancel' (Nat.eight_dvd_sq_sub_one_of_odd ho)]
  obtain ⟨k, rfl⟩ := ho
  have : 0 < (2 * k + 1) ^ 2 := by positivity
  omega

private theorem coeff_regular {p h m : ℕ} (hp : p = 2 * h + 1) (hm : m < h) (n : ℕ) :
    coeff n (X ^ ((m ^ 2 + m) / 2) *
      ramanujanThetaMonomial 1 ((p ^ 2 + (2 * m + 1) * p) / 2)
        ((p ^ 2 - (2 * m + 1) * p) / 2)) = row (hit n) p m := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show m + 1 ≤ h by omega)
  have hA : (p ^ 2 + (2 * m + 1) * p) / 2 = p * (h + m + 1) := by
    rw [show p ^ 2 + (2 * m + 1) * p = p * (h + m + 1) * 2 by rw [hp]; ring]
    simp
  have hB : (p ^ 2 - (2 * m + 1) * p) / 2 = p * (k + 1) := by
    rw [show p ^ 2 = p * (k + 1) * 2 + (2 * m + 1) * p by rw [hp, hk]; ring]
    simp
  rw [hA, hB]
  have hp' : 0 < p := by omega
  apply coeff_shift (by positivity) (by positivity)
  intro j
  rw [mul_add, twice_degree]
  have hs : 2 * (((m ^ 2 + m) / 2 : ℕ) : ℤ) = (m : ℤ) ^ 2 + m := by
    exact_mod_cast twice_offset m
  rw [hs, hp, hk]
  push_cast
  ring

private theorem coeff_central {p h : ℕ} (hp : p = 2 * h + 1) (n : ℕ) :
    coeff n (X ^ ((p ^ 2 - 1) / 8) * ramanujanThetaMonomial 1 (p ^ 2) (3 * p ^ 2)) =
      ∑ᶠ j : ℤ, hit n ((-2 * j) * p + h) := by
  have hp' : 0 < p := by omega
  apply coeff_shift (by positivity) (by positivity)
  intro j
  have hc : 8 * (((p ^ 2 - 1) / 8 : ℕ) : ℤ) + 1 = (p : ℤ) ^ 2 := by
    exact_mod_cast eight_central (show Odd p from ⟨h, hp⟩)
  rw [mul_add, twice_degree, hp]
  rw [hp] at hc
  push_cast at hc ⊢
  nlinarith only [hc]

private theorem coeff_psi (n : ℕ) :
    coeff n (ramanujanThetaMonomial 1 1 3) = ∑ᶠ j : ℤ, hit n (-2 * j) := by
  simpa using coeff_shift (a := 1) (b := 3) (by decide) (by decide) 0 n (fun j ↦ -2 * j)
    (fun j ↦ by rw [Nat.cast_zero, zero_add, twice_degree]; push_cast; ring)

private theorem offset_ne {p : ℕ} (hp : p.Prime) (ho : Odd p)
    {m : ℕ} (hm : 2 * m + 1 < p) :
    ¬ (m ^ 2 + m) / 2 ≡ (p ^ 2 - 1) / 8 [MOD p] := by
  intro he
  have hl : 8 * ((m ^ 2 + m) / 2) + 1 = (2 * m + 1) ^ 2 := by
    nlinarith only [twice_offset m]
  have he' := (he.mul_left 8).add_right 1
  rw [hl, eight_central ho] at he'
  have hd : p ∣ (2 * m + 1) ^ 2 := Nat.modEq_zero_iff_dvd.mp
    (he'.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p (by decide : 2 ≠ 0))))
  exact (Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow hd)).not_gt hm

end ramanujanPsi_p_dissection

open ramanujanPsi_p_dissection in
/-- **The p-dissection of Ramanujan's psi function.** Let $p$ be an odd prime, let $f(c, d)$ be
Ramanujan's theta function and $\psi(q) = f(q, q^3)$. Then, as integer power series,
$\psi(q) = \sum_{m=0}^{(p-3)/2} q^{(m^2+m)/2} f(q^{(p^2+(2m+1)p)/2}, q^{(p^2-(2m+1)p)/2}) +
q^{(p^2-1)/8} f(q^{p^2}, q^{3p^2})$, where the last factor is $\psi(q^{p^2})$. Moreover
$(m^2+m)/2 \not\equiv (p^2-1)/8 \pmod p$ for every integer $m$ with $0 \le m \le (p-3)/2$.

The paper quotes this from Cui and Gu, Theorem 2.1.

Source: Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock
Theta Functions*, INTEGERS 25 (2025), Article A72, Lemma 1 (`integers-2025-A72-lem-1`). -/
public theorem ramanujanPsi_p_dissection (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ramanujanThetaMonomial 1 1 3 =
        ∑ m ∈ Finset.range ((p - 3) / 2 + 1),
          X ^ ((m ^ 2 + m) / 2) *
            ramanujanThetaMonomial 1 ((p ^ 2 + (2 * m + 1) * p) / 2)
              ((p ^ 2 - (2 * m + 1) * p) / 2) +
          X ^ ((p ^ 2 - 1) / 8) * ramanujanThetaMonomial 1 (p ^ 2) (3 * p ^ 2) ∧
      ∀ m ≤ (p - 3) / 2, ¬ (m ^ 2 + m) / 2 ≡ (p ^ 2 - 1) / 8 [MOD p] := by
  obtain ⟨h, hh⟩ := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  constructor
  · apply PowerSeries.ext
    intro n
    rw [map_add, map_sum, coeff_psi, coeff_central hh, show (p - 3) / 2 + 1 = h by omega]
    have hrows := Finset.sum_congr (s₁ := Finset.range h) rfl fun m hm ↦
      coeff_regular hh (Finset.mem_range.mp hm) n
    rw [hrows]
    let g (j : ℤ) := hit n (j * p + h)
    have hpi : (p : ℤ) ≠ 0 := by omega
    have hg : Function.HasFiniteSupport g := (hit_finite n).fun_comp_of_injective
      (g := fun j : ℤ ↦ j * p + h) (fun j k hj ↦ by
        dsimp at hj
        exact (mul_left_inj' hpi).mp (add_right_cancel hj))
    have hsym (j : ℤ) : g (-1 - j) = g j := by
      unfold g
      rw [← hit_reflect n (j * p + h)]
      congr 1
      rw [hh]
      push_cast
      ring
    have hcenter : row (hit n) p h = 2 * ∑ᶠ j : ℤ, hit n ((-2 * j) * p + h) :=
      sum_even g hg hsym
    have hsum := sum_paired_rows (hit n) (hit_finite n) (hit_reflect n) hh
    rw [sum_even _ (hit_finite n) (hit_reflect n), hcenter] at hsum
    linarith
  · intro m hm
    exact offset_ne (m := m) hp ⟨h, hh⟩ (by omega)

end

end MetaMathlibExt
