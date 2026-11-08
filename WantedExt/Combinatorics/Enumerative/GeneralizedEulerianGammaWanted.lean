/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian

/-!
# Generalized Eulerian polynomials with a nonnegative gamma vector

Statements from Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5.

The paper treats `q, t, x, y` as indeterminates over `ℚ`; here they are rational numbers
(a polynomial identity over `ℚ` is equivalent to the identity at all rational points), and
the generating function `((x - y) / (x e^(yz) - y e^(xz)))^q e^((x+y)qtz)` is formed for
`x ≠ y`, where its denominator has nonzero constant term. Permutations of `Fin n` are
zero-indexed; excedances `w(i) > i` are `MetaMathlibExt.excedanceCount`, and the
`n`-cycles (all points in one cycle, so the identity of `Fin 1` counts) are those counted by
`MetaMathlibExt.circularEulerian`. The cycle count `cyc(w)` (fixed points included) is
`MetaMathlibExt.cycleQuotientCount` and `fix(w)` is `Fintype.card (Function.fixedPoints w)`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- The number `dexc(w)` of double excedances, the `i` with `w⁻¹(i) < i < w(i)`.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Section 4. -/
def doubleExcedanceCount {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i ↦ w⁻¹ i < i ∧ i < w i).card

/-- The identity has no double excedances.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Section 4. -/
theorem doubleExcedanceCount_one (n : ℕ) :
    doubleExcedanceCount (1 : Equiv.Perm (Fin n)) = 0 := by
  simp [doubleExcedanceCount]

/-- The generating function `𝒫(q, t; x, y; z) = ((x - y) / (x e^(yz) - y e^(xz)))^q e^((x+y)qtz)`
of Equation (2), the `q`-th power taken by Mathlib's binomial series (the base has constant
term `1` when `x ≠ y`).

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (2). -/
noncomputable def generalizedEulerianSeries (q t x y : ℚ) : PowerSeries ℚ :=
  (binomialSeries ℚ q).subst
      (C (x - y) * (C x * rescale y (exp ℚ) - C y * rescale x (exp ℚ))⁻¹ - 1) *
    rescale ((x + y) * q * t) (exp ℚ)

/-- The generalized Eulerian polynomial `P_n(q, t; x, y)`, `n!` times the coefficient of
`z^n` in `𝒫(q, t; x, y; z)` (Equation (3)).

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (3). -/
noncomputable def generalizedEulerianP (q t x y : ℚ) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n (generalizedEulerianSeries q t x y)

/-- For `q = 0` the generating function is `1`, so `P_n(0, t; x, y)` is `1` at `n = 0` and
`0` otherwise.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (2). -/
theorem generalizedEulerianP_zero_left (t x y : ℚ) (n : ℕ) :
    generalizedEulerianP 0 t x y n = if n = 0 then 1 else 0 := by
  have hb : binomialSeries ℚ (0 : ℚ) = 1 := by
    simp
  have hs : ∀ u : PowerSeries ℚ, (1 : PowerSeries ℚ).subst u = 1 := by
    intro u
    ext n
    simp [PowerSeries.subst, MvPowerSeries.subst, MvPowerSeries.eval₂]
  unfold generalizedEulerianP generalizedEulerianSeries
  rw [hb, hs, mul_zero, zero_mul, rescale_zero_apply]
  rcases n with _ | n <;> simp [coeff_one]

/-- **Proposition 1.** For `x ≠ 1`, with `C_n(x) = ∑_{w an n-cycle} x^(exc w)`,
`∑_{n ≥ 1} C_n(x) z^n / n! = z + ln((x - 1) / (x e^z - e^(xz)))`; the logarithm of a series
with constant term `1` is Mathlib's `PowerSeries.logOf`.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Proposition 1 (`jis-2024-24.1.5-prop-1`). -/
public theorem_wanted cyclicExcedanceEGF_eq (x : ℚ) (hx : x ≠ 1) :
    PowerSeries.mk (fun n ↦ if n = 0 then 0 else
        (∑ m ∈ Finset.range (n + 1), (circularEulerian n m : ℚ) * x ^ m) / (n.factorial : ℚ)) =
      X + logOf (C (x - 1) * (C x * exp ℚ - rescale x (exp ℚ))⁻¹)

/-- **Theorem 2.** `P_n(q, t; x, y) = ∑_{w ∈ S_n} q^(cyc w) t^(fix w) x^(exc w) y^(exc w⁻¹)
(x + y)^(fix w)`, for rational `q, t, x, y` with `x ≠ y`.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 2 (`jis-2024-24.1.5-thm-2`). -/
public theorem_wanted generalizedEulerianP_eq_sum_perm (q t x y : ℚ) (hxy : x ≠ y) (n : ℕ) :
    generalizedEulerianP q t x y n =
      ∑ w : Equiv.Perm (Fin n),
        q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w) *
          x ^ excedanceCount n w * y ^ excedanceCount n w⁻¹ *
          (x + y) ^ Fintype.card (Function.fixedPoints w)

/-- **Theorem 4.** The gamma coefficients `γ_{n,k}(q, t)` of
`P_n(q, t; x, y) = ∑_{k ≤ n/2} γ_{n,k}(q, t) x^k y^k (x + y)^(n - 2k)` (Equation (6)) are
polynomials in `q, t` with nonnegative integer coefficients: there are natural numbers
`c k i j` with `γ_{n,k}(q, t) = ∑_{i, j ≤ n} c k i j q^i t^j` making Equation (6) hold for all
rational `q, t, x, y` with `x ≠ y` (such `γ_{n,k}` are unique).

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 4 (`jis-2024-24.1.5-thm-4`). -/
public theorem_wanted generalizedEulerianP_gamma_nonneg (n : ℕ) :
    ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ q t x y : ℚ, x ≠ y →
      generalizedEulerianP q t x y n =
        ∑ k ∈ Finset.range (n / 2 + 1),
          (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (c k i j : ℚ) * q ^ i * t ^ j) * x ^ k * y ^ k * (x + y) ^ (n - 2 * k)

/-- **Corollary 5.** For nonnegative integers `q, t`, `P_n(q, t; x) = P_n(q, t; x, 1)` is a
unimodal polynomial in `x`: it agrees (for `x ≠ 1`) with a polynomial whose coefficient
sequence weakly increases up to some index `m` and weakly decreases from `m` on. The paper's
Corollary 5 asserts unimodality only ("`P_n(q,t;x)` is a unimodal polynomial in `x`"); symmetry
is not part of it.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Corollary 5 (`jis-2024-24.1.5-cor-5`). -/
public theorem_wanted generalizedEulerianP_unimodal (q t n : ℕ) :
    ∃ p : Polynomial ℚ, (∀ x : ℚ, x ≠ 1 → p.eval x = generalizedEulerianP q t x 1 n) ∧
      ∃ m : ℕ, (∀ i < m, p.coeff i ≤ p.coeff (i + 1)) ∧
        ∀ i, m ≤ i → p.coeff (i + 1) ≤ p.coeff i

/-- **Theorem 7.** The gamma coefficients are
`γ_{n,k}(q, t) = ∑_{w ∈ S_n, exc w = k, dexc w = 0} q^(cyc w) t^(fix w)`: Equation (6) holds
with these coefficients (for rational `q, t, x, y`, `x ≠ y`), and each is
`∑_{i, j ≤ n} γ_{n,k,i,j} q^i t^j` with `γ_{n,k,i,j}` the number of `w ∈ S_n` with `exc w = k`,
`dexc w = 0`, `cyc w = i`, `fix w = j`.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 7 (`jis-2024-24.1.5-thm-7`). -/
public theorem_wanted generalizedEulerianP_gamma_eq (n : ℕ) :
    (∀ q t x y : ℚ, x ≠ y →
      generalizedEulerianP q t x y n =
        ∑ k ∈ Finset.range (n / 2 + 1),
          (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦
              excedanceCount n w = k ∧ doubleExcedanceCount w = 0),
            q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w)) *
          x ^ k * y ^ k * (x + y) ^ (n - 2 * k)) ∧
    ∀ (k : ℕ) (q t : ℚ),
      ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦
          excedanceCount n w = k ∧ doubleExcedanceCount w = 0),
        q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        ((Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦ excedanceCount n w = k ∧
            doubleExcedanceCount w = 0 ∧
              cycleQuotientCount w = i ∧ Fintype.card (Function.fixedPoints w) = j)).card : ℚ) *
          q ^ i * t ^ j

/-- **Corollary 8.** `P_{2n+1}(q, t; -1) = 0` and
`(-1)^n P_{2n}(q, t; -1) = ∑_{w ∈ D_{2n}} q^(cyc w) (-1)^(n - exc w)
= ∑_{w ∈ D_{2n}, exc w = n, dexc w = 0} q^(cyc w)`, where `P_m(q, t; -1) = P_m(q, t; -1, 1)` and
`D_{2n}` is the set of derangements (`fix w = 0`); `(-1)^(n - exc w)` is an integer power.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Corollary 8 (`jis-2024-24.1.5-cor-8`). -/
public theorem_wanted generalizedEulerianP_neg_one (q t : ℚ) (n : ℕ) :
    generalizedEulerianP q t (-1) 1 (2 * n + 1) = 0 ∧
      (-1) ^ n * generalizedEulerianP q t (-1) 1 (2 * n) =
        ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
            Fintype.card (Function.fixedPoints w) = 0),
          q ^ cycleQuotientCount w * (-1 : ℚ) ^ ((n : ℤ) - excedanceCount (2 * n) w) ∧
      ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
          Fintype.card (Function.fixedPoints w) = 0),
          q ^ cycleQuotientCount w * (-1 : ℚ) ^ ((n : ℤ) - excedanceCount (2 * n) w) =
        ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
            Fintype.card (Function.fixedPoints w) = 0 ∧ excedanceCount (2 * n) w = n ∧
              doubleExcedanceCount w = 0), q ^ cycleQuotientCount w

end

end MetaMathlibExt
