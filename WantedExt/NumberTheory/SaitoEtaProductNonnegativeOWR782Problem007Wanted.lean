/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nonnegativity of K. Saito's eta products (Oberwolfach Reports 1/2005)

Oberwolfach workshop Gitter und Anwendungen (2005), T. Ibukiyama, K. Saito's conjecture: for every
natural number `h` the eta product `η(hτ)^{φ(h)} / ∏_{d ∣ h} η(dτ)^{μ(d)}` has only nonnegative
Fourier coefficients (proved there for prime powers).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.SaitoEtaProductNonnegativeOWR782Problem007Wanted

/-!
Source: T. Ibukiyama, in Gitter und Anwendungen, Oberwolfach Reports 2 (2005), no. 1, pp. 54-55, DOI
10.4171/OWR/2005/01. UnsolvedMath record UM-30000166 (`OWR-782-007`), dataset ulamai/UnsolvedMath
v1.8.0.

Since `η(dτ) = q^{d/24} ∏_{m ≥ 1} (1 - q^{dm})`, the Fourier coefficients are, up to a shift by a
power of `q`, the coefficients of the power series `∏_{m ≥ 1} (1 - q^{hm})^{φ(h)} ∏_{d ∣ h} (1 -
q^{dm})^{-μ(d)}`; the coefficient of `q^j` is read off the factors with `m ≤ j`, computed in `ℚ⟦q⟧`.
-/

open PowerSeries

/-- The factor `(1 - q^{d m})^{-μ(d)}` as a rational power series (`μ(d) ∈ {-1, 0, 1}`); for
`d m ≥ 1` the inverse is the geometric series `∑ q^{d m j}`. -/
noncomputable def moebiusFactor (d m : ℕ) : PowerSeries ℚ :=
  if ArithmeticFunction.moebius d = 1 then (1 - X ^ (d * m))⁻¹
  else if ArithmeticFunction.moebius d = -1 then 1 - X ^ (d * m) else 1

/-- The coefficient of `q^j` in `∏_{m ≥ 1} (1 - q^{h m})^{φ(h)} ∏_{d ∣ h} (1 - q^{d m})^{-μ(d)}`,
the product side of Saito's eta product `η(hτ)^{φ(h)} ∏_{d ∣ h} η(dτ)^{-μ(d)}` without its power
of `q`. It is read off the factors with `m ≤ j`: every other factor is `1 + O(q^{j + 1})`. -/
noncomputable def saitoCoeff (h j : ℕ) : ℚ :=
  coeff j (∏ m ∈ Finset.Icc 1 j,
    ((1 - X ^ (h * m)) ^ Nat.totient h * ∏ d ∈ h.divisors, moebiusFactor d m))

/-- K. Saito's conjecture (Oberwolfach Report 1/2005, pp. 54-55): for every `h ≥ 1` the eta
product `η(hτ)^{φ(h)} ∏_{d ∣ h} η(dτ)^{-μ(d)}` has nonnegative Fourier coefficients. -/
def saitoEtaProductNonnegative : Prop :=
  ∀ h : ℕ, 1 ≤ h → ∀ j : ℕ, 0 ≤ saitoCoeff h j

/--
Resolved true: Berkovich and Garvan proved Saito's conjecture for every positive integer `N`, by a
multidimensional theta function identity (earlier: Saito for small `N`, Ibukiyama for prime powers,
Saito and Yasuda for `gcd(N, 6) > 1`). Source: T. Ibukiyama, in Gitter und Anwendungen, Oberwolfach
Reports 2 (2005), no. 1, pp. 54-55, DOI 10.4171/OWR/2005/01; resolution: A. Berkovich and F. G.
Garvan, K. Saito's conjecture for nonnegative eta products and analogous results for other infinite
products, J. Number Theory 128 (2008), arXiv:math/0607606, Conjecture 1.1 (K. Saito): for every
positive integer N, η(Nτ)^{φ(N)} / ∏_{d | N} η(dτ)^{μ(d)} has nonnegative Fourier coefficients;
Section 1: 'We prove the conjecture for general N', https://arxiv.org/abs/math/0607606.
-/
public theorem_wanted saitoEtaProductNonnegative_holds : saitoEtaProductNonnegative

end MathlibExt.NumberTheory.SaitoEtaProductNonnegativeOWR782Problem007Wanted
