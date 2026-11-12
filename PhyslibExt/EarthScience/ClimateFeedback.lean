 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Climate feedback and two-box response

## i. Overview

The scalar model `C*T' = F - lambda*T` has the explicit relaxation
solution `T(t) = F/lambda + (T0 - F/lambda)*exp(-lambda*t/C)`. For the
two-box system `Cs*Ts' = F - lambda*Ts - gamma*(Ts - Td)` and
`Cd*Td' = gamma*(Ts - Td)`, the equilibrium is `Ts = Td = F/lambda`.
For anomaly variables, `E = (Cs*xs^2 + Cd*xd^2)/2` satisfies
`E' = -lambda*xs^2 - gamma*(xs - xd)^2 <= -c*E` with
`c = min (2*lambda/(Cs + 2*Cd)) (gamma/Cd) > 0`. No nonlinear tipping
or empirical sensitivity claim is made.

## ii. Key results

- `EarthScience.scalar_relaxation`: explicit relaxation solution and `T(0) = T0`.
- `EarthScience.two_box_equilibrium`: equilibrium is `Ts = Td = F/lambda`.
- `EarthScience.anomaly_energy_hasDerivAt`: `E' = -lambda*xs^2 - gamma*(xs-xd)^2`.
- `EarthScience.anomaly_energy_decay`: `E' <= -c*E` with `c > 0`.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience


/-- Scalar relaxation: `T(t) = F/lambda + (T0 - F/lambda)*exp(-lambda*t/C)`
satisfies `T(0) = T0` and `HasDerivAt T ((F - lambda*T(t))/C) t`,
i.e. `C*T' = F - lambda*T`. -/
theorem scalar_relaxation {C F lam T0 : ℝ} (hC : 0 < C) (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (fun t => F / lam + (T0 - F / lam) * Real.exp (-lam * t / C))
      ((F - lam * (F / lam + (T0 - F / lam) * Real.exp (-lam * t / C))) / C) t
    ∧ (F / lam + (T0 - F / lam) * Real.exp (-lam * 0 / C) = T0) := by
  have hC' : C ≠ 0 := ne_of_gt hC
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hg : HasDerivAt (fun t : ℝ => -lam * t / C) (-lam / C) t := by
    have h2 := ((hasDerivAt_id t).const_mul (-lam)).div_const C
    simpa using h2
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-lam * t / C))
      (Real.exp (-lam * t / C) * (-lam / C)) t :=
    hg.exp
  have hmul : HasDerivAt (fun t : ℝ => (T0 - F / lam) * Real.exp (-lam * t / C))
      ((T0 - F / lam) * (Real.exp (-lam * t / C) * (-lam / C))) t :=
    hexp.const_mul (T0 - F / lam)
  have hadd : HasDerivAt (fun t : ℝ => F / lam + (T0 - F / lam) * Real.exp (-lam * t / C))
      (0 + (T0 - F / lam) * (Real.exp (-lam * t / C) * (-lam / C))) t :=
    (hasDerivAt_const t (F / lam)).fun_add hmul
  refine ⟨?_, ?_⟩
  · convert hadd using 1
    field_simp
    ring
  · simp only [mul_zero, zero_div, Real.exp_zero, mul_one]
    ring

/-- Two-box equilibrium: if `F - lam*Ts - gam*(Ts - Td) = 0` and
`gam*(Ts - Td) = 0` with `lam, gam > 0`, then `Ts = Td = F/lam`. -/
theorem two_box_equilibrium {F lam gam Ts Td : ℝ} (hlam : 0 < lam) (hgam : 0 < gam)
    (hs : F - lam * Ts - gam * (Ts - Td) = 0) (hd : gam * (Ts - Td) = 0) :
    Ts = F / lam ∧ Td = F / lam := by
  have hgam' : gam ≠ 0 := ne_of_gt hgam
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hdiff : Ts - Td = 0 := (mul_eq_zero.mp hd).resolve_left hgam'
  have hlamTs : lam * Ts = F := by linarith
  have hTs : Ts = F / lam := by
    rw [eq_div_iff hlam']
    linear_combination hlamTs
  have hTd : Td = F / lam := by
    have hTeq : Td = Ts := by linarith
    rw [hTeq, hTs]
  exact ⟨hTs, hTd⟩

/-- Anomaly energy: if `xs, xd` satisfy the anomaly ODEs
`Cs*xs' = -lam*xs - gam*(xs - xd)` and `Cd*xd' = gam*(xs - xd)`,
then `E(t) = (Cs*xs^2 + Cd*xd^2)/2` has derivative
`-lam*xs^2 - gam*(xs - xd)^2`. -/
theorem anomaly_energy_hasDerivAt {Cs Cd lam gam : ℝ} (hCs : 0 < Cs) (hCd : 0 < Cd)
    (xs xd : ℝ → ℝ) (t : ℝ)
    (hxs : HasDerivAt xs ((-lam * xs t - gam * (xs t - xd t)) / Cs) t)
    (hxd : HasDerivAt xd ((gam * (xs t - xd t)) / Cd) t) :
    HasDerivAt (fun t => (Cs * (xs t) ^ 2 + Cd * (xd t) ^ 2) / 2)
      (-lam * (xs t) ^ 2 - gam * (xs t - xd t) ^ 2) t := by
  have hCs' : Cs ≠ 0 := ne_of_gt hCs
  have hCd' : Cd ≠ 0 := ne_of_gt hCd
  have hxs2 : HasDerivAt (fun t : ℝ => (xs t) ^ 2)
      (2 * xs t * (((-lam * xs t - gam * (xs t - xd t)) / Cs))) t := by
    have h := hxs.fun_pow 2
    simpa using h
  have hxd2 : HasDerivAt (fun t : ℝ => (xd t) ^ 2)
      (2 * xd t * (((gam * (xs t - xd t)) / Cd))) t := by
    have h := hxd.fun_pow 2
    simpa using h
  have hE : HasDerivAt (fun t => (Cs * (xs t) ^ 2 + Cd * (xd t) ^ 2) / 2)
      ((Cs * (2 * xs t * (((-lam * xs t - gam * (xs t - xd t)) / Cs)))
        + Cd * (2 * xd t * (((gam * (xs t - xd t)) / Cd)))) / 2) t := by
    have h1 := hxs2.const_mul Cs
    have h2 := hxd2.const_mul Cd
    have h3 := h1.fun_add h2
    have h4 := h3.div_const 2
    exact h4
  convert hE using 1
  field_simp
  ring

/-- Anomaly-energy decay bound: with
`c = min (2*lam/(Cs + 2*Cd)) (gam/Cd)`,
`-lam*xs^2 - gam*(xs-xd)^2 <= -c * (Cs*xs^2 + Cd*xd^2)/2`
for all `xs, xd`, and `c > 0` when `lam, gam > 0`. -/
theorem anomaly_energy_decay {Cs Cd lam gam xs xd : ℝ}
    (hCs : 0 < Cs) (hCd : 0 < Cd) (hlam : 0 < lam) (hgam : 0 < gam) :
    0 < min (2 * lam / (Cs + 2 * Cd)) (gam / Cd) ∧
    -lam * xs ^ 2 - gam * (xs - xd) ^ 2
      ≤ -(min (2 * lam / (Cs + 2 * Cd)) (gam / Cd)) * (Cs * xs ^ 2 + Cd * xd ^ 2) / 2 := by
  have hpos : (0:ℝ) < Cs + 2 * Cd := by linarith
  have h1 : (0:ℝ) < 2 * lam / (Cs + 2 * Cd) :=
    div_pos (mul_pos (by norm_num) hlam) hpos
  have h2 : (0:ℝ) < gam / Cd := div_pos hgam hCd
  have hc : (0:ℝ) < min (2 * lam / (Cs + 2 * Cd)) (gam / Cd) := lt_min h1 h2
  refine ⟨hc, ?_⟩
  have hxd : xd ^ 2 ≤ 2 * xs ^ 2 + 2 * (xs - xd) ^ 2 := by
    nlinarith [sq_nonneg (2 * xs - xd)]
  have e1 : min (2 * lam / (Cs + 2 * Cd)) (gam / Cd) * (Cs + 2 * Cd) ≤ 2 * lam :=
    (le_div_iff₀ hpos).mp (min_le_left _ _)
  have e2 : min (2 * lam / (Cs + 2 * Cd)) (gam / Cd) * Cd ≤ gam :=
    (le_div_iff₀ hCd).mp (min_le_right _ _)
  have hc0 : (0:ℝ) ≤ min (2 * lam / (Cs + 2 * Cd)) (gam / Cd) := le_of_lt hc
  nlinarith [hxd, e1, e2, sq_nonneg xs, sq_nonneg (xs - xd),
    mul_nonneg hc0 hCd.le, mul_nonneg hc0 hCs.le, hc0, hCs.le, hCd.le]


end EarthScience
