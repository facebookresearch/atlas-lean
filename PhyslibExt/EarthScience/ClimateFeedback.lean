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
import MathlibExt.Analysis.ODE.LyapunovStability

/-!
# Climate feedback and two-box response

## i. Overview

The scalar model `C*T' = F - lambda*T` has the explicit relaxation
solution `T(t) = F/lambda + (T0 - F/lambda)*exp(-lambda*t/C)`. For the
two-box system `Cs*Ts' = F - lambda*Ts - gamma*(Ts - Td)` and
`Cd*Td' = gamma*(Ts - Td)`, the equilibrium is `Ts = Td = F/lambda`.
For anomaly variables (departures from that equilibrium), solutions of
the anomaly ODEs `Cs*xs' = -lambda*xs - gamma*(xs - xd)` and
`Cd*xd' = gamma*(xs - xd)` have energy `E = (Cs*xs^2 + Cd*xd^2)/2` with
`E' = -lambda*xs^2 - gamma*(xs - xd)^2 <= -c*E`, where
`c = min (2*lambda/(Cs + 2*Cd)) (gamma/Cd) > 0`. Integrating that
inequality with `le_exp_mul_of_hasDerivWithinAt_Ici`
(`MathlibExt.Analysis.ODE.LyapunovStability`) gives
`E(t) <= exp(-c*t) * E(0)` for `t >= 0` along solutions on `[0, ∞)`.
The energy, its dissipation identity, the rate `c`, and the exponential
bound are an elementary estimate derived here, not taken from the
references. No nonlinear tipping or empirical sensitivity claim is made.

## ii. Key results

- `EarthScience.scalar_relaxation`: explicit relaxation solution and `T(0) = T0`.
- `EarthScience.two_box_equilibrium`: equilibrium is `Ts = Td = F/lambda`.
- `EarthScience.anomaly_energy_hasDerivAt`: `E' = -lambda*xs^2 - gamma*(xs-xd)^2`.
- `EarthScience.anomaly_energy_dissipation_bound`: the algebraic bound
  `-lambda*xs^2 - gamma*(xs-xd)^2 <= -c*E` with `c > 0`.
- `EarthScience.anomaly_energy_decay`: along solutions of the anomaly
  ODEs, `E' <= -c*E` with `c > 0`.
- `EarthScience.anomaly_energy_exp_bound`: along forward solutions of the
  anomaly ODEs on `[0, ∞)` (derivatives within `[0, ∞)`),
  `E(t) <= exp(-c*t) * E(0)` for `t >= 0`.

## iii. Table of contents

- A. Main results

## iv. References

- I. M. Held, M. Winton, K. Takahashi, T. Delworth, F. Zeng and
  G. K. Vallis, "Probing the fast and slow components of global warming
  by returning abruptly to preindustrial forcing", *J. Climate* 23
  (2010), 2418-2427: the two-box model of a fast surface (upper-ocean)
  box exchanging heat with a slow deep-ocean box.
- O. Geoffroy, D. Saint-Martin, D. J. L. Olivié, A. Voldoire, G. Bellon
  and S. Tytéca, "Transient climate response in a two-layer
  energy-balance model. Part I: Analytical solution and parameter
  calibration using CMIP5 AOGCM experiments", *J. Climate* 26 (2013),
  1841-1857: the two-layer model, in this module's notation
  `Cs*Ts' = F - lambda*Ts - gamma*(Ts - Td)` and
  `Cd*Td' = gamma*(Ts - Td)`, its equilibrium, and its analytical
  solution as a sum of two decaying modes.
- The scalar model is the surface equation without deep-ocean exchange
  (`gamma = 0`). The anomaly energy, its dissipation identity, the
  decay rate `c`, and the exponential bound are derived here.
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

/-- Anomaly-energy dissipation bound (algebraic, pointwise in the state):
with `c = min (2*lam/(Cs + 2*Cd)) (gam/Cd)`,
`-lam*xs^2 - gam*(xs-xd)^2 <= -c * (Cs*xs^2 + Cd*xd^2)/2`
for all `xs, xd`, and `c > 0` when `lam, gam > 0`. -/
lemma anomaly_energy_dissipation_bound {Cs Cd lam gam xs xd : ℝ}
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

/-- Anomaly-energy decay: if `xs, xd` satisfy the anomaly ODEs
`Cs*xs' = -lam*xs - gam*(xs - xd)` and `Cd*xd' = gam*(xs - xd)` at `t`,
then `E(t) = (Cs*xs^2 + Cd*xd^2)/2` satisfies `E'(t) <= -c * E(t)` with
`c = min (2*lam/(Cs + 2*Cd)) (gam/Cd) > 0`. Combines
`anomaly_energy_hasDerivAt` with `anomaly_energy_dissipation_bound`. -/
theorem anomaly_energy_decay {Cs Cd lam gam : ℝ} (hCs : 0 < Cs) (hCd : 0 < Cd)
    (hlam : 0 < lam) (hgam : 0 < gam) (xs xd : ℝ → ℝ) (t : ℝ)
    (hxs : HasDerivAt xs ((-lam * xs t - gam * (xs t - xd t)) / Cs) t)
    (hxd : HasDerivAt xd ((gam * (xs t - xd t)) / Cd) t) :
    0 < min (2 * lam / (Cs + 2 * Cd)) (gam / Cd) ∧
      deriv (fun t => (Cs * (xs t) ^ 2 + Cd * (xd t) ^ 2) / 2) t ≤
        -(min (2 * lam / (Cs + 2 * Cd)) (gam / Cd)) *
          ((Cs * (xs t) ^ 2 + Cd * (xd t) ^ 2) / 2) := by
  obtain ⟨hc, hbound⟩ :=
    anomaly_energy_dissipation_bound (xs := xs t) (xd := xd t) hCs hCd hlam hgam
  refine ⟨hc, ?_⟩
  rw [(anomaly_energy_hasDerivAt hCs hCd xs xd t hxs hxd).deriv]
  exact hbound.trans_eq (by ring)

/-- Anomaly-energy exponential bound: if `xs, xd` satisfy the anomaly ODEs
`Cs*xs' = -lam*xs - gam*(xs - xd)` and `Cd*xd' = gam*(xs - xd)` at every
`t >= 0`, with derivatives taken within `[0, ∞)` (so only the forward
trajectory matters, and `t = 0` needs only a right derivative), then
`E(t) = (Cs*xs^2 + Cd*xd^2)/2` satisfies `E(t) <= exp(-c*t) * E(0)` for
`t >= 0`, with `c = min (2*lam/(Cs + 2*Cd)) (gam/Cd) > 0`. The energy
derivative is computed as in `anomaly_energy_hasDerivAt`, within `[0, ∞)`;
with `anomaly_energy_dissipation_bound`, `le_exp_mul_of_hasDerivWithinAt_Ici`
gives the bound. -/
theorem anomaly_energy_exp_bound {Cs Cd lam gam : ℝ} (hCs : 0 < Cs) (hCd : 0 < Cd)
    (hlam : 0 < lam) (hgam : 0 < gam) (xs xd : ℝ → ℝ)
    (hxs : ∀ t, 0 ≤ t →
      HasDerivWithinAt xs ((-lam * xs t - gam * (xs t - xd t)) / Cs) (Set.Ici 0) t)
    (hxd : ∀ t, 0 ≤ t → HasDerivWithinAt xd ((gam * (xs t - xd t)) / Cd) (Set.Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) :
    (Cs * (xs t) ^ 2 + Cd * (xd t) ^ 2) / 2 ≤
      Real.exp (-(min (2 * lam / (Cs + 2 * Cd)) (gam / Cd)) * t) *
        ((Cs * (xs 0) ^ 2 + Cd * (xd 0) ^ 2) / 2) := by
  have hE : ∀ s, 0 ≤ s → HasDerivWithinAt (fun t => (Cs * (xs t) ^ 2 + Cd * (xd t) ^ 2) / 2)
      (-lam * (xs s) ^ 2 - gam * (xs s - xd s) ^ 2) (Set.Ici 0) s := by
    intro s hs
    have hxs2 : HasDerivWithinAt (fun t : ℝ => (xs t) ^ 2)
        (2 * xs s * ((-lam * xs s - gam * (xs s - xd s)) / Cs)) (Set.Ici 0) s := by
      simpa using (hxs s hs).fun_pow 2
    have hxd2 : HasDerivWithinAt (fun t : ℝ => (xd t) ^ 2)
        (2 * xd s * ((gam * (xs s - xd s)) / Cd)) (Set.Ici 0) s := by
      simpa using (hxd s hs).fun_pow 2
    convert ((hxs2.const_mul Cs).fun_add (hxd2.const_mul Cd)).div_const 2 using 1
    field_simp
    ring
  exact le_exp_mul_of_hasDerivWithinAt_Ici hE
    (fun s _ =>
      (anomaly_energy_dissipation_bound (xs := xs s) (xd := xd s) hCs hCd hlam hgam).2.trans_eq
        (by ring))
    ht

end EarthScience
