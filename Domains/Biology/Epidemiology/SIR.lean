/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Kermack–McKendrick SIR epidemic model

A closed population of size `N` is split into susceptible `S`, infectious `I` and removed `R`
individuals. With transmission rate `β` and removal rate `γ` (per unit time), the
Kermack–McKendrick SIR model is

  `S' = -β S I / N`,   `I' = β S I / N - γ I`,   `R' = γ I`.

The basic reproduction number is `R₀ = β / γ`: the expected number of secondary infections caused
by one infectious individual in a fully susceptible population. `IsSolution β γ N S I R` states
that `(S, I, R)` solves the system for all times `t ≥ 0` (derivatives in the sense of
`HasDerivAt`).

The epidemiological parameter domain is `β ≥ 0`, `γ > 0`, `N > 0` (and `N = S + I + R`). The
conservation laws below are stated for all real parameters, with the hypotheses each proof
needs; note that for `N = 0` Lean's convention `a / 0 = 0` turns the system into `S' = 0`,
`I' = -γ I`, `R' = γ I`, for which the identities hold trivially.

## Main results

* `IsSolution.total_eq`: the population `S + I + R` is constant.
* `IsSolution.deriv_infected_pos_iff`: the threshold theorem — the epidemic initially grows,
  `I'(0) > 0`, iff `R₀ S(0) / N > 1` (for `I(0) > 0`, `γ > 0`, `N > 0`).
* `IsSolution.susceptible_mul_exp_eq`: `S(t) e^{R₀ R(t) / N}` is conserved.
* `IsSolution.final_size`: the final-size relation `S(∞) = S(0) e^{-R₀ (R(∞) - R(0)) / N}`,
  for solutions along which `S` and `R` converge.
* `IsSolution.final_size_eq`: the classical final-size equation
  `S(∞) = S(0) e^{-R₀ (N - S(∞)) / N}` when `S + I + R = N`, `R(0) = 0` and `I(t) → 0`.

Existence of solutions and convergence of `S`, `I`, `R` are not proved here.

## References

* W. O. Kermack and A. G. McKendrick, *A contribution to the mathematical theory of epidemics*,
  Proc. R. Soc. Lond. A 115 (1927) 700–721.
* H. W. Hethcote, *The mathematics of infectious diseases*, SIAM Review 42 (2000) 599–653, §2.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SIR

/-- `(S, I, R)` solves the Kermack–McKendrick SIR system with transmission rate `β`, removal
rate `γ` and population size `N` for all times `t ≥ 0`:
`S' = -β S I / N`, `I' = β S I / N - γ I`, `R' = γ I`. -/
structure IsSolution (β γ N : ℝ) (S I R : ℝ → ℝ) : Prop where
  /-- Susceptibles are infected at rate `β S I / N`. -/
  hasDerivAt_susceptible : ∀ t, 0 ≤ t → HasDerivAt S (-(β * S t * I t / N)) t
  /-- Infectives gain new infections and are removed at rate `γ`. -/
  hasDerivAt_infected : ∀ t, 0 ≤ t → HasDerivAt I (β * S t * I t / N - γ * I t) t
  /-- Removed individuals accumulate at rate `γ I`. -/
  hasDerivAt_removed : ∀ t, 0 ≤ t → HasDerivAt R (γ * I t) t

/-- A function with zero derivative on `[0, ∞)` is constant there. -/
private theorem eq_zero_of_hasDerivAt {F : ℝ → ℝ} (hF : ∀ t, 0 ≤ t → HasDerivAt F 0 t)
    {t : ℝ} (ht : 0 ≤ t) : F t = F 0 :=
  constant_of_has_deriv_right_zero (b := t)
    (fun s hs => (hF s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hF s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩

namespace IsSolution

variable {β γ N : ℝ} {S I R : ℝ → ℝ}

/-- **Conservation of the population.** Along a solution, `S + I + R` is constant on
`[0, ∞)`. -/
theorem total_eq (h : IsSolution β γ N S I R) {t : ℝ} (ht : 0 ≤ t) :
    S t + I t + R t = S 0 + I 0 + R 0 :=
  eq_zero_of_hasDerivAt (F := fun s => S s + I s + R s) (fun s hs => by
    convert ((h.hasDerivAt_susceptible s hs).add (h.hasDerivAt_infected s hs)).add
      (h.hasDerivAt_removed s hs) using 1
    ring) ht

/-- **Threshold theorem (Kermack–McKendrick 1927).** If initially `I(0) > 0`, with `γ > 0` and
`N > 0`, the number of infectives initially increases, `I'(0) > 0`, iff
`R₀ S(0) / N > 1` with `R₀ = β / γ`. -/
theorem deriv_infected_pos_iff (h : IsSolution β γ N S I R) (hγ : 0 < γ) (hN : 0 < N)
    (hI : 0 < I 0) : 0 < deriv I 0 ↔ 1 < β / γ * S 0 / N := by
  rw [(h.hasDerivAt_infected 0 le_rfl).deriv]
  have hfac : β * S 0 * I 0 / N - γ * I 0 = γ * I 0 * (β / γ * S 0 / N - 1) := by
    field_simp
  rw [hfac, mul_pos_iff_of_pos_left (mul_pos hγ hI), sub_pos]

/-- **Conserved quantity behind the final-size relation.** For `γ ≠ 0`, the quantity
`S(t) e^{R₀ R(t) / N}` (`R₀ = β / γ`) is constant along a solution on `[0, ∞)`. -/
theorem susceptible_mul_exp_eq (h : IsSolution β γ N S I R) (hγ : γ ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    S t * exp (β / γ * R t / N) = S 0 * exp (β / γ * R 0 / N) :=
  eq_zero_of_hasDerivAt (F := fun s => S s * exp (β / γ * R s / N)) (fun s hs => by
    have hR := (((h.hasDerivAt_removed s hs).const_mul (β / γ)).div_const N).exp
    convert (h.hasDerivAt_susceptible s hs).mul hR using 1
    field_simp
    ring) ht

/-- **Final-size relation (Kermack–McKendrick 1927).** If along a solution (`γ ≠ 0`)
`S(t) → S∞` and `R(t) → R∞` as `t → ∞`, then `S∞ = S(0) e^{-R₀ (R∞ - R(0)) / N}` with
`R₀ = β / γ`. See `final_size_eq` for the classical form. -/
theorem final_size (h : IsSolution β γ N S I R) (hγ : γ ≠ 0) {Sinf Rinf : ℝ}
    (hS : Tendsto S atTop (𝓝 Sinf)) (hR : Tendsto R atTop (𝓝 Rinf)) :
    Sinf = S 0 * exp (-(β / γ * (Rinf - R 0) / N)) := by
  have hlim : Tendsto (fun t => S t * exp (β / γ * R t / N)) atTop
      (𝓝 (Sinf * exp (β / γ * Rinf / N))) :=
    hS.mul ((continuous_exp.tendsto _).comp ((hR.const_mul (β / γ)).div_const N))
  have hconst : Tendsto (fun t => S t * exp (β / γ * R t / N)) atTop
      (𝓝 (S 0 * exp (β / γ * R 0 / N))) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨0, fun t ht =>
      (h.susceptible_mul_exp_eq hγ ht).symm⟩)
  have heq := tendsto_nhds_unique hlim hconst
  have hpos := exp_pos (β / γ * Rinf / N)
  rw [show -(β / γ * (Rinf - R 0) / N) = β / γ * R 0 / N - β / γ * Rinf / N by ring, exp_sub,
    ← mul_div_assoc, ← heq, mul_div_cancel_right₀ _ hpos.ne']

/-- **Final-size equation (Kermack–McKendrick 1927).** If the population is `N = S + I + R`,
nobody is removed initially (`R(0) = 0`), `γ ≠ 0`, `S(t) → S∞` and the epidemic dies out
(`I(t) → 0`), then `S∞ = S(0) e^{-R₀ (N - S∞) / N}` with `R₀ = β / γ`. -/
theorem final_size_eq (h : IsSolution β γ N S I R) (hγ : γ ≠ 0)
    (hN : S 0 + I 0 + R 0 = N) (hR0 : R 0 = 0) {Sinf : ℝ} (hS : Tendsto S atTop (𝓝 Sinf))
    (hI : Tendsto I atTop (𝓝 0)) :
    Sinf = S 0 * exp (-(β / γ * (N - Sinf) / N)) := by
  have hR : Tendsto R atTop (𝓝 (N - Sinf - 0)) :=
    ((tendsto_const_nhds.sub hS).sub hI).congr' (eventually_atTop.2 ⟨0, fun t ht => by
      have := h.total_eq ht
      linarith⟩)
  have := h.final_size hγ hS hR
  rwa [hR0, sub_zero, sub_zero] at this

end IsSolution

end MathlibExt.Biology.Epidemiology.SIR
