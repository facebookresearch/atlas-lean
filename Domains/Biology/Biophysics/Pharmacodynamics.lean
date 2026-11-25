/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.GoldbeterKoshland
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Normalized pharmacodynamic response

The baseline-plus-increment response
`response E0 Emax K h C = E0 + Emax * hill h K C` built on the canonical
activating Hill law `MathlibExt.Biology.Dynamics.GoldbeterKoshland.hill`.
Here `Emax` is the maximal increment above the baseline `E0`, not the
maximal total response: the proved range is `[E0, E0 + Emax]`, the
`C = K` value `E0 + Emax / 2` is half of that increment, and the
high-concentration limit is `E0 + Emax`. At zero concentration the
response is `E0`; it is monotone for `Emax ≥ 0` and strictly
increasing for `Emax > 0`.

This is a statement about the declared response model only. It is not
an empirical efficacy claim.

## References

* A. V. Hill, "The possible effects of the aggregation of the molecules
  of haemoglobin on its dissociation curves", J. Physiol. 40 (1910),
  iv-vii: the Hill fraction `C^h / (K^h + C^h)`.
* N. H. G. Holford and L. B. Sheiner, "Understanding the dose-effect
  relationship: clinical application of pharmacokinetic-pharmacodynamic
  models", Clin. Pharmacokinet. 6 (1981), 429-453: the `Emax` model in
  the baseline-plus-increment form `E = E0 + Emax * C / (EC50 + C)`,
  with `Emax` the maximal increment above the baseline `E0` and `EC50`
  the half-maximal concentration (here `K`, generalized to Hill
  coefficient `h`).
-/

@[expose] public section

open Real Filter Topology

namespace MathlibExt.Biology.Biophysics.Pharmacodynamics

/-- The baseline-plus-increment pharmacodynamic response: baseline `E0` plus maximal increment
`Emax` times the normalized Hill fraction with half-saturation `K` and Hill coefficient `h`. With
real powers and the conventions `x / 0 = 0`, `x ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and
`x ^ t = |x| ^ t * cos (π t)` for `x < 0`, it is defined for all real inputs: at `C = 0` the
fraction is `0` when `h ≠ 0`, at `h = 0` it is `1 / 2`, and it is `0` where `K ^ h + C ^ h = 0`. The
intended domain is `K > 0`, `h > 0`, `C ≥ 0`. -/
noncomputable def response (E0 Emax K h C : ℝ) : ℝ :=
  E0 + Emax * MathlibExt.Biology.Dynamics.GoldbeterKoshland.hill h K C

/-- The response unfolded to the explicit Hill fraction. -/
theorem response_eq (E0 Emax K h C : ℝ) :
    response E0 Emax K h C = E0 + Emax * (C ^ h / (K ^ h + C ^ h)) := rfl

private theorem pd_hillFrac_le {A u v : ℝ} (hA : 0 < A) (hu : 0 ≤ u) (huv : u ≤ v) :
    u / (A + u) ≤ v / (A + v) := by
  have hv : 0 ≤ v := le_trans hu huv
  have h1 : 0 < A + u := by linarith
  have h2 : 0 < A + v := by linarith
  have hmul : u * A ≤ v * A := mul_le_mul_of_nonneg_right huv (le_of_lt hA)
  have key : u * (A + v) ≤ v * (A + u) := by
    calc u * (A + v) = u * A + u * v := by ring
      _ ≤ v * A + u * v := add_le_add_left hmul _
      _ = v * (A + u) := by ring
  rw [le_div_iff₀ h2, div_mul_eq_mul_div, div_le_iff₀ h1]
  exact key

private theorem pd_hillFrac_lt {A u v : ℝ} (hA : 0 < A) (hu : 0 ≤ u) (huv : u < v) :
    u / (A + u) < v / (A + v) := by
  have hv : 0 ≤ v := le_of_lt (lt_of_le_of_lt hu huv)
  have h1 : 0 < A + u := by linarith
  have h2 : 0 < A + v := by linarith
  have hmul : u * A < v * A := mul_lt_mul_of_pos_right huv hA
  have key : u * (A + v) < v * (A + u) := by
    calc u * (A + v) = u * A + u * v := by ring
      _ < v * A + u * v := add_lt_add_left hmul _
      _ = v * (A + u) := by ring
  rw [lt_div_iff₀ h2, div_mul_eq_mul_div, div_lt_iff₀ h1]
  exact key

/-- **Normalized pharmacodynamic response.** For `E(C) = E0 + Emax *
(C^h / (K^h + C^h))` with `K > 0`, `h > 0`, `Emax ≥ 0` and `C ≥ 0`:
the response at zero concentration is `E0`, at `C = K` it is the
half-maximal `E0 + Emax / 2`, it is monotone and bounded between `E0`
and `E0 + Emax`, and it tends to `E0 + Emax` at high concentration. -/
private theorem pd_response_characterization {E0 Emax K h : ℝ}
    (hK : 0 < K) (hh : 0 < h) (hEmax : 0 ≤ Emax) :
    (E0 + Emax * ((0 : ℝ) ^ h / (K ^ h + (0 : ℝ) ^ h))) = E0 ∧
    (E0 + Emax * (K ^ h / (K ^ h + K ^ h))) = E0 + Emax / 2 ∧
    MonotoneOn (fun C : ℝ => E0 + Emax * (C ^ h / (K ^ h + C ^ h))) (Set.Ici 0) ∧
    (∀ C : ℝ, 0 ≤ C → E0 ≤ E0 + Emax * (C ^ h / (K ^ h + C ^ h)) ∧
      E0 + Emax * (C ^ h / (K ^ h + C ^ h)) ≤ E0 + Emax) ∧
    Tendsto (fun C : ℝ => E0 + Emax * (C ^ h / (K ^ h + C ^ h))) atTop
      (𝓝 (E0 + Emax)) := by
  have hKh : 0 < K ^ h := Real.rpow_pos_of_pos hK h
  refine ⟨?zero, ?half, ?mono, ?bounds, ?lim⟩
  · have h0 : (0 : ℝ) ^ h = 0 := Real.zero_rpow (ne_of_gt hh)
    rw [h0, add_zero, zero_div, mul_zero, add_zero]
  · have hKh' : K ^ h ≠ 0 := ne_of_gt hKh
    have hden : K ^ h + K ^ h ≠ 0 := ne_of_gt (by linarith)
    have hfrac : K ^ h / (K ^ h + K ^ h) = 1 / 2 := by
      field_simp
      ring
    rw [hfrac]
    ring
  · intro a ha b hb hab
    rw [Set.mem_Ici] at ha hb
    have huv : a ^ h ≤ b ^ h := Real.rpow_le_rpow ha hab (le_of_lt hh)
    have hfrac : a ^ h / (K ^ h + a ^ h) ≤ b ^ h / (K ^ h + b ^ h) :=
      pd_hillFrac_le hKh (Real.rpow_nonneg ha h) huv
    have hmul : Emax * (a ^ h / (K ^ h + a ^ h)) ≤ Emax * (b ^ h / (K ^ h + b ^ h)) :=
      mul_le_mul_of_nonneg_left hfrac hEmax
    exact add_le_add_right hmul E0
  · intro C hC
    have hCh : 0 ≤ C ^ h := Real.rpow_nonneg hC h
    have hden : 0 < K ^ h + C ^ h := by linarith
    have h0 : 0 ≤ C ^ h / (K ^ h + C ^ h) := div_nonneg hCh (le_of_lt hden)
    have h1 : C ^ h / (K ^ h + C ^ h) ≤ 1 := (div_le_one hden).mpr (by linarith)
    constructor
    · have hnn : 0 ≤ Emax * (C ^ h / (K ^ h + C ^ h)) := mul_nonneg hEmax h0
      linarith
    · have hle : Emax * (C ^ h / (K ^ h + C ^ h)) ≤ Emax * 1 :=
        mul_le_mul_of_nonneg_left h1 hEmax
      rw [mul_one] at hle
      linarith
  · have hpow : Tendsto (fun C : ℝ => C ^ h) atTop atTop := tendsto_rpow_atTop hh
    have hfun : (fun C : ℝ => K ^ h + C ^ h) = (fun C : ℝ => C ^ h + K ^ h) :=
      funext fun C => add_comm _ _
    have hsum : Tendsto (fun C : ℝ => K ^ h + C ^ h) atTop atTop := by
      rw [hfun]
      exact tendsto_atTop_add_const_right atTop (K ^ h) hpow
    have hfrac0 : Tendsto (fun C : ℝ => K ^ h / (K ^ h + C ^ h)) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop hsum (K ^ h)
    have hfrac1 : Tendsto (fun C : ℝ => 1 - K ^ h / (K ^ h + C ^ h)) atTop (𝓝 1) := by
      have h := Filter.Tendsto.const_sub (1 : ℝ) hfrac0
      rwa [sub_zero] at h
    have heq : (fun C : ℝ => C ^ h / (K ^ h + C ^ h)) =ᶠ[atTop]
        (fun C : ℝ => 1 - K ^ h / (K ^ h + C ^ h)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with C hC
      have hCh : 0 ≤ C ^ h := Real.rpow_nonneg hC h
      have hden : K ^ h + C ^ h ≠ 0 := ne_of_gt (by linarith)
      field_simp
      ring
    have hlim : Tendsto (fun C : ℝ => C ^ h / (K ^ h + C ^ h)) atTop (𝓝 1) :=
      Tendsto.congr' heq.symm hfrac1
    have hEmaxT : Tendsto (fun C : ℝ => Emax * (C ^ h / (K ^ h + C ^ h))) atTop (𝓝 Emax) := by
      have h := Filter.Tendsto.const_mul Emax hlim
      rwa [mul_one] at h
    exact Filter.Tendsto.const_add E0 hEmaxT

/-- With `Emax > 0` the normalized response is strictly increasing on
nonnegative concentrations. -/
private theorem pd_response_strictMonoOn {E0 Emax K h : ℝ}
    (hK : 0 < K) (hh : 0 < h) (hEmax : 0 < Emax) :
    StrictMonoOn (fun C : ℝ => E0 + Emax * (C ^ h / (K ^ h + C ^ h))) (Set.Ici 0) := by
  intro a ha b hb hab
  rw [Set.mem_Ici] at ha hb
  have hKh : 0 < K ^ h := Real.rpow_pos_of_pos hK h
  have huv : a ^ h < b ^ h := Real.rpow_lt_rpow ha hab hh
  have hfrac : a ^ h / (K ^ h + a ^ h) < b ^ h / (K ^ h + b ^ h) :=
    pd_hillFrac_lt hKh (Real.rpow_nonneg ha h) huv
  have hmul : Emax * (a ^ h / (K ^ h + a ^ h)) < Emax * (b ^ h / (K ^ h + b ^ h)) :=
    mul_lt_mul_of_pos_left hfrac hEmax
  exact add_lt_add_right hmul E0

/-- For `K > 0`, `h > 0` and `Emax ≥ 0`, at zero concentration the response is the baseline `E0`. -/
theorem response_at_zero {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h)
    (hEmax : 0 ≤ Emax) : response E0 Emax K h 0 = E0 := by
  rw [response_eq]
  exact (pd_response_characterization (E0 := E0) (Emax := Emax) (K := K) (h := h)
      hK hh hEmax).1

/-- For `K > 0`, `h > 0` and `Emax ≥ 0`, at `C = K` the response is the baseline plus half the
maximal increment. -/
theorem response_at_half {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h)
    (hEmax : 0 ≤ Emax) : response E0 Emax K h K = E0 + Emax / 2 := by
  rw [response_eq]
  exact (pd_response_characterization (E0 := E0) (Emax := Emax) (K := K) (h := h)
      hK hh hEmax).2.1

/-- For `K > 0`, `h > 0` and `Emax ≥ 0`, the response is monotone (nondecreasing) on nonnegative
concentrations. -/
theorem response_monotoneOn {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h)
    (hEmax : 0 ≤ Emax) : MonotoneOn (response E0 Emax K h) (Set.Ici 0) := by
  have hm := (pd_response_characterization (E0 := E0) (Emax := Emax) (K := K) (h := h)
      hK hh hEmax).2.2.1
  intro a ha b hb hab
  rw [response_eq, response_eq]
  exact hm ha hb hab

/-- For `K > 0`, `h > 0`, `Emax ≥ 0` and `C ≥ 0`, the response stays between the baseline and
baseline plus the maximal increment. -/
theorem response_bounds {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h)
    (hEmax : 0 ≤ Emax) (C : ℝ) (hC : 0 ≤ C) :
    E0 ≤ response E0 Emax K h C ∧ response E0 Emax K h C ≤ E0 + Emax := by
  have hb := (pd_response_characterization (E0 := E0) (Emax := Emax) (K := K) (h := h)
      hK hh hEmax).2.2.2.1 C hC
  rw [response_eq]
  exact hb

/-- For `K > 0`, `h > 0` and `Emax ≥ 0`, at high concentration the response tends to baseline plus
the maximal increment. -/
theorem response_tendsto {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h)
    (hEmax : 0 ≤ Emax) :
    Tendsto (response E0 Emax K h) atTop (𝓝 (E0 + Emax)) := by
  have hlim := (pd_response_characterization (E0 := E0) (Emax := Emax) (K := K) (h := h)
      hK hh hEmax).2.2.2.2
  refine hlim.congr (fun C => ?_)
  exact (response_eq E0 Emax K h C).symm

/-- For `K > 0`, `h > 0` and a positive maximal increment `Emax > 0`, the response is strictly
increasing on nonnegative concentrations. -/
theorem response_strictMonoOn {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h)
    (hEmax : 0 < Emax) : StrictMonoOn (response E0 Emax K h) (Set.Ici 0) := by
  have hs := pd_response_strictMonoOn (E0 := E0) (Emax := Emax) (K := K) (h := h)
      hK hh hEmax
  intro a ha b hb hab
  rw [response_eq, response_eq]
  exact hs ha hb hab

set_option linter.unusedVariables false in
/-- **Inverse pharmacodynamic response.** For the response
`E(C) = E0 + Emax * (C^h / (K^h + C^h))` with `K > 0`, `h > 0`,
`Emax > 0`, every interior response value `E0 < E < E0 + Emax` is
attained at the concentration
`C = K * ((E - E0) / (E0 + Emax - E))^(1/h)`. The endpoints are
excluded: `E = E0` is attained only at `C = 0` and `E0 + Emax` is not
attained at any finite concentration. -/
private theorem pd_inverse_response {E0 Emax K h E : ℝ}
    (hK : 0 < K) (hh : 0 < h) (hEmax : 0 < Emax)
    (hlo : E0 < E) (hhi : E < E0 + Emax) :
    E0 + Emax * ((K * ((E - E0) / (E0 + Emax - E)) ^ (1 / h)) ^ h /
      (K ^ h + (K * ((E - E0) / (E0 + Emax - E)) ^ (1 / h)) ^ h)) = E := by
  have ha : 0 < E - E0 := sub_pos.mpr hlo
  have hb : 0 < E0 + Emax - E := by linarith
  have hrpos : 0 < (E - E0) / (E0 + Emax - E) := div_pos ha hb
  have hpow : (((E - E0) / (E0 + Emax - E)) ^ (1 / h)) ^ h
      = (E - E0) / (E0 + Emax - E) := by
    rw [← Real.rpow_mul (le_of_lt hrpos), div_mul_cancel₀ _ (ne_of_gt hh),
      Real.rpow_one]
  have hCh : (K * ((E - E0) / (E0 + Emax - E)) ^ (1 / h)) ^ h
      = K ^ h * ((E - E0) / (E0 + Emax - E)) := by
    rw [Real.mul_rpow (le_of_lt hK) (Real.rpow_nonneg (le_of_lt hrpos) _), hpow]
  have hKh : 0 < K ^ h := Real.rpow_pos_of_pos hK h
  rw [hCh]
  have hden : K ^ h + K ^ h * ((E - E0) / (E0 + Emax - E)) ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hKh (le_of_lt (mul_pos hKh hrpos)))
  have hbne : E0 + Emax - E ≠ 0 := ne_of_gt hb
  field_simp
  ring

set_option linter.unusedVariables false in
/-- **Concentration-unit scaling.** Rescaling the concentration unit
scales `C` and `K` together and does not change the response: for
`s > 0`, `C ≥ 0`, the Hill fraction at `(s * C, s * K)` equals the one
at `(C, K)`. Scaling only one of them changes the response in general. -/
private theorem pd_response_scale {Emax K h C s : ℝ}
    (hK : 0 < K) (hh : 0 < h) (hC : 0 ≤ C) (hs : 0 < s) :
    (s * C) ^ h / ((s * K) ^ h + (s * C) ^ h) = C ^ h / (K ^ h + C ^ h) := by
  rw [Real.mul_rpow (le_of_lt hs) hC, Real.mul_rpow (le_of_lt hs) (le_of_lt hK)]
  have hsh : s ^ h ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hs h)
  have hfac : s ^ h * K ^ h + s ^ h * C ^ h = s ^ h * (K ^ h + C ^ h) := by ring
  rw [hfac, mul_div_mul_left _ _ hsh]

/-- The concentration attaining an interior response value `E`:
`K * ((E - E0) / (E0 + Emax - E))^(1/h)`. It is defined for all real inputs (real power, with
`x / 0 = 0`): it is `K` when `h = 0`, and `0` when `h ≠ 0` and `E = E0` or `E = E0 + Emax`; a
negative base `x` gives `|x| ^ (1 / h) * cos (π / h)`. The intended domain is `K > 0`, `h > 0`,
`Emax > 0` and `E0 < E < E0 + Emax`. -/
noncomputable def inverseConcentration (E0 Emax K h E : ℝ) : ℝ :=
  K * ((E - E0) / (E0 + Emax - E)) ^ (1 / h)

/-- For `K > 0`, `h > 0` and `Emax > 0`, the inverse concentration attains its response value:
`response E0 Emax K h (inverseConcentration E0 Emax K h E) = E` for `E0 < E < E0 + Emax`. -/
theorem response_inverseConcentration {E0 Emax K h E : ℝ}
    (hK : 0 < K) (hh : 0 < h) (hEmax : 0 < Emax)
    (hlo : E0 < E) (hhi : E < E0 + Emax) :
    response E0 Emax K h (inverseConcentration E0 Emax K h E) = E := by
  rw [response_eq]
  exact pd_inverse_response hK hh hEmax hlo hhi

/-- For `K > 0`, `h > 0`, `C ≥ 0` and `s > 0`, rescaling the concentration unit scales `C` and `K`
together and does not change the response. -/
theorem response_scale {E0 Emax K h C s : ℝ}
    (hK : 0 < K) (hh : 0 < h) (hC : 0 ≤ C) (hs : 0 < s) :
    response E0 Emax (s * K) h (s * C) = response E0 Emax K h C := by
  rw [response_eq, response_eq]
  have h := pd_response_scale hK hh hC hs (Emax := Emax)
  rw [h]

end MathlibExt.Biology.Biophysics.Pharmacodynamics
