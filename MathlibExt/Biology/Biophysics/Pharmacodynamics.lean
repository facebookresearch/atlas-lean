/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.GoldbeterKoshland
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Normalized pharmacodynamic response

The normalized response `response E0 Emax K h C = E0 + Emax * hill h K C`
built on the canonical activating Hill law
`MathlibExt.Biology.Dynamics.GoldbeterKoshland.hill`: at zero
concentration it is `E0`, at `C = K` it is half-maximal, it is monotone
and bounded between `E0` and `E0 + Emax` for `Emax ≥ 0`, strictly
increasing for `Emax > 0`, and it tends to `E0 + Emax` at high
concentration.

This is a statement about the declared response model only. It is not
an empirical efficacy claim.
-/

@[expose] public section

open Real Filter Topology

namespace MathlibExt.Biology.Biophysics.Pharmacodynamics

/-- The normalized pharmacodynamic response with baseline `E0`, maximal
effect `Emax`, half-saturation `K` and Hill coefficient `h`. -/
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
theorem pd_response_characterization {E0 Emax K h : ℝ}
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
theorem pd_response_strictMonoOn {E0 Emax K h : ℝ}
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

end MathlibExt.Biology.Biophysics.Pharmacodynamics
