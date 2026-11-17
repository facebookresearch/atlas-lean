/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Oral curve identification

The oral concentration curve at fixed known absorption rate is preserved by common
scaling of `(F, V, CL)`, and at unknown `ka` the absorption/elimination labels can be swapped without changing the curve: neither scale nor the flip-flop assignment is identified from the curve alone.
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.PharmacokineticObservation.OralCurve

/-- **Oral common scaling.** With fixed known `ka > 0`, dose `D`,
rates `k = CL / V`, the oral concentration curve
`C(t) = F * D * ka * (exp (-(CL/V) t) - exp (-ka t)) / (V * (ka - CL/V))`
is preserved by the common scaling `(F, V, CL) ↦ (F * s, V * s, CL * s)`
for any `s ≠ 0` (admissible scalings have `s > 0`, `F * s ≤ 1`):
scale is not identified from oral curves alone. -/
lemma oral_scaling_curve {F D ka V CL s t : ℝ} (hV : V ≠ 0)
    (hs : s ≠ 0) (hden : ka - CL / V ≠ 0) :
    F * D * ka * (Real.exp (-(CL / V) * t) - Real.exp (-ka * t)) / (V * (ka - CL / V)) =
      (F * s) * D * ka * (Real.exp (-((CL * s) / (V * s)) * t) - Real.exp (-ka * t)) /
        ((V * s) * (ka - (CL * s) / (V * s))) := by
  have hVs : V * s ≠ 0 := mul_ne_zero hV hs
  have h1 : (CL * s) / (V * s) = CL / V := by
    rw [div_eq_div_iff hVs hV]
    ring
  rw [h1]
  have hD : V * (ka - CL / V) ≠ 0 := mul_ne_zero hV hden
  have hD' : (V * s) * (ka - CL / V) ≠ 0 := mul_ne_zero hVs hden
  rw [div_eq_div_iff hD hD']
  ring

/-- **Flip-flop parameter transformation.** Two admissible oral
parameter tuples at distinct positive rates give the same curve at
time `t` when the second absorbs at the first's elimination rate
and eliminates at the first's absorption rate, with amplitude
adjusted to the new prefactor: concretely the original tuple
`(F, D, ka, V, CL)` and the flipped tuple share the curve exactly
when the flipped prefactor is chosen so that both sides agree; the
instance below states this with the transformation
`ka ↦ CL / V`, `CL ↦ ka * V`, which exchanges the two exponential
rates while keeping `F`, `D`, `V` fixed. The prefactor identity is
part of the statement: a naive label swap without transforming
`CL` does not preserve the curve. Equal rates are excluded (the
denominator vanishes; the limiting equal-rate form is different). -/
lemma oral_flip_flop {F D ka V CL t : ℝ} (hV : V ≠ 0)
    (hka : ka ≠ CL / V) (hka0 : ka ≠ 0) (hCL0 : CL ≠ 0) :
    F * D * ka * (Real.exp (-(CL / V) * t) - Real.exp (-ka * t)) /
        (V * (ka - CL / V)) =
      (F * D * (CL / V) * (Real.exp (-ka * t) - Real.exp (-(CL / V) * t)) *
        (ka / (CL / V))) / (V * (CL / V - ka)) := by
  have hd1 : (V * (ka - CL / V)) ≠ 0 :=
    mul_ne_zero hV (sub_ne_zero.mpr hka)
  have hd2 : (V * (CL / V - ka)) * (ka / (CL / V)) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero hV (sub_ne_zero.mpr (Ne.symm hka))
    · exact div_ne_zero hka0 (div_ne_zero hCL0 hV)
  have hd2' : (V * (CL / V - ka)) ≠ 0 :=
    mul_ne_zero hV (sub_ne_zero.mpr (Ne.symm hka))
  have hne1 : (-CL + V * ka) ≠ 0 := by
    by_contra h
    apply hka
    have h2 : CL = V * ka := by
      have h3 : -CL + V * ka = 0 := h
      linarith
    rw [h2]
    field_simp
  have hne : (CL - V * ka) ≠ 0 := by
    by_contra h
    apply hka
    have h2 : CL = V * ka := by linarith
    rw [h2]
    field_simp
  field_simp
  have hneg : CL - ka * V = -(ka * V - CL) := by ring
  have hnum : Real.exp (-(ka * t)) - Real.exp (-(CL * t / V)) =
      -(Real.exp (-(CL * t / V)) - Real.exp (-(ka * t))) := by ring
  rw [hneg, hnum]
  simp only [mul_neg, neg_div_neg_eq]

end MathlibExt.Biology.Biophysics.PharmacokineticObservation.OralCurve
