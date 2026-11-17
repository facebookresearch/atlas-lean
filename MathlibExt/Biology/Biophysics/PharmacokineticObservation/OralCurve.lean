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

/-- **Flip-flop pair.** When `ka` is also unknown, swapping
the absorption and elimination labels (with the denominator sign)
leaves the difference-of-exponentials curve unchanged, so the
curve alone does not say which rate is absorption. -/
lemma oral_flip_flop {A ka k t : ℝ} :
    A * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k) =
      A * (Real.exp (-ka * t) - Real.exp (-k * t)) / (k - ka) := by
  have h1 : A * (Real.exp (-ka * t) - Real.exp (-k * t))
      = - (A * (Real.exp (-k * t) - Real.exp (-ka * t))) := by ring
  have h2 : (k - ka : ℝ) = -(ka - k) := by ring
  rw [h1, h2, neg_div_neg_eq]

#print axioms oral_flip_flop

end MathlibExt.Biology.Biophysics.PharmacokineticObservation.OralCurve
