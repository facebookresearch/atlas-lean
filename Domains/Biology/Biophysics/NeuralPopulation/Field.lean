/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Wilson-Cowan neural population field derivatives

The two-population Wilson-Cowan field with refractory factors,
`E(x, y) = (-x + (1 - rE * x) * fE (hE - wEI * y + wEE * x)) / tauE` and
`I(x, y) = (-y + (1 - rI * y) * fI (hI + wIE * x - wII * y)) / tauI`,
has the exact partial derivatives stated below, including the
`-r * f` contribution from differentiating the refractory factor
`1 - r * x`. At `r = 0` the formulas recover the simplified field.

These are local derivative statements about the declared field only:
no global solution, stability, or trajectory claim is made from a
Jacobian.

## References

* H. R. Wilson and J. D. Cowan, "Excitatory and inhibitory
  interactions in localized populations of model neurons",
  Biophys. J. 12 (1972), 1-24. This module states the normalized
  specialization of the classical refractory factors
  `(kE - rE * x)`, `(kI - rI * y)` with `kE = kI = 1`.
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.NeuralPopulation.Field

/-- **Wilson-Cowan field derivatives (E population).** For the field
component `E(x, y) = (-x + (1 - rE * x) * fE (hE - wEI * y + wEE * x)) / tauE`
with gain `fE` differentiable at the E input with derivative `fE'`,
the partial derivatives are
`∂E/∂x = (-1 - rE * fE + (1 - rE * x) * fE' * wEE) / tauE` and
`∂E/∂y = ((1 - rE * x) * fE' * (-wEI)) / tauE`. The `-rE * fE` term
comes from differentiating the refractory factor `1 - rE * x`. In the
model `tauE > 0`; at `tauE = 0` both sides are `0` by the convention
`q / 0 = 0`. -/
theorem rate_field_E_deriv {tauE rE x y hE wEI wEE : ℝ} {fE : ℝ → ℝ} {fE' : ℝ}
    (hfE : HasDerivAt fE fE' (hE - wEI * y + wEE * x)) :
    HasDerivAt (fun x' => (-x' + (1 - rE * x') * fE (hE - wEI * y + wEE * x')) / tauE)
      ((-1 - rE * fE (hE - wEI * y + wEE * x) + (1 - rE * x) * fE' * wEE) / tauE) x ∧
    HasDerivAt (fun y' => (-x + (1 - rE * x) * fE (hE - wEI * y' + wEE * x)) / tauE)
      ((1 - rE * x) * fE' * (-wEI) / tauE) y := by
  constructor
  · have h_id : HasDerivAt (fun x' : ℝ => x') 1 x := hasDerivAt_id' x
    have h_neg : HasDerivAt (fun x' : ℝ => -x') (-1) x := h_id.fun_neg
    have h_mul : HasDerivAt (fun x' : ℝ => rE * x') (rE * 1) x :=
      HasDerivAt.const_mul rE h_id
    have h_ref : HasDerivAt (fun x' : ℝ => 1 - rE * x') (-rE) x := by
      have h := HasDerivAt.const_sub 1 h_mul
      convert h using 1
      ring
    have h_wEE : HasDerivAt (fun x' : ℝ => wEE * x') (wEE * 1) x :=
      HasDerivAt.const_mul wEE h_id
    have h_inner : HasDerivAt (fun x' : ℝ => hE - wEI * y + wEE * x') wEE x := by
      have h := HasDerivAt.const_add (hE - wEI * y) h_wEE
      convert h using 1
      ring
    have h_comp : HasDerivAt (fun x' : ℝ => fE (hE - wEI * y + wEE * x')) (fE' * wEE) x :=
      hfE.comp x h_inner
    have h_prod : HasDerivAt (fun x' : ℝ => (1 - rE * x') * fE (hE - wEI * y + wEE * x'))
        ((-rE) * fE (hE - wEI * y + wEE * x) + (1 - rE * x) * (fE' * wEE)) x :=
      h_ref.fun_mul h_comp
    have h_sum : HasDerivAt (fun x' : ℝ => -x' + (1 - rE * x') * fE (hE - wEI * y + wEE * x'))
        ((-1) + ((-rE) * fE (hE - wEI * y + wEE * x) + (1 - rE * x) * (fE' * wEE))) x :=
      h_neg.fun_add h_prod
    have h_div := h_sum.div_const tauE
    convert h_div using 1
    ring
  · have h_id : HasDerivAt (fun y' : ℝ => y') 1 y := hasDerivAt_id' y
    have h_mul : HasDerivAt (fun y' : ℝ => wEI * y') (wEI * 1) y :=
      HasDerivAt.const_mul wEI h_id
    have h_sub : HasDerivAt (fun y' : ℝ => hE - wEI * y') (-(wEI * 1)) y :=
      HasDerivAt.const_sub hE h_mul
    have h_inner : HasDerivAt (fun y' : ℝ => hE - wEI * y' + wEE * x) (-wEI) y := by
      have h := h_sub.add_const (wEE * x)
      convert h using 1
      ring
    have h_comp : HasDerivAt (fun y' : ℝ => fE (hE - wEI * y' + wEE * x)) (fE' * (-wEI)) y :=
      hfE.comp y h_inner
    have h_prod : HasDerivAt (fun y' : ℝ => (1 - rE * x) * fE (hE - wEI * y' + wEE * x))
        ((1 - rE * x) * (fE' * (-wEI))) y :=
      HasDerivAt.const_mul (1 - rE * x) h_comp
    have h_const : HasDerivAt (fun _ : ℝ => -x) 0 y := hasDerivAt_const y (-x)
    have h_sum : HasDerivAt (fun y' : ℝ => -x + (1 - rE * x) * fE (hE - wEI * y' + wEE * x))
        (0 + (1 - rE * x) * (fE' * (-wEI))) y :=
      h_const.fun_add h_prod
    have h_div := h_sum.div_const tauE
    convert h_div using 1
    ring

/-- **Wilson-Cowan field derivatives (I population).** For
`I(x, y) = (-y + (1 - rI * y) * fI (hI + wIE * x - wII * y)) / tauI`
with gain derivative `fI'` at the I input, the partial derivatives are
`∂I/∂y = (-1 - rI * fI + (1 - rI * y) * fI' * (-wII)) / tauI` and
`∂I/∂x = ((1 - rI * y) * fI' * wIE) / tauI`. In the model `tauI > 0`; at
`tauI = 0` both sides are `0` by the convention `q / 0 = 0`. -/
theorem rate_field_I_deriv {tauI rI x y hI wIE wII : ℝ} {fI : ℝ → ℝ} {fI' : ℝ}
    (hfI : HasDerivAt fI fI' (hI + wIE * x - wII * y)) :
    HasDerivAt (fun y' => (-y' + (1 - rI * y') * fI (hI + wIE * x - wII * y')) / tauI)
      ((-1 - rI * fI (hI + wIE * x - wII * y) + (1 - rI * y) * fI' * (-wII)) / tauI) y ∧
    HasDerivAt (fun x' => (-y + (1 - rI * y) * fI (hI + wIE * x' - wII * y)) / tauI)
      ((1 - rI * y) * fI' * wIE / tauI) x := by
  constructor
  · have h_id : HasDerivAt (fun y' : ℝ => y') 1 y := hasDerivAt_id' y
    have h_neg : HasDerivAt (fun y' : ℝ => -y') (-1) y := h_id.fun_neg
    have h_mul : HasDerivAt (fun y' : ℝ => rI * y') (rI * 1) y :=
      HasDerivAt.const_mul rI h_id
    have h_ref : HasDerivAt (fun y' : ℝ => 1 - rI * y') (-rI) y := by
      have h := HasDerivAt.const_sub 1 h_mul
      convert h using 1
      ring
    have h_wII : HasDerivAt (fun y' : ℝ => wII * y') (wII * 1) y :=
      HasDerivAt.const_mul wII h_id
    have h_inner : HasDerivAt (fun y' : ℝ => hI + wIE * x - wII * y') (-wII) y := by
      have h := HasDerivAt.const_sub (hI + wIE * x) h_wII
      convert h using 1
      ring
    have h_comp : HasDerivAt (fun y' : ℝ => fI (hI + wIE * x - wII * y')) (fI' * (-wII)) y :=
      hfI.comp y h_inner
    have h_prod : HasDerivAt (fun y' : ℝ => (1 - rI * y') * fI (hI + wIE * x - wII * y'))
        ((-rI) * fI (hI + wIE * x - wII * y) + (1 - rI * y) * (fI' * (-wII))) y :=
      h_ref.fun_mul h_comp
    have h_sum : HasDerivAt (fun y' : ℝ => -y' + (1 - rI * y') * fI (hI + wIE * x - wII * y'))
        ((-1) + ((-rI) * fI (hI + wIE * x - wII * y) + (1 - rI * y) * (fI' * (-wII)))) y :=
      h_neg.fun_add h_prod
    have h_div := h_sum.div_const tauI
    convert h_div using 1
    ring
  · have h_id : HasDerivAt (fun x' : ℝ => x') 1 x := hasDerivAt_id' x
    have h_mul : HasDerivAt (fun x' : ℝ => wIE * x') (wIE * 1) x :=
      HasDerivAt.const_mul wIE h_id
    have h_add : HasDerivAt (fun x' : ℝ => hI + wIE * x') (wIE * 1) x :=
      HasDerivAt.const_add hI h_mul
    have h_inner : HasDerivAt (fun x' : ℝ => hI + wIE * x' - wII * y) wIE x := by
      have h := h_add.sub_const (wII * y)
      convert h using 1
      ring
    have h_comp : HasDerivAt (fun x' : ℝ => fI (hI + wIE * x' - wII * y)) (fI' * wIE) x :=
      hfI.comp x h_inner
    have h_prod : HasDerivAt (fun x' : ℝ => (1 - rI * y) * fI (hI + wIE * x' - wII * y))
        ((1 - rI * y) * (fI' * wIE)) x :=
      HasDerivAt.const_mul (1 - rI * y) h_comp
    have h_const : HasDerivAt (fun _ : ℝ => -y) 0 x := hasDerivAt_const x (-y)
    have h_sum : HasDerivAt (fun x' : ℝ => -y + (1 - rI * y) * fI (hI + wIE * x' - wII * y))
        (0 + (1 - rI * y) * (fI' * wIE)) x :=
      h_const.fun_add h_prod
    have h_div := h_sum.div_const tauI
    convert h_div using 1
    ring

end MathlibExt.Biology.Biophysics.NeuralPopulation.Field
