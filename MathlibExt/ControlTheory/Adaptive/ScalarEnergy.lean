/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Basic.Real.Basic

/-!
# Scalar MRAC energy derivative

For a scalar plant with model-reference adaptive control, the
energy `V = ((x - xm) ^ 2 + (a - ahat) ^ 2 / gamma) / 2` built
from the tracking error and the parameter error has derivative
`-lam * (x - xm) ^ 2` along the plant, reference, and
adaptation laws. This module records that one-point derivative
identity.
-/

@[expose] public section

namespace ControlTheory

/-- Derivative of the scalar model-reference adaptive control
energy. With tracking error `e = x - xm`, parameter error
`a - ahat`, adaptation gain `gamma`, and energy
`V = (e ^ 2 + (a - ahat) ^ 2 / gamma) / 2`, the plant law
`x' = a * x + b * u` with feedback
`u = (-ahat * x - lam * x + r) / b`, the reference law
`xm' = -lam * xm + r`, and the adaptation law
`ahat' = gamma * (x - xm) * x` give `V' = -lam * e ^ 2` at
the point `t`. -/
theorem scalarMRACEnergy_hasDerivAt
    {a b lam gamma r : ℝ} (hb : b ≠ 0) (hγ : 0 < gamma)
    {x xm ahat : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x
      (a * x t + b * ((- ahat t * x t - lam * x t + r) / b)) t)
    (hxm : HasDerivAt xm (-lam * xm t + r) t)
    (hahat : HasDerivAt ahat (gamma * (x t - xm t) * x t) t) :
    HasDerivAt
      (fun s => ((x s - xm s) ^ 2 + (a - ahat s) ^ 2 / gamma) / 2)
      (-lam * (x t - xm t) ^ 2) t := by
  have hγne : gamma ≠ 0 := ne_of_gt hγ
  have hx_eq : a * x t + b * ((-ahat t * x t - lam * x t + r) / b)
      = (a - ahat t) * x t - lam * x t + r := by
    field_simp
    ring
  rw [hx_eq] at hx
  have he : HasDerivAt (fun s => x s - xm s)
      (((a - ahat t) * x t - lam * x t + r) - (-lam * xm t + r)) t :=
    hx.fun_sub hxm
  have he_eq : ((a - ahat t) * x t - lam * x t + r) - (-lam * xm t + r)
      = (a - ahat t) * x t - lam * (x t - xm t) := by ring
  rw [he_eq] at he
  have hp : HasDerivAt (fun s => a - ahat s) (-(gamma * (x t - xm t) * x t)) t :=
    HasDerivAt.const_sub a hahat
  have he2 := he.fun_pow 2
  have hp2 := hp.fun_pow 2
  have hp2d := hp2.div_const gamma
  have hadd := he2.fun_add hp2d
  have hV := hadd.div_const 2
  convert hV using 2
  simp
  field_simp
  ring

end ControlTheory
