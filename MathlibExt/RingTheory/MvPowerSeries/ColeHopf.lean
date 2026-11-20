/-
Copyright (c) 2025–2026 the contributors.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.IteratedPDeriv
import Mathlib.Tactic.Ring

/-!
# The formal Cole–Hopf transformation

For an invertible formal heat solution φ, the logarithmic derivative
`u = -2ν (∂ₓφ) φ⁻¹` satisfies the formal viscous Burgers equation.
This is an identity of multivariate formal power series. No convergence or
analytic realization is asserted, and viscosity need not be positive.

Mathematical reference: F. Gesztesy and H. Holden, The Cole-Hopf and Miura
Transformations Revisited, Lemma 3.1, equations (3.1)-(3.2),
https://arxiv.org/abs/solv-int/9812025. The residual identity is algebraic;
here it is proved for formal series over any field. This does not assert
an analytic extension of the source's smooth, positive-function theorem.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ K : Type*} [Field K]

/-- The formal Cole–Hopf logarithmic derivative along a selected spatial axis.
Its interpretation as a quotient requires a nonzero constant coefficient of φ. -/
noncomputable def coleHopf (ν : K) (x : σ) (φ : MvPowerSeries σ K) :
    MvPowerSeries σ K := C (-2 * ν) * (pderiv x φ * φ⁻¹)

/-- Cole–Hopf sends an invertible formal heat solution to a formal Burgers
solution. Extra formal variables may act as parameters. -/
theorem pderiv_coleHopf_of_heat (ν : K) (t x : σ) (φ : MvPowerSeries σ K)
    (hc : constantCoeff φ ≠ 0)
    (heat : pderiv t φ = C ν * pderiv x (pderiv x φ)) :
    pderiv t (coleHopf ν x φ) =
      C ν * pderiv x (pderiv x (coleHopf ν x φ)) -
        coleHopf ν x φ * pderiv x (coleHopf ν x φ) := by
  have dmul (i : σ) (a b : MvPowerSeries σ K) :
      pderiv i (a * b) = a * pderiv i b + b * pderiv i a := by
    simpa only [smul_eq_mul] using (pderiv i).leibniz a b
  have dC (i : σ) (q : K) (a : MvPowerSeries σ K) :
      pderiv i (C q * a) = C q * pderiv i a := by
    simp only [dmul, pderiv_C, mul_zero, add_zero]
  have dinv (i : σ) : pderiv i φ⁻¹ = -φ⁻¹ ^ 2 * pderiv i φ :=
    (pderiv i).leibniz_of_mul_eq_one (MvPowerSeries.inv_mul_cancel (h := hc))
  have dtx : pderiv t (pderiv x φ) = C ν * pderiv x (pderiv x (pderiv x φ)) := by
    rw [pderiv_pderiv, heat]
    rw [dC]
  have c2 : (C (-2 * ν) : MvPowerSeries σ K) = -(2 * C ν) := by
    rw [map_mul, map_neg, map_ofNat]
    ring
  simp only [coleHopf, dC]
  simp only [dmul, map_add, map_neg, dinv, dtx, pderiv_pow]
  rw [c2, heat]
  ring

end MvPowerSeries
