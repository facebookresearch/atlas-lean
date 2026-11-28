/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.LinearStability
import MathlibExt.LinearAlgebra.Matrix.MMatrix
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Tests for asymptotic stability of linear ODEs -/

open Filter Topology
open MathlibExt.Analysis.LinearStabilityWanted.Analysis.ODE

namespace MathlibExtTest.Analysis.ODE.LinearStability

-- In dimension zero the spectrum is empty and every trajectory satisfies the equation.
example (A : Matrix (Fin 0) (Fin 0) ℝ) (x : ℝ → Fin 0 → ℝ) :
    Tendsto (fun t => ‖x t‖) atTop (𝓝 0) := by
  refine linear_ode_asymptotic_stability 0 A ?_ x ?_
  · simp [Module.End.hasEigenvalue_iff_mem_spectrum, spectrum.of_subsingleton]
  · intro t _
    convert hasDerivAt_const t (0 : Fin 0 → ℝ) using 1

-- For A = -1 the positive-time trajectory exp(-t) can be assigned the value zero at t = 0.
example : Tendsto (fun t : ℝ => ‖if 0 < t then (fun _ : Fin 1 => Real.exp (-t)) else 0‖)
    atTop (𝓝 0) := by
  let A := (-1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
  apply linear_ode_asymptotic_stability 1 A
  · simpa only [Matrix.IsHurwitz, Module.End.hasEigenvalue_iff_mem_spectrum,
      Matrix.spectrum_toLin'] using (show A.IsHurwitz from Matrix.isHurwitz_smul_one (by norm_num))
  · intro t ht
    have hlocal : (fun s : ℝ => if 0 < s then (fun _ : Fin 1 => Real.exp (-s)) else 0)
        =ᶠ[𝓝 t] (fun s _ => Real.exp (-s)) := by
      filter_upwards [lt_mem_nhds ht] with s hs using ite_eq_left hs
    apply HasDerivAt.congr_of_eventuallyEq _ hlocal
    apply hasDerivAt_pi.mpr
    intro i
    simpa [A, ht, Matrix.neg_mulVec] using ((hasDerivAt_neg t).exp)

end MathlibExtTest.Analysis.ODE.LinearStability
