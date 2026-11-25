/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.BesselKernel

@[expose] public section

open MeasureTheory Set

namespace BesselKernelTest

/-- Consumer with the original binders: existence of a nonzero value. -/
theorem exactSource_exists (ν : ℂ) :
    ∃ x : ℝ, 0 < x ∧ ArchBessel.besselKernel ν x ≠ 0 :=
  ArchBessel.exists_besselKernel_ne_zero ν

/-- Consumer with the original binders: derivative identities. -/
theorem exactSource_deriv (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => ArchBessel.besselKernel ν x)
        (-ArchBessel.besselKernel (ν + 1) x + ν / (x : ℂ) * ArchBessel.besselKernel ν x) x ∧
      HasDerivAt (deriv fun x : ℝ => ArchBessel.besselKernel ν x)
        ((1 + ν ^ 2 / (x : ℂ) ^ 2) * ArchBessel.besselKernel ν x -
          (deriv (fun x : ℝ => ArchBessel.besselKernel ν x) x) / (x : ℂ)) x :=
  ArchBessel.hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel ν x hx

/-- Consumer with the original binders: Mellin transform formula. -/
theorem exactSource_mellin (ν s : ℂ) (hs : |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => ArchBessel.besselKernel ν x) s ∧
      mellin (fun x : ℝ => ArchBessel.besselKernel ν x) s =
        (2 : ℂ) ^ (s - 1) * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2) :=
  ArchBessel.mellin_besselKernel_eq_mul_Gamma_mul_Gamma ν s hs

/-- Boundary example: the Mellin hypothesis fails at `s = 0` for `ν = 0`,
so the Gamma-factor formula is not asserted there. -/
example : ¬ |(0 : ℂ).re| < (0 : ℂ).re := by norm_num

end BesselKernelTest
