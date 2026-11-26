/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/
module

public import MathlibExt.Analysis.Calculus.PolynomialZeroExtension
public import Mathlib.Tactic.NormNum

/-!
# First derivatives of closed-interval polynomial zero extensions

The polynomial `(x-l)^2 (x-r)^2` has the endpoint factors required for a C¹ zero
extension. On `[0,1]` its midpoint value is `1/16`; reversed and coincident
endpoints give the zero function while retaining the same positive-order theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace PolynomialZeroExtensionSmoke

private def endpointPolynomial (l r : ℝ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C l) ^ 2 * (Polynomial.X - Polynomial.C r) ^ 2

private def zeroExtension (l r : ℝ) : ℝ → ℝ :=
  (Set.Icc l r).indicator (fun x => (endpointPolynomial l r).eval x)

example : ContDiff ℝ (1 : WithTop ℕ∞) (zeroExtension 0 1) := by
  exact Polynomial.contDiff_indicator_Icc_of_factor 0 1 (endpointPolynomial 0 1) 1
    (by change endpointPolynomial 0 1 ∣ endpointPolynomial 0 1; exact dvd_refl _)

example : zeroExtension 0 1 (1 / 2) = 1 / 16 ∧
    zeroExtension 0 1 0 = 0 ∧ zeroExtension 0 1 1 = 0 ∧
    zeroExtension 0 1 (-1) = 0 ∧ zeroExtension 0 1 ≠ 0 := by
  have hmid : zeroExtension 0 1 (1 / 2) = 1 / 16 := by
    norm_num [zeroExtension, endpointPolynomial, Set.mem_Icc]
  refine ⟨hmid, ?_, ?_, ?_, ?_⟩
  · norm_num [zeroExtension, endpointPolynomial, Set.mem_Icc]
  · norm_num [zeroExtension, endpointPolynomial, Set.mem_Icc]
  · norm_num [zeroExtension, endpointPolynomial, Set.mem_Icc]
  · intro hzero
    have h := congrFun hzero (1 / 2)
    rw [hmid] at h
    norm_num at h

example : ContDiff ℝ (1 : WithTop ℕ∞) (zeroExtension 1 0) := by
  exact Polynomial.contDiff_indicator_Icc_of_factor 1 0 (endpointPolynomial 1 0) 1
    (by change endpointPolynomial 1 0 ∣ endpointPolynomial 1 0; exact dvd_refl _)

example : zeroExtension 1 0 = 0 := by
  have hI : Set.Icc (1 : ℝ) 0 = ∅ :=
    Set.Icc_eq_empty (by norm_num : ¬ (1 : ℝ) ≤ 0)
  funext x
  change (Set.Icc (1 : ℝ) 0).indicator
    (fun y => (endpointPolynomial 1 0).eval y) x = 0
  rw [hI]
  simp only [Set.indicator_empty]

example : ContDiff ℝ (1 : WithTop ℕ∞) (zeroExtension 1 1) := by
  exact Polynomial.contDiff_indicator_Icc_of_factor 1 1 (endpointPolynomial 1 1) 1
    (by change endpointPolynomial 1 1 ∣ endpointPolynomial 1 1; exact dvd_refl _)

example : zeroExtension 1 1 = 0 := by
  funext x
  by_cases hx : x = 1
  · subst x
    norm_num [zeroExtension, endpointPolynomial]
  · have hxI : x ∉ Set.Icc (1 : ℝ) 1 := by
      simpa only [Set.Icc_self, Set.mem_singleton_iff] using hx
    change (Set.Icc (1 : ℝ) 1).indicator
      (fun y => (endpointPolynomial 1 1).eval y) x = 0
    exact Set.indicator_of_notMem hxI _

end PolynomialZeroExtensionSmoke
