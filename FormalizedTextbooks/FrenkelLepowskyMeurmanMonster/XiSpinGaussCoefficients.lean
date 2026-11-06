/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Kernel-checked six-dimensional Gauss coefficients and their involutions.
Source: Seysen, arXiv:2002.10921v3, Lemma 9.1 and equation (9.3.1).
The finite computations use the Lean kernel; no external numerical result
is used as a proof of a relation in the named group.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinGray

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Integral signs allow the finite certificates to avoid real equality decisions. -/
def xiGraySign (a : XiGrayIndex) : ℤ := if xiGrayQuadratic a = 0 then 1 else -1

@[simp] theorem xiGraySign_real (a : XiGrayIndex) :
    (xiGraySign a : ℝ) = qSign (xiGrayQuadratic a) := by
  simp [xiGraySign, qSign]

/-- The polar form of the published binomial-weight quadratic form. -/
theorem xiGrayQuadratic_add (a b : XiGrayIndex) :
    xiGrayQuadratic (a + b) = xiGrayQuadratic a + xiGrayQuadratic b + xiGrayBilinear a b := by
  simp [xiGrayQuadratic, xiGrayBilinear, Fin.sum_univ_succ, Finset.sum_filter]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- The 64 shifts each require an exact sum of 64 integral signs.
/-- Exact autocorrelation of the 64 published quadratic signs. -/
theorem xiGraySign_autocorrelation : ∀ c : XiGrayIndex,
    (∑ a : XiGrayIndex, xiGraySign a * xiGraySign (a + c)) = if c = 0 then 64 else 0 := by
  decide +kernel

theorem xiGraySign_autocorrelation_real (c : XiGrayIndex) :
    (∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) * qSign (xiGrayQuadratic (a + c))) =
      if c = 0 then (64 : ℝ) else 0 := by
  have h := xiGraySign_autocorrelation c
  have hc : (↑(∑ a : XiGrayIndex, xiGraySign a * xiGraySign (a + c)) : ℝ) =
      if c = 0 then 64 else 0 := by exact_mod_cast h
  simpa using hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
