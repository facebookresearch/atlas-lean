/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnected

set_option autoImplicit false

open Complex

/-- The slit plane is star convex about `1`, hence simply connected. -/
private lemma isSimplyConnected_slitPlane : IsSimplyConnected slitPlane :=
  have := starConvex_one_slitPlane.contractibleSpace ⟨1, one_mem_slitPlane⟩
  SimplyConnectedSpace.ofContractible _

-- `log ‖z‖` is harmonic on the slit plane (a proper subset of `ℂ`, so the proof goes through a
-- Riemann map), hence it is the real part of a holomorphic function there.
example : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f slitPlane ∧
    slitPlane.EqOn (fun z => (f z).re) (fun z => Real.log ‖z‖) :=
  InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_re_eq_of_isSimplyConnected
    isOpen_slitPlane isSimplyConnected_slitPlane
    fun _ hz => analyticAt_id.harmonicAt_log_norm (slitPlane_ne_zero hz)

-- Uniqueness: every holomorphic function on the slit plane with real part `log ‖z‖` is the
-- principal logarithm plus a constant.
example (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f slitPlane)
    (hfre : ∀ z ∈ slitPlane, (f z).re = Real.log ‖z‖) :
    ∃ c : ℂ, ∀ z ∈ slitPlane, f z = log z + c :=
  (MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted.exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected
    slitPlane (fun z => Real.log ‖z‖) isOpen_slitPlane isSimplyConnected_slitPlane
    fun _ hz => analyticAt_id.harmonicAt_log_norm (slitPlane_ne_zero hz)).2 f log hf
    (fun _ hz => (differentiableAt_log hz).differentiableWithinAt) hfre fun z _ => log_re z

-- The inverse of `z ↦ z ^ 2` on the right half-plane (a holomorphic square root) is holomorphic.
example {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (Function.invFunOn (· ^ 2) {w : ℂ | 0 < w.re}) (z ^ 2) := by
  refine Complex.analyticAt_invFunOn (isOpen_lt continuous_const continuous_re)
    (differentiable_pow 2).differentiableOn (fun a ha b hb hab => ?_) hz
  have ha' : 0 < a.re := ha
  have hb' : 0 < b.re := hb
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show a ^ 2 = b ^ 2 from hab) with h | h
  · exact h
  · rw [h, neg_re] at ha'
    linarith

#print axioms InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_re_eq_of_isSimplyConnected
#print axioms MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted.exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected
