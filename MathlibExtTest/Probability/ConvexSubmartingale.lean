/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvexSubmartingale
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

open MeasureTheory Filter

namespace MathlibExtTest.Probability.ConvexSubmartingale

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- The convex-composition API restates with the exact public signature. -/
example (hmart : Martingale X ℱ μ) {φ : ℝ → ℝ}
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_int : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
    Submartingale (fun n ω => φ (X n ω)) ℱ μ :=
  hmart.submartingale_comp_convex hφ_convex hφ_int

/-- Squaring a martingale gives a submartingale: `x ^ 2` is convex, and
`E[(Xₙ)^2] < ∞` is the square-integrability hypothesis. -/
example (hmart : Martingale X ℱ μ)
    (hX_sq : ∀ n, Integrable (fun ω => (X n ω) ^ 2) μ) :
    Submartingale (fun n ω => (X n ω) ^ 2) ℱ μ :=
  hmart.submartingale_comp_convex ((show Even (2 : ℕ) from ⟨1, rfl⟩).convexOn_pow) hX_sq

/-- Exponentiating a martingale gives a submartingale: `Real.exp` is convex. -/
example (hmart : Martingale X ℱ μ)
    (hφ_int : ∀ n, Integrable (fun ω => Real.exp (X n ω)) μ) :
    Submartingale (fun n ω => Real.exp (X n ω)) ℱ μ :=
  hmart.submartingale_comp_convex convexOn_exp hφ_int

/-- The monotone-convex API restates with the exact public signature. -/
example (hsub : Submartingale X ℱ μ) {φ : ℝ → ℝ}
    (hφ_convex : ConvexOn ℝ Set.univ φ) (hφ_mono : MonotoneOn φ Set.univ)
    (hφ_int : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
    Submartingale (fun n ω => φ (X n ω)) ℱ μ :=
  hsub.comp_convex_of_monotoneOn hφ_convex hφ_mono hφ_int

/-- Exponentiating a submartingale gives a submartingale: `Real.exp` is
convex and monotone. -/
example (hsub : Submartingale X ℱ μ)
    (hφ_int : ∀ n, Integrable (fun ω => Real.exp (X n ω)) μ) :
    Submartingale (fun n ω => Real.exp (X n ω)) ℱ μ :=
  hsub.comp_convex_of_monotoneOn convexOn_exp
    (by intro a _ b _ h; exact Real.exp_le_exp.mpr h) hφ_int

/-- The concave-composition API restates with the exact public signature. -/
example (hmart : Martingale X ℱ μ) {φ : ℝ → ℝ}
    (hφ_concave : ConcaveOn ℝ Set.univ φ)
    (hφ_int : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
    Supermartingale (fun n ω => φ (X n ω)) ℱ μ :=
  hmart.supermartingale_comp_concave hφ_concave hφ_int

/-- Negated squaring of a martingale gives a supermartingale:
`fun x => -(x ^ 2)` is concave. -/
example (hmart : Martingale X ℱ μ)
    (hX_sq : ∀ n, Integrable (fun ω => -(X n ω) ^ 2) μ) :
    Supermartingale (fun n ω => -(X n ω) ^ 2) ℱ μ :=
  hmart.supermartingale_comp_concave
    (neg_concaveOn_iff.mpr ((show Even (2 : ℕ) from ⟨1, rfl⟩).convexOn_pow)) hX_sq

/-- The zero martingale composed with any convex `φ` is a submartingale:
the composed process is the constant `φ 0` process. -/
example {φ : ℝ → ℝ} (hφ_convex : ConvexOn ℝ Set.univ φ) :
    Submartingale (fun n ω => φ ((0 : ℕ → Ω → ℝ) n ω)) ℱ μ :=
  (martingale_zero ℝ ℱ μ).submartingale_comp_convex hφ_convex
    (fun _ => by simp only [Pi.zero_apply]; exact integrable_const _)

/-- The constant martingale composed with any convex `φ` is a
submartingale. -/
example (c : ℝ) {φ : ℝ → ℝ} (hφ_convex : ConvexOn ℝ Set.univ φ) :
    Submartingale (fun n ω => φ ((fun _ _ => c) n ω)) ℱ μ :=
  (martingale_const ℱ μ c).submartingale_comp_convex hφ_convex
    (fun _ => integrable_const _)

-- `#print axioms` for the three public theorems: only the standard triple.
#print axioms MeasureTheory.Martingale.submartingale_comp_convex
#print axioms MeasureTheory.Submartingale.comp_convex_of_monotoneOn
#print axioms MeasureTheory.Martingale.supermartingale_comp_concave

end MathlibExtTest.Probability.ConvexSubmartingale
