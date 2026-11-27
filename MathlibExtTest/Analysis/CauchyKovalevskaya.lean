/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CauchyKovalevskaya
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions

/-! # Tests for the Cauchy–Kovalevskaya theorem -/

namespace MathlibExtTest.Analysis.CauchyKovalevskaya

open MathlibExt.Analysis.CauchyKovalevskayaWanted.Analysis Set

-- Constant transport with unit forcing and linear initial data fixes the sign of the drift.
example {d : ℕ} (b x₀ : E d) (L : E d →L[ℝ] ℝ) :
    ∃ U : Set (E d × ℝ), (x₀, 0) ∈ U ∧ IsOpen U ∧
      ∀ v : E d × ℝ → ℝ, AnalyticOnNhd ℝ v U →
        (∀ x, (x, 0) ∈ U → v (x, 0) = L x) →
        (∀ p ∈ U, fderiv ℝ v p (0, 1) = fderiv ℝ v p (b, 0) + 1) →
        ∀ p ∈ U, v p = L p.1 + (L b + 1) * p.2 := by
  obtain ⟨U, u, hx, hU, _, _, _, unique⟩ :=
    cauchy_kovalevskaya (fun _ => b) (fun _ => 1) L
      (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_const) (fun x _ => L.analyticAt x) x₀
  let w : E d × ℝ →L[ℝ] ℝ :=
    L.comp (.fst ℝ _ ℝ) + (L b + 1) • ContinuousLinearMap.snd ℝ (E d) ℝ
  have hw := unique w (fun p _ => w.analyticAt p) (fun x _ => by simp [w])
    (fun p _ => by
      rw [w.fderiv]
      simp [w])
  refine ⟨U, hx, hU, ?_⟩
  intro v hv h₀ hP p hp
  exact (unique v hv h₀ hP p hp).symm.trans (hw p hp)

-- In dimension zero the nonlinear source u² gives an ODE with initial slope one at u = 1.
example : ∃ u : E 0 × ℝ → ℝ, u (0, 0) = 1 ∧ HasDerivAt (fun t => u (0, t)) 1 0 := by
  obtain ⟨U, u, hx, _, hu, hi, hpde, _⟩ := cauchy_kovalevskaya (d := 0)
    (fun _ => 0) (fun q => q.2.2 ^ 2) (fun _ => 1) (fun _ _ => analyticAt_const)
    (fun _ _ => (analyticAt_snd.comp analyticAt_snd).pow 2) (fun _ _ => analyticAt_const) 0
  have h₀ := hi 0 hx
  change u 0 = 1 at h₀
  have h₁ := hpde _ hx
  simp [h₀, ← Prod.zero_eq_mk] at h₁
  refine ⟨u, h₀, ?_⟩
  have hpath := (hasDerivAt_const (0 : ℝ) (0 : E 0)).prodMk (hasDerivAt_id' (0 : ℝ))
  rw [← h₁]
  exact (hu _ hx).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath rfl

end MathlibExtTest.Analysis.CauchyKovalevskaya
