/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.SmoothEnvelope
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic

/-!
# Tests for the smooth envelope theorem

For `F (x, θ) = θ x - x²` the maximizer is `θ / 2`, the value is `θ² / 4`, and its derivative at
`θ = 2` is `1`, the parameter derivative `x` of `F` at the optimizer.
-/

@[expose] public section

open Filter Topology

namespace MathlibExtTest.Analysis.Calculus.SmoothEnvelope

open _root_.MathlibExt.Envelope

noncomputable def F : ℝ × ℝ → ℝ := fun z => z.2 * z.1 - z.1 ^ 2

noncomputable def xstar : ℝ → ℝ := fun θ => θ / 2

theorem isMaxOn_test (θ : ℝ) : IsMaxOn (fun y => F (y, θ)) Set.univ (xstar θ) := by
  rw [isMaxOn_iff]
  intro y _
  show θ * y - y ^ 2 ≤ θ * (θ / 2) - (θ / 2) ^ 2
  have h := sq_nonneg (y - θ / 2)
  linarith

theorem valueFunction_test (θ : ℝ) : valueFunction F Set.univ θ = θ ^ 2 / 4 := by
  rw [valueFunction_eq_of_isMaxOn (Set.mem_univ _) (isMaxOn_test θ)]
  show θ * (θ / 2) - (θ / 2) ^ 2 = θ ^ 2 / 4
  ring

theorem hasDerivAt_test : HasDerivAt (valueFunction F Set.univ) 1 2 := by
  have hx2 : xstar 2 = (1 : ℝ) := by
    simp only [xstar]
    norm_num
  have hopt : ∀ᶠ θ in 𝓝 (2 : ℝ),
      xstar θ ∈ Set.univ ∧ IsMaxOn (fun y => F (y, θ)) Set.univ (xstar θ) :=
    Filter.Eventually.of_forall fun θ => ⟨Set.mem_univ _, isMaxOn_test θ⟩
  have h2 : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 2) := hasFDerivAt_snd
  have h1 : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 2) := hasFDerivAt_fst
  have hF : HasFDerivAt F
      ((Prod.snd ((1 : ℝ), (2 : ℝ)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        Prod.fst ((1 : ℝ), (2 : ℝ)) • ContinuousLinearMap.snd ℝ ℝ ℝ) -
        (((2 : ℕ) • Prod.fst ((1 : ℝ), (2 : ℝ)) ^ (2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ))
      ((xstar 2), 2) := by
    rw [hx2]
    show HasFDerivAt (fun z : ℝ × ℝ => z.2 * z.1 - z.1 ^ 2) _ (1, 2)
    exact (h2.mul h1).sub (h1.pow 2)
  have hx : HasFDerivAt xstar ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (2 : ℝ) := by
    show HasFDerivAt (fun θ : ℝ => θ / 2) _ 2
    have h := (hasFDerivAt_id (𝕜 := ℝ) (2 : ℝ)).mul_const (1 / 2 : ℝ)
    have hfun : (fun θ : ℝ => θ / 2) = (fun y : ℝ => y * (1 / 2)) := by
      ext θ
      exact div_eq_mul_one_div _ _
    rw [hfun]
    exact h
  have hmain := hasFDerivAt_valueFunction isOpen_univ hopt hF hx
  have hderiv := hmain.hasDerivAt
  convert hderiv using 2
  have hfst01 : (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 1) = (0 : ℝ) := rfl
  have hsnd01 : (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) = (1 : ℝ) := rfl
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, sub_apply,
    add_apply, smul_apply, hfst01, hsnd01]
  simp

end MathlibExtTest.Analysis.Calculus.SmoothEnvelope
