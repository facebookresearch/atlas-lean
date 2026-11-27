/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.NonlinearControl
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open MathlibExt.Analysis.Control
open scoped ContDiff

namespace MathlibExtTest.Analysis.Control.NonlinearControl

/-- The nonholonomic integrator satisfies the regularity and equilibrium hypotheses of
Brockett's theorem: it is `C^∞` and vanishes at `(0, 0)`. -/
example : ContDiff ℝ ∞ nonholonomicIntegrator ∧ nonholonomicIntegrator (0, 0) = 0 := by
  refine ⟨contDiff_pi.2 fun i => ?_, ?_⟩
  · fin_cases i <;> simp [nonholonomicIntegrator] <;> fun_prop
  · funext i; fin_cases i <;> simp [nonholonomicIntegrator]

/-- Non-vacuity of the Lie algebra rank condition: the constant coordinate fields on `ℝⁿ`
already span at every point. -/
example (n : ℕ) (x : Fin n → ℝ) :
    accessibilitySpace (fun i : Fin n => fun _ : Fin n → ℝ => Pi.single i (1 : ℝ)) x = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ i, y i • Pi.single i (1 : ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨_, iteratedLieBrackets.base i, rfl⟩)

/-- Non-vacuity of the Rashevskii–Chow hypotheses with a nonlinear example: the fields of the
nonholonomic integrator are smooth on `Ω = ℝ³`, which is open and connected, and satisfy the Lie
algebra rank condition everywhere. -/
example : IsOpen (Set.univ : Set (Fin 3 → ℝ)) ∧ IsConnected (Set.univ : Set (Fin 3 → ℝ)) ∧
    (∀ i, ContDiffOn ℝ ∞ (nonholonomicFields i) Set.univ) ∧
    ∀ x ∈ (Set.univ : Set (Fin 3 → ℝ)), accessibilitySpace nonholonomicFields x = ⊤ := by
  refine ⟨isOpen_univ, isConnected_univ, fun i => ?_,
    fun x _ => accessibilitySpace_nonholonomicFields_eq_top x⟩
  apply ContDiff.contDiffOn
  refine contDiff_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [nonholonomicFields] <;> fun_prop

/- Every solution of `ẋ = -x` on `[0, τ)`, in the sense of `IsLocallyAsymptoticallyStable`, is
`x(t) = e^{-t} x(0)`. -/
theorem eq_exp_neg_mul_of_hasDerivWithinAt {τ : ℝ} {x : ℝ → ℝ}
    (hx : ∀ t ∈ Set.Ico 0 τ, HasDerivWithinAt x (-(x t)) (Set.Ico 0 τ) t) :
    ∀ t ∈ Set.Ico 0 τ, x t = Real.exp (-t) * x 0 := by
  intro t ht
  set g : ℝ → ℝ := fun s => Real.exp s * x s with hg
  have hgd : ∀ s ∈ Set.Ico 0 τ, HasDerivWithinAt g 0 (Set.Ico 0 τ) s := by
    intro s hs
    have h := (Real.hasDerivAt_exp s).hasDerivWithinAt.mul (hx s hs)
    convert h using 1
    ring
  have hconst := constant_of_has_deriv_right_zero (f := g) (a := 0) (b := t)
    (fun s hs => ((hgd s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩).continuousWithinAt).mono
      (fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩))
    (fun s hs => (hgd s ⟨hs.1, hs.2.trans ht.2⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Ico_mem_nhdsGE (hs.2.trans ht.2))
        fun r hr => ⟨hs.1.trans hr.1, hr.2⟩))
    t ⟨ht.1, le_rfl⟩
  simp only [hg, Real.exp_zero, one_mul] at hconst
  rw [Real.exp_neg, ← hconst]
  field_simp

/-- Non-vacuity of the hypothesis of Brockett's theorem: the fully actuated scalar system
`ẋ = u` is locally asymptotically stabilised by the continuous stationary feedback `u = -x`
(closed loop `ẋ = -x`), in the exact sense of `IsLocallyAsymptoticallyStabilizable`. For this
`f(x, u) = u` Brockett's conclusion indeed holds, since `f` is open. -/
example : IsLocallyAsymptoticallyStabilizable (fun p : ℝ × ℝ => p.2) := by
  refine ⟨fun x => -x, continuous_neg, neg_zero, 1, one_pos, fun ε hε => ?_⟩
  refine ⟨max 1 (-Real.log ε), lt_max_of_lt_left one_pos, fun τ x hx h0 t ht hMt => ?_⟩
  rw [Real.norm_eq_abs] at h0 ⊢
  rw [eq_exp_neg_mul_of_hasDerivWithinAt hx t ht, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hlog : -Real.log ε < t := lt_of_le_of_lt (le_max_right _ _) hMt
  have hexp : Real.exp (-t) < ε := by
    rw [← Real.exp_log hε]
    exact Real.exp_lt_exp.2 (by linarith)
  calc Real.exp (-t) * |x 0| ≤ Real.exp (-t) * 1 :=
        mul_le_mul_of_nonneg_left h0.le (Real.exp_pos _).le
    _ < ε := by rw [mul_one]; exact hexp

end MathlibExtTest.Analysis.Control.NonlinearControl
