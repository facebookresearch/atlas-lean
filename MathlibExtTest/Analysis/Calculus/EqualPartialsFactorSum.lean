/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.EqualPartialsFactorSum
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Tests for `MathlibExt.Analysis.Calculus.EqualPartialsFactorSum` -/

set_option autoImplicit false

namespace MathlibExtTest.EqualPartialsFactorSum

open MathlibExt.Analysis.Calculus.EqualPartialsFactorSumWanted

/-- For every `h : ℝ → ℝ`, the function `(x, y) ↦ h (x + y)` satisfies the hypothesis on the
partial derivatives. Where it is differentiable, `h` is differentiable at `x + y` and both partial
derivatives equal `h' (x + y)`; elsewhere `fderiv` is `0`. -/
private lemma fderiv_comp_add_apply_eq (h : ℝ → ℝ) (p : ℝ × ℝ) :
    (fderiv ℝ (fun q : ℝ × ℝ => h (q.1 + q.2)) p) (1, 0) =
      (fderiv ℝ (fun q : ℝ × ℝ => h (q.1 + q.2)) p) (0, 1) := by
  by_cases hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => h (q.1 + q.2)) p
  · -- `h t = F (t - p.2, p.2)` for `F (x, y) = h (x + y)`, so `h` is differentiable at `p.1 + p.2`.
    have hh : DifferentiableAt ℝ h (p.1 + p.2) := by
      have hd' : DifferentiableAt ℝ (fun q : ℝ × ℝ => h (q.1 + q.2))
          ((fun t : ℝ => (t - p.2, p.2)) (p.1 + p.2)) := by simpa using hd
      have hline : DifferentiableAt ℝ (fun t : ℝ => (t - p.2, p.2)) (p.1 + p.2) := by fun_prop
      have hcomp := hd'.comp (p.1 + p.2) hline
      simpa [Function.comp_def] using hcomp
    have hsum : HasFDerivAt (fun q : ℝ × ℝ => q.1 + q.2)
        (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hasFDerivAt_fst.fun_add hasFDerivAt_snd
    have hF := HasDerivAt.comp_hasFDerivAt (f := fun q : ℝ × ℝ => q.1 + q.2) p hh.hasDerivAt hsum
    rw [show (fun q : ℝ × ℝ => h (q.1 + q.2)) = h ∘ fun q => q.1 + q.2 from rfl, hF.fderiv]
    simp
  · simp [fderiv_zero_of_not_differentiableAt hd]

-- Test section: the hypotheses can be met. `(x, y) ↦ sin (x + y)` is continuously
-- differentiable, has equal partial derivatives and vanishes at the origin, so `sin (x + y)` is a
-- continuous multiple of `x + y`.
example : ∃ g : ℝ × ℝ → ℝ, Continuous g ∧ ∀ x y : ℝ, Real.sin (x + y) = g (x, y) * (x + y) :=
  exists_continuous_mul_add_of_fderiv_eq (f := fun q => Real.sin (q.1 + q.2)) (by fun_prop)
    (fderiv_comp_add_apply_eq Real.sin) (by simp)

-- Test section: the hypothesis `f (0, 0) = 0` cannot be dropped. The constant function `1` is
-- continuously differentiable with equal (zero) partial derivatives, but every multiple of
-- `x + y` vanishes at the origin.
example : ContDiff ℝ 1 (fun _ : ℝ × ℝ => (1 : ℝ)) ∧
    (∀ p : ℝ × ℝ, (fderiv ℝ (fun _ : ℝ × ℝ => (1 : ℝ)) p) (1, 0) =
      (fderiv ℝ (fun _ : ℝ × ℝ => (1 : ℝ)) p) (0, 1)) ∧
    ¬∃ g : ℝ × ℝ → ℝ, Continuous g ∧ ∀ x y : ℝ, (1 : ℝ) = g (x, y) * (x + y) := by
  refine ⟨contDiff_const, fun p => by simp, ?_⟩
  rintro ⟨g, -, hg⟩
  simpa using hg 0 0

-- Test section: differentiability cannot be weakened to continuity. Since `fderiv` is `0` where
-- a function is not differentiable, the continuous function `(x, y) ↦ |x + y|` satisfies the
-- hypothesis on the partial derivatives and vanishes at the origin, but
-- `|x + y| = g (x, y) * (x + y)` forces `g (t, 0) = 1` for `t > 0` and `g (t, 0) = -1` for
-- `t < 0`, so no such `g` is continuous.
example : Continuous (fun q : ℝ × ℝ => |q.1 + q.2|) ∧
    (∀ p : ℝ × ℝ, (fderiv ℝ (fun q : ℝ × ℝ => |q.1 + q.2|) p) (1, 0) =
      (fderiv ℝ (fun q : ℝ × ℝ => |q.1 + q.2|) p) (0, 1)) ∧
    (fun q : ℝ × ℝ => |q.1 + q.2|) (0, 0) = 0 ∧
    ¬∃ g : ℝ × ℝ → ℝ, Continuous g ∧ ∀ x y : ℝ, |x + y| = g (x, y) * (x + y) := by
  refine ⟨by fun_prop, fderiv_comp_add_apply_eq (fun t => |t|), by simp, ?_⟩
  rintro ⟨g, hg, hfac⟩
  have hcont : Continuous fun t : ℝ => g (t, 0) := hg.comp (continuous_id.prodMk continuous_const)
  -- `g (t, 0) = c` on a side of `0` forces `g (0, 0) = c`, as `0` is in the closure of that side.
  have hpos : g (0, 0) = 1 := by
    have hsub : Set.Ioi (0 : ℝ) ⊆ {t | g (t, 0) = 1} := fun t (ht : 0 < t) => by
      have h := hfac t 0
      rw [add_zero, abs_of_pos ht] at h
      exact mul_right_cancel₀ ht.ne' (h.symm.trans (one_mul t).symm)
    exact (isClosed_eq hcont continuous_const).closure_subset_iff.2 hsub
      (by rw [closure_Ioi]; exact Set.self_mem_Ici)
  have hneg : g (0, 0) = -1 := by
    have hsub : Set.Iio (0 : ℝ) ⊆ {t | g (t, 0) = -1} := fun t (ht : t < 0) => by
      have h := hfac t 0
      rw [add_zero, abs_of_neg ht] at h
      exact mul_right_cancel₀ ht.ne (h.symm.trans (neg_one_mul t).symm)
    exact (isClosed_eq hcont continuous_const).closure_subset_iff.2 hsub
      (by rw [closure_Iio]; exact Set.self_mem_Iic)
  linarith

-- Test section: for any normed space `E`, equal partial derivatives make a differentiable
-- `f : ℝ × ℝ → E` symmetric, here for `E = ℂ`: both `f (x, y)` and `f (y, x)` equal `f (x + y, 0)`.
example {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f)
    (hpar : ∀ p : ℝ × ℝ, (fderiv ℝ f p) (1, 0) = (fderiv ℝ f p) (0, 1)) (x y : ℝ) :
    f (x, y) = f (y, x) := by
  rw [apply_eq_apply_add_zero_of_fderiv_eq hf hpar, apply_eq_apply_add_zero_of_fderiv_eq hf hpar y,
    add_comm]

end MathlibExtTest.EqualPartialsFactorSum
