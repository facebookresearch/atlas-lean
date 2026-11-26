/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Order.LiminfLimsup

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Normwise iterative refinement

With a bounded inverse and stipulated error bounds for the residual, correction, and
update, the error satisfies an affine scalar recurrence. Its geometric majorant yields
a limit-superior bound on the error norms without requiring convergence of the iterates.
-/

open Filter Topology

namespace Cslib.Algorithms.Lean.Numerical

/-- The normwise iterative-refinement recurrence and geometric bound. The invertible
linear system is represented by a continuous linear equivalence, and the inverse is
measured in its induced operator norm. The computed residuals, corrections and update
errors are arbitrary sequences satisfying the stipulated bounds. The final assertion
bounds the limit superior of the error norms, not convergence of the iterates.

For related componentwise bounds with actual mixed-precision triangular solves, see
Carson and Higham, *Accelerating the Solution of Linear Systems by Iterative Refinement
in Three Precisions*, §3, Theorem 3.2 and Corollary 3.3. -/
public theorem iterative_refinement_error_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E ≃L[ℝ] F) (b : F) (x : ℕ → E) (rhat : ℕ → F) (dhat g : ℕ → E)
    (ρ φ γ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ < 1)
    (hres : ∀ i, ‖rhat i - (b - A (x i))‖ ≤ ρ)
    (hcorr : ∀ i, ‖dhat i - A.symm (rhat i)‖ ≤ φ * ‖A.symm (rhat i)‖)
    (hnoise : ∀ i, ‖g i‖ ≤ γ) (hupdate : ∀ i, x (i + 1) = x i + dhat i + g i) :
    let e := fun i => x i - A.symm b
    let B := (1 + φ) * ‖A.symm.toContinuousLinearMap‖ * ρ + γ
    let L := B / (1 - φ)
    (∀ i, ‖e (i + 1)‖ ≤ φ * ‖e i‖ + B) ∧
    (∀ i, ‖e i‖ ≤ L + φ ^ i * (‖e 0‖ - L)) ∧
    limsup (fun i => ‖e i‖) atTop ≤ L := by
  intro e B L
  let Ainv : F →L[ℝ] E := A.symm.toContinuousLinearMap
  let w (i : ℕ) := Ainv (rhat i - (b - A (x i)))
  have hresid (i : ℕ) : A.symm (rhat i) = -e i + w i := by
    dsimp only [w, e, Ainv]
    change A.symm (rhat i) = -(x i - A.symm b) + A.symm (rhat i - (b - A (x i)))
    rw [map_sub, map_sub, A.symm_apply_apply]
    abel
  have hw (i : ℕ) : ‖w i‖ ≤ ‖Ainv‖ * ρ :=
    (Ainv.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hres i) (norm_nonneg _))
  have hstep (i : ℕ) : ‖e (i + 1)‖ ≤ φ * ‖e i‖ + B := by
    have hcor (i : ℕ) : ‖A.symm (rhat i)‖ ≤ ‖e i‖ + ‖Ainv‖ * ρ := by
      calc
        ‖A.symm (rhat i)‖ = ‖-e i + w i‖ := congrArg norm (hresid i)
        _ ≤ ‖e i‖ + ‖w i‖ := by simpa only [norm_neg] using norm_add_le (-e i) (w i)
        _ ≤ _ := add_le_add_right (hw i) _
    have herror : e (i + 1) = w i + (dhat i - A.symm (rhat i)) + g i := by
      change x (i + 1) - A.symm b = _
      rw [hupdate i, hresid i]
      dsimp only [e]
      abel
    calc
      _ = ‖w i + (dhat i - A.symm (rhat i)) + g i‖ := congrArg norm herror
      _ ≤ ‖w i‖ + ‖dhat i - A.symm (rhat i)‖ + ‖g i‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ ‖Ainv‖ * ρ + φ * (‖e i‖ + ‖Ainv‖ * ρ) + γ :=
        add_le_add (add_le_add (hw i) ((hcorr i).trans (mul_le_mul_of_nonneg_left (hcor i) hφ₀)))
          (hnoise i)
      _ = φ * ‖e i‖ + B := by
        change _ = φ * ‖e i‖ + ((1 + φ) * ‖Ainv‖ * ρ + γ)
        ring
  have hL : L * (1 - φ) = B := div_mul_cancel₀ _ (sub_pos.mpr hφ₁).ne'
  have hgeom (i : ℕ) : ‖e i‖ ≤ L + φ ^ i * (‖e 0‖ - L) := by
    induction i with
    | zero => simp
    | succ i hi =>
      calc
        _ ≤ φ * ‖e i‖ + B := hstep i
        _ ≤ φ * (L + φ ^ i * (‖e 0‖ - L)) + B :=
          add_le_add_left (mul_le_mul_of_nonneg_left hi hφ₀) B
        _ = _ := by rw [← hL, pow_succ]; ring
  refine ⟨hstep, hgeom, ?_⟩
  have hlim : Tendsto (fun i : ℕ => L + φ ^ i * (‖e 0‖ - L)) atTop (𝓝 L) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hφ₀ hφ₁
    have ht := (hp.const_mul (‖e 0‖ - L)).add_const L
    rw [mul_zero, zero_add] at ht
    simpa only [mul_comm, add_comm] using ht
  calc
    _ ≤ limsup (fun i : ℕ => L + φ ^ i * (‖e 0‖ - L)) atTop :=
      limsup_le_limsup (Eventually.of_forall hgeom)
        (isCoboundedUnder_le_of_eventually_le atTop
          (Eventually.of_forall fun i => norm_nonneg (e i)))
        hlim.isBoundedUnder_le
    _ = L := hlim.limsup_eq

end Cslib.Algorithms.Lean.Numerical
