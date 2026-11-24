/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.RadialPrimitive
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Tests for radial primitives through their centre

* At the centre the derivative is `0`, for the admissible profile `f t = t` on `ℂ`.
* A singleton sum gives the single radial field; the empty sum gives `0`.
* Two centres `0` and `2` with the admissible profile `f t = t`: the total field at
  the centre `0` is `-2`, although each field vanishes at its own centre.
* The hypothesis `f 0 = 0` cannot be dropped: for the constant profile `1`, the
  primitive is `‖w‖`, which is not differentiable at the centre.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.RadialPrimitive

open MathlibExt.Analysis.InnerProductSpace.RadialPrimitive
open MathlibExt.Analysis.Complex.HartogsWanted

/-- At the centre, the derivative of the radial primitive of `t ↦ t` is `0`. -/
example (z₀ : ℂ) :
    HasFDerivAt (fun w : ℂ => ∫ t in (0 : ℝ)..‖w - z₀‖, t) (0 : ℂ →L[ℝ] ℝ) z₀ := by
  simpa using hasFDerivAt_intervalIntegral_norm_sub (f := fun t : ℝ => t)
    continuous_id.continuousOn rfl z₀ z₀

/-- The radial primitive of `t ↦ t` is `C¹` on `ℂ`. -/
example (z₀ : ℂ) : ContDiff ℝ 1 (fun w : ℂ => ∫ t in (0 : ℝ)..‖w - z₀‖, t) :=
  contDiff_one_intervalIntegral_norm_sub (f := fun t : ℝ => t) continuous_id.continuousOn rfl z₀

/-- A singleton sum: twice the Wirtinger derivative is the single radial field. -/
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ici 0)) (hf0 : f 0 = 0) (z₀ z : ℂ) :
    2 * barDeriv (fun w : ℂ => ((∫ t in (0 : ℝ)..‖w - z₀‖, f t : ℝ) : ℂ)) z =
      ((f ‖z - z₀‖ / ‖z - z₀‖ : ℝ) : ℂ) * (z - z₀) := by
  simpa using two_mul_barDeriv_ofReal_sum_intervalIntegral_norm_sub {()}
    (f := fun _ => f) (fun _ _ => hf) (fun _ _ => hf0) (fun _ => z₀) z

/-- The empty sum: the Wirtinger derivative of `0` is `0`. -/
example (z : ℂ) :
    2 * barDeriv (fun w : ℂ =>
        ((∑ α ∈ (∅ : Finset Unit), ∫ t in (0 : ℝ)..‖w - (fun _ => (0 : ℂ)) α‖,
          (fun _ (t : ℝ) => t) α t : ℝ) : ℂ)) z = 0 := by
  rw [two_mul_barDeriv_ofReal_sum_intervalIntegral_norm_sub ∅ (by simp) (by simp)]
  simp

/-- Two centres `0` and `2` with the admissible profile `t ↦ t`: the total field at the
centre `0` is `-2`. Only the field of the centre `0` vanishes there. -/
example :
    2 * barDeriv (fun w : ℂ =>
        ((∑ α ∈ (Finset.univ : Finset (Fin 2)),
            ∫ t in (0 : ℝ)..‖w - ![(0 : ℂ), 2] α‖, t : ℝ) : ℂ)) 0 = -2 := by
  rw [two_mul_barDeriv_ofReal_sum_intervalIntegral_norm_sub (f := fun _ (t : ℝ) => t)
    Finset.univ (fun _ _ => continuous_id.continuousOn) (fun _ _ => rfl) ![(0 : ℂ), 2] 0]
  simp [Fin.sum_univ_two]

/-- The hypothesis `f 0 = 0` cannot be dropped: for the constant profile `1` the radial
primitive is `‖w‖`, which is not differentiable at the centre `0`. -/
example : ¬ DifferentiableAt ℝ (fun w : ℂ => ∫ _t in (0 : ℝ)..‖w - 0‖, (1 : ℝ)) 0 := by
  simpa using not_differentiableAt_norm_zero ℂ

#print axioms hasFDerivAt_intervalIntegral_norm_sub
#print axioms contDiff_one_intervalIntegral_norm_sub
#print axioms two_mul_barDeriv_ofReal_sum_intervalIntegral_norm_sub

end MathlibExtTest.Analysis.InnerProductSpace.RadialPrimitive
