/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Author: @toskua
-/
module

import MathlibExt.Analysis.CStarAlgebra.PointNormAction.C0Translation
import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.FullCoefficientEmbedding
import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedMultiplierPair
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Count

/-!
# A three-cycle on a nonzero full crossed-product completion

The finite group C₃ acts by left translation on its three complex coordinate
functions, with pointwise operations and the supremum norm. Counting Haar
measure assigns mass one to each group element. The identity-coordinate
projection has different forward, inverse, and untranslated images.

The actual full covariant seminorm and its separation/completion map are
used throughout. Faithfulness of the coefficient embedding gives a nonzero
dense-core image and nonzero completion vectors on which replacing the
coefficient action by its inverse, or omitting it, changes the result.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory HaarTwistedCore
open scoped ZeroAtInfty MultiplierAlgebra

namespace CyclicCompletedCovarianceSmoke

private abbrev C3 := Multiplicative (ZMod 3)

private instance : TopologicalSpace C3 := ⊥
private instance : DiscreteTopology C3 := ⟨rfl⟩
private instance : MeasurableSpace C3 := borel C3
private instance : BorelSpace C3 := ⟨rfl⟩

private abbrev cyclicHaar : Measure C3 := Measure.count

private theorem cyclicHaar_univ_ne_zero : cyclicHaar Set.univ ≠ 0 := by
  intro h
  have hm : cyclicHaar ({1} : Set C3) ≤ cyclicHaar Set.univ :=
    measure_mono (Set.subset_univ ({1} : Set C3))
  have hs : cyclicHaar ({1} : Set C3) = 1 := Measure.count_singleton (1 : C3)
  rw [hs, h] at hm
  exact (not_le_of_gt (zero_lt_one : (0 : ENNReal) < 1)) hm

private instance : cyclicHaar.IsHaarMeasure :=
  Measure.isHaarMeasure_of_isCompact_nonempty_interior cyclicHaar Set.univ
    isCompact_univ (by simp) cyclicHaar_univ_ne_zero (measure_ne_top cyclicHaar _)

private instance : cyclicHaar.Regular :=
  Measure.regular_of_isMulLeftInvariant (μ := cyclicHaar)
    (K := Set.univ) isCompact_univ (by simp) (measure_ne_top cyclicHaar _)

private abbrev Coefficients := C₀(C3, ℂ)
private abbrev cyclicAction : PointNormCStarAction C3 Coefficients :=
  PointNormCStarAction.c0LeftTranslationAction
private abbrev fullSeminorm := maximalCStarSeminorm cyclicHaar cyclicAction
attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra
private abbrev Completion := fullSeminorm.NonUnitalCompletion
private abbrev coreMap : Carrier cyclicHaar cyclicAction →⋆ₙₐ[ℂ] Completion :=
  fullSeminorm.toNonUnitalCompletion
private abbrev coefficient (a : Coefficients) : Completion →L[ℂ] Completion :=
  coefficientLeftCompletion cyclicHaar cyclicAction fullSeminorm a
private abbrev shift (g : C3) : Completion →L[ℂ] Completion :=
  groupLeftCompletion cyclicHaar cyclicAction fullSeminorm g

private abbrev generator : C3 := Multiplicative.ofAdd (1 : ZMod 3)

private theorem generator_ne_one : generator ≠ 1 := by decide
private theorem generator_sq_ne_one : generator * generator ≠ 1 := by decide

private def projection : Coefficients :=
  ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
    (⟨fun t : C3 => if t = 1 then (1 : ℂ) else 0,
      continuous_of_discreteTopology⟩ : C(C3, ℂ))

private theorem projection_ne_zero : projection ≠ 0 := by
  intro h
  have hv := congrArg (fun a : Coefficients => a (1 : C3)) h
  change (if (1 : C3) = 1 then (1 : ℂ) else 0) = 0 at hv
  rw [ite_eq_left rfl] at hv
  exact one_ne_zero hv

private theorem projection_at_generator : projection generator = 0 := by
  change (if generator = (1 : C3) then (1 : ℂ) else 0) = 0
  rw [ite_eq_right generator_ne_one]

private theorem forward_at_generator : (cyclicAction generator projection) generator = 1 := by
  change (if generator⁻¹ * generator = (1 : C3) then (1 : ℂ) else 0) = 1
  simp only [inv_mul_cancel, ite_true]

private theorem inverse_at_generator : (cyclicAction generator⁻¹ projection) generator = 0 := by
  change (if (generator⁻¹)⁻¹ * generator = (1 : C3) then (1 : ℂ) else 0) = 0
  rw [inv_inv, ite_eq_right generator_sq_ne_one]

private theorem forward_ne_inverse :
    cyclicAction generator projection ≠ cyclicAction generator⁻¹ projection := by
  intro h
  have hv := congrArg (fun a : Coefficients => a generator) h
  rw [forward_at_generator, inverse_at_generator] at hv
  exact one_ne_zero hv

private theorem forward_ne_untranslated : cyclicAction generator projection ≠ projection := by
  intro h
  have hv := congrArg (fun a : Coefficients => a generator) h
  rw [forward_at_generator, projection_at_generator] at hv
  exact one_ne_zero hv

private theorem fst_injective :
    Function.Injective (fun T : 𝓜(ℂ, Completion) => T.fst) := by
  intro T S h
  change T.fst = S.fst at h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  calc
    ‖T - S‖ = ‖(T - S).fst‖ := (DoubleCentralizer.norm_fst (T - S)).symm
    _ = ‖T.fst - S.fst‖ := by rw [DoubleCentralizer.sub_fst]
    _ = 0 := by rw [h, sub_self, norm_zero]

private theorem coefficient_injective : Function.Injective coefficient := by
  intro a b h
  apply fullCoefficientMultiplierHom_injective cyclicHaar cyclicAction
  apply fst_injective
  change coefficient a = coefficient b
  exact h

private theorem separating_core (a b : Coefficients) (hab : a ≠ b) :
    ∃ f : Carrier cyclicHaar cyclicAction,
      coefficient a (coreMap f) ≠ coefficient b (coreMap f) := by
  by_contra h
  push Not at h
  apply hab
  apply coefficient_injective
  apply ContinuousLinearMap.ext
  intro x
  have heq := (fullSeminorm.denseRange_toNonUnitalCompletion).equalizer
    (coefficient a).continuous (coefficient b).continuous (by
      funext f
      exact h f)
  exact congrFun heq x

private theorem nonzero_core :
    ∃ f : Carrier cyclicHaar cyclicAction,
      0 < fullCovariantNorm cyclicHaar cyclicAction f ∧ coreMap f ≠ 0 := by
  obtain ⟨f, hf⟩ := separating_core projection 0 projection_ne_zero
  have hx : coreMap f ≠ 0 := by
    intro h
    apply hf
    rw [h]
    simp only [map_zero]
  refine ⟨f, ?_, hx⟩
  have hn : ‖coreMap f‖ = fullCovariantNorm cyclicHaar cyclicAction f :=
    fullSeminorm.norm_toNonUnitalCompletion f
  rw [← hn]
  exact norm_pos_iff.mpr hx

private theorem completed_covariance (g : C3) (a : Coefficients) (x : Completion) :
    shift g (coefficient a x) = coefficient (cyclicAction g a) (shift g x) := by
  have h := groupMultiplier_coefficientMultiplier cyclicHaar cyclicAction fullSeminorm g a
  have hx := congrArg (fun T : 𝓜(ℂ, Completion) => T.fst x) h
  change shift g (coefficient a x) = coefficient (cyclicAction g a) (shift g x) at hx
  exact hx

private theorem shift_inverse (g : C3) (x : Completion) : shift g (shift g⁻¹ x) = x := by
  have h := congrArg (fun T : Completion →L[ℂ] Completion => T x)
    (groupLeftCompletion_mul cyclicHaar cyclicAction fullSeminorm g g⁻¹)
  simpa only [mul_inv_cancel, groupLeftCompletion_one,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h.symm

private theorem wrong_covariance_witness (b : Coefficients)
    (hb : cyclicAction generator projection ≠ b) :
    ∃ x : Completion, x ≠ 0 ∧
      shift generator (coefficient projection x) ≠ coefficient b (shift generator x) := by
  obtain ⟨f, hf⟩ := separating_core (cyclicAction generator projection) b hb
  let x := shift generator⁻¹ (coreMap f)
  have hdiff : shift generator (coefficient projection x) ≠ coefficient b (shift generator x) := by
    dsimp only [x]
    rw [completed_covariance, shift_inverse]
    exact hf
  refine ⟨x, ?_, hdiff⟩
  intro hx
  apply hdiff
  simp only [hx, map_zero]

example : cyclicHaar ({1} : Set C3) = 1 := Measure.count_singleton (1 : C3)

example : (cyclicAction generator projection) generator = 1 ∧
    (cyclicAction generator⁻¹ projection) generator = 0 ∧ projection generator = 0 :=
  ⟨forward_at_generator, inverse_at_generator, projection_at_generator⟩

example : ∃ f : Carrier cyclicHaar cyclicAction,
    0 < fullCovariantNorm cyclicHaar cyclicAction f ∧ coreMap f ≠ 0 := nonzero_core

example (x : Completion) :
    shift generator (coefficient projection x) =
      coefficient (cyclicAction generator projection) (shift generator x) :=
  completed_covariance generator projection x

example : ∃ x : Completion, x ≠ 0 ∧
    shift generator (coefficient projection x) ≠
      coefficient (cyclicAction generator⁻¹ projection) (shift generator x) :=
  wrong_covariance_witness (cyclicAction generator⁻¹ projection) forward_ne_inverse

example : ∃ x : Completion, x ≠ 0 ∧
    shift generator (coefficient projection x) ≠ coefficient projection (shift generator x) :=
  wrong_covariance_witness projection forward_ne_untranslated

example :
    groupMultiplier cyclicHaar cyclicAction fullSeminorm generator *
        coefficientMultiplier cyclicHaar cyclicAction fullSeminorm projection *
        star (groupMultiplier cyclicHaar cyclicAction fullSeminorm generator) =
      coefficientMultiplier cyclicHaar cyclicAction fullSeminorm
        (cyclicAction generator projection) :=
  groupMultiplier_conjugates_coefficient cyclicHaar cyclicAction fullSeminorm generator projection

end CyclicCompletedCovarianceSmoke
