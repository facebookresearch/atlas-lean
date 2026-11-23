/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.MulByIdOnL2OneTwoSelfAdjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.Holder

/-! # Tests for `MathlibExt.Analysis.OperatorTheory.MulByIdOnL2OneTwoSelfAdjoint` -/

namespace MathlibExtTest.MulByIdOnL2OneTwoSelfAdjoint

open MeasureTheory
open scoped ENNReal
open MathlibExt.Analysis.OperatorTheory.MulByIdOnL2OneTwoSelfAdjointWanted

-- Test section: the inner product of `L2OnOneTwo` is `⟪f, g⟫ = ∫_[1, 2] f g`, as the docstrings
-- say.
example (f g : L2OnOneTwo) : inner ℝ f g = ∫ x in Set.Icc (1 : ℝ) 2, f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

-- Test section: the hypotheses are satisfiable, so the theorem is not vacuous. Hölder's
-- inequality for the exponents `∞, 2, 2` makes multiplication by the bounded function `x ↦ x`
-- a continuous linear map on `L²([1, 2])`, and the theorem applies to it.
example : ∃ T : L2OnOneTwo →ₗ[ℝ] L2OnOneTwo,
    (∀ f : L2OnOneTwo, T f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x) ∧
      Continuous T ∧ Function.Bijective T ∧
        ∃ Tc : L2OnOneTwo →L[ℝ] L2OnOneTwo, Tc.toLinearMap = T ∧ Tc.adjoint = Tc := by
  have hg : MemLp (fun x : ℝ => x) ∞ (volume.restrict (Set.Icc (1 : ℝ) 2)) :=
    memLp_top_of_bound continuous_id.aestronglyMeasurable 2
      (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hx.1], hx.2⟩)
  let M : L2OnOneTwo →L[ℝ] L2OnOneTwo := (ContinuousLinearMap.mul ℝ ℝ).holderL _ ∞ 2 2 hg.toLp
  have hM : ∀ f : L2OnOneTwo,
      M.toLinearMap f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x := fun f => by
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) hg.toLp f,
      hg.coeFn_toLp] with x hx hgx
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.holderL_apply_apply, hx,
      ContinuousLinearMap.mul_apply', hgx]
  exact ⟨M.toLinearMap, hM, continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two _ hM⟩

-- Test section: the hypothesis determines the operator. Two linear maps on `L²([1, 2])` that both
-- multiply by `x` almost everywhere are equal.
example (T S : L2OnOneTwo →ₗ[ℝ] L2OnOneTwo)
    (hT : ∀ f : L2OnOneTwo, T f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x)
    (hS : ∀ f : L2OnOneTwo, S f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x) :
    T = S :=
  LinearMap.ext fun f => Lp.ext ((hT f).trans (hS f).symm)

-- Test section: the operator is invertible with a bounded inverse. By the open mapping theorem,
-- the continuous bijection of the theorem is an isomorphism of Banach spaces.
example (T : L2OnOneTwo →ₗ[ℝ] L2OnOneTwo)
    (hT : ∀ f : L2OnOneTwo, T f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x) :
    ∃ e : L2OnOneTwo ≃L[ℝ] L2OnOneTwo, ∀ f, e f = T f := by
  obtain ⟨-, hbij, Tc, rfl, -⟩ := continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two T hT
  exact ⟨ContinuousLinearEquiv.ofBijective Tc (LinearMap.ker_eq_bot_of_injective hbij.1)
    (LinearMap.range_eq_top_of_surjective _ hbij.2), fun f => rfl⟩

-- Test section: the self-adjointness conclusion in Mathlib's star-algebra form, and the symmetry
-- `⟪T f, g⟫ = ⟪f, T g⟫` it gives.
example (T : L2OnOneTwo →ₗ[ℝ] L2OnOneTwo)
    (hT : ∀ f : L2OnOneTwo, T f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x) :
    ∃ Tc : L2OnOneTwo →L[ℝ] L2OnOneTwo, Tc.toLinearMap = T ∧ IsSelfAdjoint Tc := by
  obtain ⟨-, -, Tc, hTc, hadj⟩ := continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two T hT
  exact ⟨Tc, hTc, by rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, hadj]⟩

example (T : L2OnOneTwo →ₗ[ℝ] L2OnOneTwo)
    (hT : ∀ f : L2OnOneTwo, T f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x)
    (f g : L2OnOneTwo) :
    inner ℝ (T f) g = inner ℝ f (T g) := by
  obtain ⟨-, -, Tc, rfl, hadj⟩ := continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two T hT
  have h := ContinuousLinearMap.adjoint_inner_right Tc f g
  rw [hadj] at h
  exact h.symm

end MathlibExtTest.MulByIdOnL2OneTwoSelfAdjoint
