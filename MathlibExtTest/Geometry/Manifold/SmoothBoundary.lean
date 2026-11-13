/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.SmoothBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Tests for `Manifold.HasSmoothBoundary` on the plane `EuclideanSpace ℝ (Fin 2)`,
viewed as a manifold modeled on itself via `𝓡 2`, and a regression test showing that the
predicate does not apply to the closed half-plane model `𝓡∂ 2`. The tests go through the public
API only (`HasSmoothBoundary.intro`, `HasSmoothBoundary.isOpen`,
`HasSmoothBoundary.exists_isLocalDefiningFunction`, the fields of `IsLocalDefiningFunction`
and the lemmas for sets with empty frontier), never through the definition's unfolding.
-/

open scoped Manifold ContDiff Topology

noncomputable section

namespace Manifold

namespace SmoothBoundaryTest

/-- The open unit disc of the plane has smooth boundary. -/
theorem unitBall_hasSmoothBoundary :
    HasSmoothBoundary (𝓡 2) (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  have hfront : frontier (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    frontier_ball 0 (by norm_num)
  refine HasSmoothBoundary.intro Metric.isOpen_ball fun p hp => ?_
  rw [hfront, Metric.mem_sphere, dist_zero_right] at hp
  refine ⟨Set.univ, fun x => ‖x‖ ^ 2 - 1,
    { isOpen := isOpen_univ
      mem := Set.mem_univ p
      contMDiffOn := ?_
      apply_eq_zero := ?_
      mfderiv_ne_zero := ?_
      mem_iff := ?_ }⟩
  · have hρ : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2 - 1) :=
      (contDiff_norm_sq ℝ).sub contDiff_const
    exact contMDiffOn_iff_contDiffOn.mpr hρ.contDiffOn
  · simp [hp]
  · have hHas : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2 - 1)
        ((2 : ℝ) • (innerSL ℝ) p) p := by
      have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2)
          ((2 : ℝ) • (innerSL ℝ) p) p := by
        have hid : HasFDerivAt (id : EuclideanSpace ℝ (Fin 2) → _)
            (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) p :=
          hasFDerivAt_id p
        have h2 := HasFDerivAt.norm_sq hid
        have hcast : ((2 : ℕ) • (innerSL ℝ) p) = ((2 : ℝ) • (innerSL ℝ) p) := by
          rw [two_nsmul, two_smul]
        simpa [hcast] using h2
      exact h1.sub_const 1
    have h2L : (2 : ℝ) • (innerSL ℝ) (p : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
      have hp0 : p ≠ 0 := by
        intro hcon
        rw [hcon, norm_zero] at hp
        norm_num at hp
      have hLp : (innerSL ℝ) (p : EuclideanSpace ℝ (Fin 2)) p = (1 : ℝ) := by
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hp, one_pow]
      intro hcon
      have hL0 : (innerSL ℝ) (p : EuclideanSpace ℝ (Fin 2)) = 0 := by
        rcases smul_eq_zero.mp hcon with h | h
        · norm_num at h
        · exact h
      rw [hL0] at hLp
      simp at hLp
    have heq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2 - 1) p
        = (2 : ℝ) • (innerSL ℝ) p :=
      (hasMFDerivAt_iff_hasFDerivAt.mpr hHas).mfderiv
    rw [heq]
    exact h2L
  · intro x _
    rw [Metric.mem_ball, dist_zero_right]
    show ‖x‖ < 1 ↔ ‖x‖ ^ 2 - 1 < 0
    have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    constructor <;> intro h <;> nlinarith [hnn]

/-- The whole plane has smooth boundary, vacuously. -/
theorem univ_hasSmoothBoundary :
    HasSmoothBoundary (𝓡 2) (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) :=
  hasSmoothBoundary_univ

/-- The empty set has smooth boundary, vacuously. -/
theorem empty_hasSmoothBoundary :
    HasSmoothBoundary (𝓡 2) (∅ : Set (EuclideanSpace ℝ (Fin 2))) :=
  hasSmoothBoundary_empty

/-- A clopen set has smooth boundary through `HasSmoothBoundary.of_isClopen`. -/
example : HasSmoothBoundary (𝓡 2) (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) :=
  HasSmoothBoundary.of_isClopen isClopen_univ

/-- The elimination lemmas recover exactly the data that `HasSmoothBoundary.intro` needs. -/
example (Ω : Set (EuclideanSpace ℝ (Fin 2))) (h : HasSmoothBoundary (𝓡 2) Ω) :
    HasSmoothBoundary (𝓡 2) Ω :=
  HasSmoothBoundary.intro h.isOpen fun _ hp => h.exists_isLocalDefiningFunction hp

/-- The punctured plane does not have smooth boundary. -/
theorem punctured_notHasSmoothBoundary :
    ¬ HasSmoothBoundary (𝓡 2) (({0} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 2))
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set u : EuclideanSpace ℝ (Fin 2) := ‖v‖⁻¹ • v with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      inv_mul_cancel₀ (ne_of_gt hpos)]
  have hu0 : u ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hu1
    norm_num at hu1
  have hmem : (0 : EuclideanSpace ℝ (Fin 2))
      ∈ frontier (({0} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) := by
    rw [frontier_eq_closure_inter_closure, Set.mem_inter_iff]
    constructor
    · rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨(ε / 2) • u, ?_, ?_⟩
      · intro hcon
        have h_eq : (ε / 2) • u = 0 := Set.mem_singleton_iff.mp hcon
        have hne : (ε / 2) • u ≠ 0 :=
          smul_ne_zero (ne_of_gt (show (0 : ℝ) < ε / 2 by linarith)) hu0
        exact hne h_eq
      · rw [dist_zero_left, norm_smul, hu1, mul_one, Real.norm_eq_abs,
          abs_of_pos (show (0 : ℝ) < ε / 2 by linarith)]
        linarith
    · exact subset_closure (by simp)
  intro hH
  obtain ⟨U, ρ, hρ⟩ := hH.exists_isLocalDefiningFunction hmem
  have hUopen : IsOpen U := hρ.isOpen
  have h0U : (0 : EuclideanSpace ℝ (Fin 2)) ∈ U := hρ.mem
  have hCont : ContDiffOn ℝ ∞ ρ U := contMDiffOn_iff_contDiffOn.mp hρ.contMDiffOn
  have hWithin : DifferentiableWithinAt ℝ ρ U (0 : EuclideanSpace ℝ (Fin 2)) :=
    ContDiffWithinAt.differentiableWithinAt (hCont 0 h0U) (by simp)
  have hdiff : DifferentiableAt ℝ ρ (0 : EuclideanSpace ℝ (Fin 2)) :=
    DifferentiableWithinAt.differentiableAt hWithin (hUopen.mem_nhds h0U)
  have hHasF : HasFDerivAt ρ (fderiv ℝ ρ (0 : EuclideanSpace ℝ (Fin 2))) 0 :=
    hdiff.hasFDerivAt
  have hfd_ne : fderiv ℝ ρ (0 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro hcon
    apply hρ.mfderiv_ne_zero
    have hHasMF := hasMFDerivAt_iff_hasFDerivAt.mpr hHasF
    have heq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ρ 0
        = fderiv ℝ ρ (0 : EuclideanSpace ℝ (Fin 2)) :=
      hHasMF.mfderiv
    exact heq.trans hcon
  have hev : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℝ (Fin 2)), ρ x ≤ ρ 0 := by
    filter_upwards [hUopen.mem_nhds h0U] with x hx
    by_cases hx0 : x = 0
    · subst hx0
      exact le_refl _
    · have hxs : x ∈ (({0} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) :=
        fun h => hx0 (Set.mem_singleton_iff.mp h)
      have hlt : ρ x < 0 := (hρ.mem_iff x hx).mp hxs
      rw [hρ.apply_eq_zero]
      exact le_of_lt hlt
  exact hfd_ne (IsLocalMax.hasFDerivAt_eq_zero hev hHasF)

/-- The closed unit disc is not open, so it does not have smooth boundary. -/
theorem closedBall_notHasSmoothBoundary :
    ¬ HasSmoothBoundary (𝓡 2)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  have hno : ¬ IsOpen (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    intro hopen
    obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 2))
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set u : EuclideanSpace ℝ (Fin 2) := ‖v‖⁻¹ • v with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
        inv_mul_cancel₀ (ne_of_gt hpos)]
    have hu_mem : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hu1]
    have hnhds : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∈ 𝓝 u :=
      hopen.mem_nhds hu_mem
    rw [Metric.mem_nhds_iff] at hnhds
    obtain ⟨ε, hε, hsub⟩ := hnhds
    have e1 : (1 + ε / 2) • u - u = (ε / 2) • u := by
      have hsplit : (1 + ε / 2 : ℝ) • u
          = (1 : ℝ) • u + (ε / 2 : ℝ) • u :=
        add_smul _ _ _
      rw [hsplit, one_smul, add_sub_cancel_left]
    have hdist : dist ((1 + ε / 2) • u) u = ε / 2 := by
      rw [dist_eq_norm, e1, norm_smul, hu1, mul_one, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    have hyball : (1 + ε / 2) • u ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, hdist]
      linarith
    have hyclosed := hsub hyball
    rw [Metric.mem_closedBall, dist_zero_right] at hyclosed
    have hnormy : ‖(1 + ε / 2) • u‖ = 1 + ε / 2 := by
      rw [norm_smul, hu1, mul_one, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < 1 + ε / 2)]
    linarith
  intro hH
  exact hno hH.isOpen

/-- The closed half-plane model `𝓡∂ 2` is not boundaryless, so no instance can make
`HasSmoothBoundary (𝓡∂ 2)` well typed. Without that restriction the remaining clauses would
accept `{0}ᶜ` there: it is the strict sublevel set of `ρ x = -(x₀ + x₁²)`, whose differential
at the boundary point `0` is `-dx₀ ≠ 0`, although its frontier is the single point `0`. -/
theorem halfPlane_not_boundaryless : ¬ (𝓡∂ 2).Boundaryless := by
  intro h
  have hmem : EuclideanSpace.single (0 : Fin 2) (-1 : ℝ) ∈ Set.range (𝓡∂ 2) := by
    rw [h.range_eq_univ]
    exact Set.mem_univ _
  rw [range_modelWithCornersEuclideanHalfSpace] at hmem
  norm_num [EuclideanSpace.single, PiLp.single_apply] at hmem

-- The half-plane counterexample cannot even be stated: elaboration fails for lack of a
-- `(𝓡∂ 2).Boundaryless` instance, which `halfPlane_not_boundaryless` shows cannot exist.
/--
error: failed to synthesize instance of type class
  (𝓡∂ 2).Boundaryless
-/
#guard_msgs (error, substring := true) in
example : Prop := HasSmoothBoundary (𝓡∂ 2) ({0}ᶜ : Set (EuclideanHalfSpace 2))

end SmoothBoundaryTest

end Manifold
