/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.PoincareBendixson
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Tests for `MathlibExt.Dynamics.PoincareBendixson` -/

namespace MathlibExtTest.PoincareBendixson

open MathlibExt.Dynamics.PoincareBendixsonWanted.Dynamics

-- Test section: a field without equilibria. Every bounded forward orbit of a `C¹` field without
-- zeros accumulates on a non-constant periodic orbit, which is its whole ω-limit set.
example (F : Plane → Plane) (hF : ContDiff ℝ 1 F) (hF0 : ∀ x, F x ≠ 0) (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x => F x) (Set.Ici 0))
    (hb : Bornology.IsBounded (γ '' Set.Ici 0)) :
    ∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → Plane, IsIntegralCurve β (fun _ x => F x) ∧
      (∀ t, β (t + T) = β t) ∧ (⋂ s : ℝ, closure (γ '' Set.Ici s)) = Set.range β := by
  rcases poincare_bendixson F hF γ hγ with h | ⟨x₀, hx₀, -⟩ | ⟨T, hT, β, hβ, hper, -, hω⟩
  · exact absurd hb h
  · exact absurd hx₀ (hF0 x₀)
  · exact ⟨T, hT, β, hβ, hper, hω⟩

-- Test section: the rotation field `(x, y) ↦ (-y, x)` and the unit circle. The hypotheses of the
-- theorem hold, the orbit is bounded and the only equilibrium is the origin, which lies off the
-- circle, so the theorem yields the periodic alternative.

/-- The rotation field `(x, y) ↦ (-y, x)`, written through the identification of the plane with
`ℂ`. -/
private noncomputable def rot (v : Plane) : Plane :=
  Complex.orthonormalBasisOneI.repr (Complex.I * Complex.orthonormalBasisOneI.repr.symm v)

/-- The unit circle `t ↦ (cos t, sin t)`. -/
private noncomputable def circ (t : ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr (Complex.exp (t * Complex.I))

private theorem contDiff_rot : ContDiff ℝ 1 rot :=
  Complex.orthonormalBasisOneI.repr.contDiff.comp
    ((contDiff_const.mul contDiff_id).comp Complex.orthonormalBasisOneI.repr.symm.contDiff)

private theorem isIntegralCurve_circ : IsIntegralCurve circ (fun _ x => rot x) := by
  intro t
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I))
      (Complex.exp (t * Complex.I) * (1 * Complex.I)) t :=
    ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp
  have h2 := (Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toContinuousLinearMap
    |>.hasFDerivAt (x := Complex.exp (t * Complex.I))).comp_hasDerivAt t h1
  change HasDerivAt circ (rot (circ t)) t
  have e : rot (circ t) = Complex.orthonormalBasisOneI.repr
      (Complex.exp (t * Complex.I) * (1 * Complex.I)) := by
    simp only [rot, circ, LinearIsometryEquiv.symm_apply_apply]
    ring_nf
  rw [e]
  exact h2

private theorem norm_circ (t : ℝ) : ‖circ t‖ = 1 := by
  simp [circ, Complex.norm_exp_ofReal_mul_I]

example : ∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → Plane, IsIntegralCurve β (fun _ x => rot x) ∧
    (∀ t, β (t + T) = β t) ∧ rot (β 0) ≠ 0 ∧
    (⋂ s : ℝ, closure (circ '' Set.Ici s)) = Set.range β := by
  have hsub : circ '' Set.Ici 0 ⊆ Metric.sphere 0 1 := by
    rintro _ ⟨t, -, rfl⟩
    simp [norm_circ]
  rcases poincare_bendixson rot contDiff_rot circ (isIntegralCurve_circ.isIntegralCurveOn _) with
    h | ⟨x₀, hx₀, hmem⟩ | h
  · exact absurd ((Metric.isBounded_sphere).subset hsub) h
  · exfalso
    have hx : x₀ = 0 := by
      have : Complex.I * Complex.orthonormalBasisOneI.repr.symm x₀ = 0 :=
        Complex.orthonormalBasisOneI.repr.map_eq_zero_iff.1 hx₀
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h Complex.I_ne_zero
      · exact Complex.orthonormalBasisOneI.repr.symm.map_eq_zero_iff.1 h
    have h1 : x₀ ∈ Metric.sphere (0 : Plane) 1 :=
      closure_minimal hsub Metric.isClosed_sphere (Set.mem_iInter.1 hmem 0)
    rw [hx, mem_sphere_iff_norm, sub_zero, norm_zero] at h1
    exact zero_ne_one h1
  · exact h

end MathlibExtTest.PoincareBendixson
