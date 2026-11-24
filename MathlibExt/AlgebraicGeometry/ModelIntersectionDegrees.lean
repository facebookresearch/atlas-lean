/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings
public import Mathlib.Basic.Real.Basic

/-!
# Actual coherent Euler degrees for model intersections

The degree of a model tuple is the alternating finite difference of the
Euler characteristics of its actual subset tensor sheaves. Every cochain
presentation is identified with the native derived direct image after the
specified affine pullback. Terms have finite projective modules in all
degrees; no two-term amplitude or assigned numerical degree is used.

These expressions retain nonreduced schemes. For pure-dimensional proper
models they give the ordinary multilinear intersection degree. They are the
model coefficients used by adelic completion and Chern measures, not an
independently chosen height function.

Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 4.1--4.2 and Proposition
4.1.1; native bounded determinant/coherent direct-image interfaces in Atlas.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ModelIntersectionDegrees

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open BoundedProjectiveDeterminants RelativeDeterminantPairings

variable {K : Type} [Field K]

/-- The actual alternating term dimension of a bounded perfect presentation. -/
def boundedEuler (C : BoundedProjectiveDeterminants.Complex K) : ℤ :=
  ((BoundedProjectiveDeterminants.degrees K C).map
    (fun i ↦ if Even i then (Module.finrank K (C.cochain.X i) : ℤ)
      else -(Module.finrank K (C.cochain.X i) : ℤ))).sum

/-- Literal cochain isomorphisms preserve this computed Euler expression. -/
theorem boundedEuler_iso (C D : BoundedProjectiveDeterminants.Complex K)
    (e : C.cochain ≅ D.cochain) : boundedEuler C = boundedEuler D := by
  rw [boundedEuler, boundedEuler, BoundedProjectiveDeterminants.degrees_eq_of_iso K C D e]
  congr 1
  apply List.map_congr_left
  intro i _hi
  have h : Module.finrank K (C.cochain.X i) = Module.finrank K (D.cochain.X i) :=
    ((HomologicalComplex.eval _ _ i).mapIso e).toLinearEquiv.finrank_eq
  simp only [h]

attribute [local instance] HasDerivedCategory.standard

variable [FourierMukai.HasDerivedPullbacks.{0}]
  [FourierMukai.HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

/-- The coherent presentations are fixed on the actual model and every subset tensor. -/
structure DegreeData (X : Over (Spec (.of K))) (d : ℕ) (L : Fin d → X.left.Modules) where
  [proper : IsProper X.hom]
  [finiteType : LocallyOfFiniteType X.hom]
  pureDimension : IsPureRelativeDimension X.hom d
  line : ∀ i, CoherentCurveLinearSeries.IsLineBundle (L i)
  presentation : Presentations X.hom L (.of K) (𝟙 (Spec (.of K)))

variable {X : Over (Spec (.of K))} {d : ℕ} {L : Fin d → X.left.Modules}

/-- The full alternating subset difference, including the empty subset/unit. -/
def mixedDegree (D : DegreeData X d L) : ℤ := by
  classical
  exact ∑ s : Finset (Fin d),
    if IsPositive s then boundedEuler (D.presentation s).complex
      else -boundedEuler (D.presentation s).complex

/-- Rational model denominators remain attached to the individual actual lines. -/
def rationalMixedDegree (D : DegreeData X d L) (denominator : Fin d → ℕ+) : ℝ :=
  (mixedDegree D : ℝ) / ∏ i : Fin d, (denominator i : ℝ)

omit [FourierMukai.HasDerivedPullbacks] [FourierMukai.HasDerivedPushforwards]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)] in
/-- No zero denominator is permitted in a rational model coefficient. -/
theorem denominator_pos (denominator : Fin d → ℕ+) :
    0 < ∏ i : Fin d, (denominator i : ℝ) := by
  exact Finset.prod_pos (fun i _hi ↦ by exact_mod_cast (denominator i).pos)

end MathlibExt.AlgebraicGeometry.ModelIntersectionDegrees
