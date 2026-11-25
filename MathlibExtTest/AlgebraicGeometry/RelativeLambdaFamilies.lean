/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CoarseHodgeScaling
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
Boundary probes for the actual zero-dimensional source and a nonreduced
parameter scheme. The source Spec C has semistable bundles of rank greater
than one, while stability there is rank one. The dual-number parameter is
nonzero as a global section but vanishes at every complex-valued point, so
the all-scheme family functor must retain its actual parameter section.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section

  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PerverseSheaves AdmissibleRelativeLambdaFamilies LambdaConnectionStability
open ProjectiveLineSystems PolarizedHiggsStability RelativeDeRhamDifferential

private abbrev point : ComplexScheme := scalarBase

section Point

variable (D : Differential point.hom) (H : LineBundle point.left)
  (N : HilbertNumerics point H 0)
  (E : CoherentConnection (X := point) point.hom 1 D)

example (rank : E.connection.rank = 1) : LambdaConnectionStability.IsStable N E :=
  (isStable_dimension_zero N E).mpr rank

example (rank : E.connection.rank = 2) :
    LambdaConnectionStability.IsSemistable N E ∧ ¬ LambdaConnectionStability.IsStable N E := by
  constructor
  · apply (isSemistable_dimension_zero N E).mpr
    rw [rank]
    decide
  · rw [isStable_dimension_zero N E, rank]
    decide

end Point

private abbrev ParameterRing := TrivSqZeroExt ℂ ℂ

private def epsilon : ParameterRing := TrivSqZeroExt.inr 1

private abbrev infinitesimalScheme : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ ParameterRing)))

private def nilpotentParameter : Γ(infinitesimalScheme.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ParameterRing)).inv.hom epsilon

example : nilpotentParameter ≠ 0 := by
  intro h
  have he : epsilon = 0 :=
    (Scheme.ΓSpecIso (CommRingCat.of ParameterRing)).commRingCatIsoToRingEquiv.symm.injective
      (by
        change (Scheme.ΓSpecIso (CommRingCat.of ParameterRing)).inv.hom epsilon =
          (Scheme.ΓSpecIso (CommRingCat.of ParameterRing)).inv.hom 0
        simpa only [nilpotentParameter, map_zero] using h)
  have hs := congrArg TrivSqZeroExt.snd he
  simp [epsilon] at hs

example : nilpotentParameter ^ 2 = 0 := by
  change ((Scheme.ΓSpecIso (CommRingCat.of ParameterRing)).inv.hom epsilon) ^ 2 = 0
  rw [← map_pow, pow_two, epsilon, TrivSqZeroExt.inr_mul_inr, map_zero]

example (g : ParameterRing →ₐ[ℂ] ℂ) : g epsilon = 0 := by
  have h : g epsilon * g epsilon = 0 := by
    rw [← map_mul, epsilon, TrivSqZeroExt.inr_mul_inr, map_zero]
  exact (mul_eq_zero.mp h).elim id id
