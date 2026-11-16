/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricHitchinFiltrations
public import MathlibExt.AlgebraicGeometry.RankTwoHiggsAnalyticFrames

/-!
# Native shifts, ordinary cutoff and nonzero cotangent regressions

Canonical shift addition identifies H^(d-a)(K[a]) with H^d(K), including
negative d-a. Ordinary truncation of Q in degree zero vanishes below zero
and is unchanged at zero, as required by the k-d weight cutoff. An actual
realized cotangent generator cannot be replaced by zero and erase theta.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.HitchinFiltrationNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PerverseSheaves BettiRealization BoundedBettiDirectImages GeometricHitchinFiltrations
open RankTwoHiggsCurveFamilies RankTwoHiggsAnalyticFrames
open ComplexAnalytification KahlerClassGeometry
open scoped Manifold ContDiff

attribute [local instance] HasDerivedCategory.standard

theorem shift_hypercohomology_bijective (Y : TopCat.{0}) (K : RationalDerived Y) (a d : ℤ) :
    Function.Bijective (shiftHypercohomology K a d) := by
  simpa [shiftHypercohomology, Iso.homCongr] using
    (Iso.homCongr (Iso.refl (rationalUnit Y))
      ((shiftFunctorAdd' (RationalDerived Y) a (d - a) d (by omega)).app K).symm).bijective

theorem ordinary_constant_below_zero (Y : TopCat.{0}) :
    IsZero ((DerivedCategory.TStructure.t.truncLE (-1)).obj (rationalUnit Y)) := by
  change IsZero ((DerivedCategory.TStructure.t.truncLE (-1)).obj
    ((DerivedCategory.singleFunctor (RationalSheaf Y) 0).obj (rationalConstantSheaf Y)))
  exact DerivedCategory.TStructure.t.isZero_truncLE_obj_of_isGE (-1) 0 (by omega) _

theorem ordinary_constant_at_zero (Y : TopCat.{0}) :
    IsIso ((DerivedCategory.TStructure.t.truncLEι 0).app (rationalUnit Y)) := by
  change IsIso ((DerivedCategory.TStructure.t.truncLEι 0).app
    ((DerivedCategory.singleFunctor (RationalSheaf Y) 0).obj (rationalConstantSheaf Y)))
  infer_instance

theorem realized_cotangent_ne_zero (C : RankTwoHiggsCurveFamilies.ComplexScheme)
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    (E : GeometricHiggsFamilies.TwistedBundle C.left (canonicalLine C) 2)
    (V : AnalyticFrames C E) (i : Fin V.bundle.count) (x : ComplexPoints C.hom)
    (hx : x.Mem (V.chart i)) : V.cotangent i x ≠ 0 := by
  intro h
  obtain ⟨u, hu⟩ := (V.cotangent_nondegenerate i x hx).2 (1 : ℂ)
  rw [h] at hu
  simp at hu

end MathlibExtTest.AlgebraicGeometry.HitchinFiltrationNormalization
