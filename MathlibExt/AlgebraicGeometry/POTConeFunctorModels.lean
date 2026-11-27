/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineConeAtlas
public import MathlibExt.AlgebraicGeometry.StackBundleCones
public import MathlibExt.AlgebraicGeometry.LiFiniteComplexPresentations

/-!
# Actual affine POT cone coordinates and tangent translations

Each obstruction coordinate is the actual normal-cone functional on the
POT's negative cotangent map. Tangent translations are the actual tangent
functional on its degree-zero cotangent map. Their relation is the
displayed cotangent-comparison chain equation. These formulas fix the
cone functor before its global stack realization.
Source: Behrend--Fantechi, arXiv:alg-geom/9601010, Section4;
native Axiom/Mathlib conormal and associated-graded source in the imports.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.POTConeFunctorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open AffineConeAtlas StackBundleCones
open scoped BigOperators

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
  (P : _root_.Algebra.Extension.{0} k A) (F : ConePresentation P)
  (B : Type) [CommRing B] [Algebra A B]

def differential : (Fin F.zeroRank → B) →ₗ[B] (Fin F.negativeRank → B) where
  toFun x j := ∑ i : Fin F.zeroRank,
    algebraMap A B (F.differential (Pi.single j 1) i) * x i
  map_add' x y := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def tangentMatrix : LiFiniteComplexPresentations.Matrix A where
  leftRank := F.zeroRank
  rightRank := F.negativeRank
  differential := differential P F A

theorem linearCoordinates {r : ℕ} (f : (Fin r → A) →ₗ[A] B) (v : Fin r → A) :
    f v = ∑ i : Fin r, algebraMap A B (v i) * f (Pi.single i 1) := by
  have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : A) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [f.map_smul]
  exact Algebra.smul_def _ _

def coneFunctor : IntrinsicConePoint P B ⥤ AdditiveQuotient (differential P F B) where
  obj x := ⟨fun j => x.map (normalCotangent P (F.negativeMap (Pi.single j 1)))⟩
  map {x y} h :=
    { translation := fun i => h.tangent (F.zeroMap (Pi.single i 1))
      relation := by
        ext j
        change y.map (normalCotangent P (F.negativeMap (Pi.single j 1))) =
          x.map (normalCotangent P (F.negativeMap (Pi.single j 1))) + _
        rw [h.relation]
        congr 1
        have hc := LinearMap.congr_fun F.comm (Pi.single j 1)
        change P.cotangentComplex (F.negativeMap (Pi.single j 1)) =
          F.zeroMap (F.differential (Pi.single j 1)) at hc
        rw [hc]
        exact linearCoordinates (B := B) (h.tangent.comp F.zeroMap) (F.differential (Pi.single j 1)) }
  map_id x := by apply AdditiveQuotient.hom_ext; rfl
  map_comp h j := by apply AdditiveQuotient.hom_ext; rfl

end MathlibExt.AlgebraicGeometry.POTConeFunctorModels
