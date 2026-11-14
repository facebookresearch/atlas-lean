/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

@[expose] public noncomputable section

/-!
# Pointed Picard-zero families

Line bundles are normalized along a specified point of a curve. The
representative below is characterized on all test schemes by actual
pullbacks of its universal bundle. The group law is linked to the
ordinary sheaf tensor, and the identity represents the trivial bundle.

Reference: Bosch--Lütkebohmert--Raynaud, *Néron Models*, Chapter 9.
-/

namespace MathlibExt.AlgebraicGeometry.PointedPicardFamilies

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

universe u

/-- The chosen point of a curve after extension over a parameter scheme. -/
def sectionAt {k : Type u} [Field k]
    (C T : Over (Spec (.of k))) (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    T ⟶ prod C T :=
  prod.lift (toUnit T ≫ p) (𝟙 T)

/-- Normalization along the chosen point, on the actual pulled-back module. -/
def IsNormalized {k : Type u} [Field k]
    (C T : Over (Spec (.of k))) (p : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    (L : (prod C T).left.Modules) : Prop :=
  Nonempty ((Scheme.Modules.pullback (sectionAt C T p).left).obj L ≅
    structureModule T.left)

/-- A Picard-zero representative with its universal family and group laws. -/
structure PicardZeroModel {k : Type u} [Field k]
    (C : Over (Spec (.of k))) (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) where
  /-- The representing group scheme. -/
  J : Over (Spec (.of k))
  [group : GrpObj J]
  [commutative : IsCommMonObj J]
  [smoothDimension : SmoothOfRelativeDimension (genus C.hom) J.hom]
  [connected : GeometricallyConnected J.hom]
  /-- The actual universal module. -/
  P : (prod C J).left.Modules
  lineBundle : IsLineBundle P
  normalized : IsNormalized C J p P
  algebraicallyTrivial :
    IsFibrewiseAlgebraicallyTrivial (prod.snd : prod C J ⟶ J).left P
  /-- The group identity represents the trivial line bundle on the curve. -/
  identity :
    Nonempty ((Scheme.Modules.pullback (pointSection C J η[J]).left).obj P ≅
      structureModule C.left)
  /-- Addition of parameters represents tensoring the two families. -/
  addition : ∀ (T : Over (Spec (.of k))) (f g : T ⟶ J),
    Nonempty (familyPullback C J T P
      (CartesianMonoidalCategory.lift f g ≫ μ[J]) ≅
      moduleTensor (prod C T).left
        (familyPullback C J T P f) (familyPullback C J T P g))
  /-- Universal parameter maps for all normalized Picard-zero families. -/
  universal : ∀ (T : Over (Spec (.of k))) (L : (prod C T).left.Modules),
    IsLineBundle L → IsNormalized C T p L →
    IsFibrewiseAlgebraicallyTrivial (prod.snd : prod C T ⟶ T).left L →
      ∃! f : T ⟶ J, Nonempty (familyPullback C J T P f ≅ L)

end MathlibExt.AlgebraicGeometry.PointedPicardFamilies
