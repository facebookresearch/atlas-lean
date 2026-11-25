/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGenericSourceModels
public import MathlibExt.AlgebraicGeometry.StackAffineModules
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# All source presentations and all affine tests for generic Li sources

The index contains every affine parent, every qualified finite-type
source presentation, every component/Cech tuple and every actual local
lift. It also contains every arbitrary-affine base change into each
source chart and actual etale covering arrows over every parent.

Qualification is geometric data on a source chart, supplied by the
relative or central native family frame. It is retained as data. The
category's morphisms are the actual affine-stack arrows, including
stabilizers, with their native coefficient-ring maps.

Sources: Jun Li math/0110113v1 Sections 1--2 and math/0009097v1 Section 4;
native stack affine points and module presheaves at the frozen public
Atlas/Mathlib source revisions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGenericSourceIndex

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry GeneralStackGeometry StackCycleGeometry StackAffineModules StackFibreModels
open LiGenericSourceModels
open scoped Simplicial

variable {k : Type} [Field k] (X : Stack (Spec (.of k)))

/-- A source chart has a native moduli point and actual universal Li source data. -/
structure SourceChart where
  ring : Type
  [commRing : CommRing ring]
  [algebra : Algebra k ring]
  point : X.Fibre (Over.mk (Spec.algebraMap k ring))
  noetherian : IsNoetherian (Spec (.of ring))
  finiteType : LocallyOfFiniteType (Spec.algebraMap k ring)
  family : MapFamily k ring
  source : LiGenericSourceModels.Source family
  coefficients : SourceCoefficientFunctor family source
  coefficient_normalization : SourceCoefficientNormalization family coefficients
  deformations : DeformationClassification family source

attribute [instance] SourceChart.commRing SourceChart.algebra

variable {X}

def SourceChart.spec (C : SourceChart X) : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap k C.ring)

def SourceChart.native (C : SourceChart X) : AffinePoint X :=
  ⟨StackFibreModels.point C.spec C.point, by
    change IsAffine (Spec (.of C.ring))
    infer_instance⟩

abbrev SourceChart.Lift (C : SourceChart X) (v : Fin C.family.components)
    (i : Fin (C.source.cover v).count) :=
  LiGenericSourceModels.Lift C.family C.source.classification C.source.universal
    (C.source.cover v) i

variable (X) (Frame : SourceChart X → Type 2)

/-- A common refinement keeps both actual stack arrows and the native covering. -/
structure Refinement (C E : SourceChart X) (f : E.native ⟶ C.native) where
  chart : SourceChart X
  qualification : Frame chart
  left : chart.native ⟶ C.native
  right : chart.native ⟶ E.native
  composite : right ≫ f = left
  etale : Etale right.hom.base.left
  covering : Function.Surjective right.hom.base.left

inductive LocalChoice where
  | chart (C : SourceChart X) (qualified : Frame C)
  | member (C : SourceChart X) (qualified : Frame C) (v : Fin C.family.components)
      (z : SimplexCategory) (a : Fin (z.len + 1) → Fin (C.source.cover v).count)
  | lift (C : SourceChart X) (qualified : Frame C) (v : Fin C.family.components)
      (i : Fin (C.source.cover v).count) (L : C.Lift v i)
  | baseChange (C : SourceChart X) (qualified : Frame C) (p : AffinePoint X)
      (map : p ⟶ C.native)
  | cover (C : SourceChart X) (qualified : Frame C) (p : AffinePoint X)
      (map : C.native ⟶ p) (etale : Etale map.hom.base.left)
      (covering : Function.Surjective map.hom.base.left)
  | baseChangeCover (C : SourceChart X) (qualified : Frame C) (p q : AffinePoint X)
      (toChart : q ⟶ C.native) (toParent : q ⟶ p)
      (etale : Etale toParent.hom.base.left)
      (covering : Function.Surjective toParent.hom.base.left)
  | refinement (C E : SourceChart X) (qualifiedC : Frame C) (qualifiedE : Frame E)
      (f : E.native ⟶ C.native) (V : Refinement X Frame C E f)

def localChart : LocalChoice X Frame → SourceChart X
  | .chart C _ => C
  | .member C _ _ _ _ => C
  | .lift C _ _ _ _ => C
  | .baseChange C _ _ _ => C
  | .cover C _ _ _ _ _ => C
  | .baseChangeCover C _ _ _ _ _ _ _ => C
  | .refinement _ _ _ _ _ V => V.chart

def localNative : LocalChoice X Frame → AffinePoint X
  | .baseChange _ _ p _ => p
  | .baseChangeCover _ _ _ q _ _ _ _ => q
  | i => (localChart X Frame i).native

inductive FullChoice where
  | parent (p : AffinePoint X)
  | local (i : LocalChoice X Frame)

def native : FullChoice X Frame → AffinePoint X
  | .parent p => p
  | .local i => localNative X Frame i

abbrev Index := InducedCategory (AffinePoint X) (native X Frame)
abbrev LiftIndex := InducedCategory (AffinePoint X) (localNative X Frame)

def projection : Index X Frame ⥤ AffinePoint X := inducedFunctor (native X Frame)

def parent : AffinePoint X ⥤ Index X Frame where
  obj p := .parent p
  map f := InducedCategory.homMk f

def includeLift : LiftIndex X Frame ⥤ Index X Frame where
  obj i := .local i
  map f := InducedCategory.homMk f.hom

def coefficientRings : (Index X Frame)ᵒᵖ ⥤ RingCat.{0} :=
  (projection X Frame).op ⋙ rings X ⋙ forget₂ CommRingCat RingCat

abbrev LargeModules := PresheafOfModules.{2} (coefficientRings X Frame)
abbrev LargeLiftModules := PresheafOfModules.{2}
  ((includeLift X Frame).op ⋙ coefficientRings X Frame)

def restrictToLifts : LargeModules X Frame ⥤ LargeLiftModules X Frame :=
  PresheafOfModules.pushforward₀ (includeLift X Frame) (coefficientRings X Frame)

def parentRestriction : LargeModules X Frame ⥤
    PresheafOfModules.{2} (rings X ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward₀ (parent X Frame) (coefficientRings X Frame)

@[simp] theorem parent_projection : parent X Frame ⋙ projection X Frame = 𝟭 (AffinePoint X) := rfl

end MathlibExt.AlgebraicGeometry.LiGenericSourceIndex
