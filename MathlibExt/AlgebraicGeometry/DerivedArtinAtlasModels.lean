/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual derived Artin atlas and geometricity predicates

The base level consists of the actual augmented derived-affine models.
A representability test takes every actual affine family into the target
and tests the native stack homotopy pullback. Higher levels require the
same lower-level test for the diagonal and for a smooth affine atlas.
Atlas surjectivity is on the actual path components at algebraically
closed field points; it is not a freely named surjective map.

The level convention is explicit: level zero is affine and level n+1
is the next geometric-atlas step. Derived Artin means some finite level.
Local finite presentation and future cotangent/closed-form constructions
are separate predicates and construction dependencies.

References: Toën--Vezzosi, HAG II, §2.2; Toën--Vaquié,
arXiv:math/0503269v5, §2.3 (geometric D⁻-stacks), pp. 27--28; PTVV,
arXiv:1111.3209v4, conventions and §1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels

open CategoryTheory Limits
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels

universe u

variable {k : Type u} [CommRing k]
variable {Q : AlgebraReplacementFunctor k}

/-- The actual constant simplicial algebra of a field-valued point. -/
def fieldAlgebra (L : Type u) [Field L] [Algebra k L] : SAlg k :=
  (SimplicialObject.const (CommAlgCat.{u} k)).obj (CommAlgCat.of k L)

/-- Representability uses every actual affine-family homotopy fibre. -/
def IsRepresentableBy (property : DerivedStack Q → Prop)
    {F G : DerivedStack Q} (f : StackMap F G) : Prop :=
  ∀ (A : SAlg k) (M : AffineStackModel Q A) (x : StackMap M.stack G)
    (P : NaturalPathModel G), ∃ N : FibreStackModel P f x, property N.stack

/-- Actual geometric-point surjectivity of a family of affine-stack maps. -/
def JointlySurjectiveOnGeometricPoints {I : Type (u + 1)}
    {A : I → SAlg k} (M : ∀ i, AffineStackModel Q (A i)) (F : DerivedStack Q)
    (a : ∀ i, StackMap (M i).stack F) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra k L] [IsAlgClosed L],
    ∀ y : SSet.toTop.obj (F.functor.obj (fieldAlgebra (k := k) L)),
      ∃ (i : I) (x : SSet.toTop.obj ((M i).stack.functor.obj (fieldAlgebra (k := k) L))),
        Joined (SSet.toTop.map ((a i).app (fieldAlgebra (k := k) L)) x) y

/-- One geometric step is fixed by the actual diagonal and smooth affine atlas. -/
def GeometricStep (lower : DerivedStack Q → Prop) (F : DerivedStack Q) : Prop :=
  ∃ D : ProductStackModel F F, IsRepresentableBy lower (diagonal F D) ∧
    ∃ (I : Type (u + 1)) (A : I → SAlg k)
      (M : ∀ i, AffineStackModel Q (A i)) (a : ∀ i, StackMap (M i).stack F),
      (∀ i, IsRepresentableBy lower (a i) ∧ IsSmooth (a i)) ∧
        JointlySurjectiveOnGeometricPoints M F a

/-- Actual geometricity: zero is affine, and each successor is the atlas step. -/
def IsGeometric : ℕ → DerivedStack Q → Prop
  | 0, F => IsAffine Q F
  | n + 1, F => GeometricStep (IsGeometric n) F

/-- A derived Artin stack has an actual finite geometric presentation level. -/
def IsDerivedArtin (F : DerivedStack Q) : Prop :=
  ∃ n : ℕ, IsGeometric n F

/-- An explicit finite geometric presentation, with no cotangent/form conclusion. -/
structure ArtinPresentation (F : DerivedStack Q) where
  level : ℕ
  geometric : IsGeometric level F

/-- A native affine augmentation is an actual level-zero presentation. -/
theorem AffineStackModel.isGeometric {A : SAlg k} (M : AffineStackModel Q A) :
    IsGeometric 0 M.stack := ⟨A, M.augmentation, M.weak⟩

/-- The actual affine model is derived Artin in the stated level convention. -/
theorem AffineStackModel.isDerivedArtin {A : SAlg k} (M : AffineStackModel Q A) :
    IsDerivedArtin M.stack := ⟨0, AffineStackModel.isGeometric M⟩

/-- An explicit atlas presentation supplies the geometricity predicate. -/
theorem ArtinPresentation.isDerivedArtin {F : DerivedStack Q} (P : ArtinPresentation F) :
    IsDerivedArtin F := ⟨P.level, P.geometric⟩

end MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
