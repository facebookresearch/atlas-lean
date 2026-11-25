/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The category of normalized algebraic Berkovich realizations

Objects retain an actual scheme and the normalized affinoid sheaf atlas.
Morphisms retain an actual scheme map and an actual locally ringed map,
with their canonical point map and regular-function square. The two
forgetful functors and category laws are completed constructions.

The category construction uses explicitly characterized bounded-identity
and bounded-composition closure proofs. Those are separate shared Wanted
dependencies; locally ringed maps alone do not supply analytic closure.

`SchemeAnalytification` is the general functor-lifting contract for all
locally finite-type schemes over the prescribed valued field. Its
construction, not the category definition, is the unresolved provider.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.BerkovichAnalyticCategory

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticGeometry
open MathlibExt.AlgebraicGeometry.BerkovichAnalytification

variable (K : Type) [NormedField K] [IsUltrametricDist K]

structure RealizedScheme where
  scheme : AlgebraicScheme K
  analytic : AnalyticSpace scheme

namespace RealizedScheme

variable {K} (X Y Z : RealizedScheme K)

structure Hom where
  schemeMap : X.scheme ⟶ Y.scheme
  analyticMap : X.analytic.locallyRinged ⟶ Y.analytic.locallyRinged
  point_map : analyticMap.base = BerkovichAnalytification.map schemeMap
  square : analyticMap.toShHom ≫ Y.analytic.algebraic =
    X.analytic.algebraic ≫ schemeMap.left.toLRSHom.toShHom
  bounded : X.analytic.IsLocallyBounded Y.analytic analyticMap.toShHom

@[ext]
theorem Hom.ext {f g : Hom X Y} (hs : f.schemeMap = g.schemeMap)
    (ha : f.analyticMap = g.analyticMap) : f = g := by
  cases f
  cases g
  cases hs
  cases ha
  rfl

end RealizedScheme

/-- Closure of the fixed bounded chart condition under the actual identity
and composition operations. This is geometric proof input, not free maps. -/
class BoundedComposition : Prop where
  identity (X : RealizedScheme K) :
    X.analytic.IsLocallyBounded X.analytic (𝟙 X.analytic.ringed)
  composition (X Y Z : RealizedScheme K)
      (f : RealizedScheme.Hom X Y) (g : RealizedScheme.Hom Y Z) :
    X.analytic.IsLocallyBounded Z.analytic
      (f.analyticMap ≫ g.analyticMap).toShHom

namespace RealizedScheme

variable {K} [BoundedComposition K] (X Y Z : RealizedScheme K)

def Hom.id : Hom X X where
  schemeMap := 𝟙 X.scheme
  analyticMap := 𝟙 X.analytic.locallyRinged
  point_map := by ext p; exact (mapPoint_id p).symm
  square := by
    change (𝟙 X.analytic.ringed) ≫ X.analytic.algebraic =
      X.analytic.algebraic ≫ 𝟙 X.scheme.left.toRingedSpace
    simp
  bounded := BoundedComposition.identity X

def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  schemeMap := f.schemeMap ≫ g.schemeMap
  analyticMap := f.analyticMap ≫ g.analyticMap
  point_map := by
    rw [LocallyRingedSpace.comp_base, f.point_map, g.point_map]
    ext p
    exact (mapPoint_comp f.schemeMap g.schemeMap p).symm
  square := by
    rw [LocallyRingedSpace.comp_toShHom, Category.assoc, g.square,
      ← Category.assoc, f.square]
    rfl
  bounded := BoundedComposition.composition X Y Z f g

instance : Category (RealizedScheme K) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp _ _ _ f g
  id_comp _f := Hom.ext _ _ (Category.id_comp _) (Category.id_comp _)
  comp_id _f := Hom.ext _ _ (Category.comp_id _) (Category.comp_id _)
  assoc _f _g _h := Hom.ext _ _ (Category.assoc _ _ _) (Category.assoc _ _ _)

end RealizedScheme

variable [BoundedComposition K]

/-- The algebraic forgetful functor retains the actual scheme morphisms. -/
def forgetAlgebraic : RealizedScheme K ⥤ AlgebraicScheme K where
  obj X := X.scheme
  map f := f.schemeMap

/-- The analytic forgetful functor retains the actual locally ringed maps. -/
def forgetAnalytic : RealizedScheme K ⥤ LocallyRingedSpace where
  obj X := X.analytic.locallyRinged
  map f := f.analyticMap

def locallyFiniteType : ObjectProperty (AlgebraicScheme K) :=
  fun X ↦ LocallyOfFiniteType X.hom

abbrev LocallyFiniteTypeScheme := (locallyFiniteType K).FullSubcategory

/-- A general analytification is a functor lifting the actual algebraic
inclusion, with its identification supplied by a natural isomorphism. -/
structure SchemeAnalytification where
  functor : LocallyFiniteTypeScheme K ⥤ RealizedScheme K
  algebraicComparison : functor ⋙ forgetAlgebraic K ≅ (locallyFiniteType K).ι

end MathlibExt.AlgebraicGeometry.BerkovichAnalyticCategory
