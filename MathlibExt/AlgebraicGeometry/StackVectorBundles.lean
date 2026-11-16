/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackAffineModules
public import Mathlib.CategoryTheory.Elements

/-!
# Stack vector bundles as representations of actual module sections

The total stack represents the actual underlying presheaf of sections of a
cartesian locally free module on affine stack points. The comparison is an
equivalence of the total affine-point categories over the actual base-point
category; it is not a collection of unrelated pointwise bijections.

Maps are fixed by the genuine linear presheaf morphism and its induced
category-of-elements functor. Scheme fibres retain the entire represented
fibred category. This is the vector-bundle index used by Kresch's integral
Chow construction (arXiv:math/9810166v1, Definition 2.1.3).
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackVectorBundles

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackAffineModules

variable {S : Scheme.{0}}

def affineMap {X Y : Stack S} (f : StackHom X Y) : AffinePoint X ⥤ AffinePoint Y where
  obj a := ⟨(totalMap f).obj a.obj, a.property⟩
  map h := ObjectProperty.homMk ((totalMap f).map h.hom)
  map_id a := by apply ObjectProperty.hom_ext; exact (totalMap f).map_id a.obj
  map_comp h k := by apply ObjectProperty.hom_ext; exact (totalMap f).map_comp h.hom k.hom

def sectionPresheaf {X : Stack S} (M : FPModule X) : (AffinePoint X)ᵒᵖ ⥤ Type :=
  M.presheaf.presheaf ⋙ forget AddCommGrpCat

def sectionForget {X : Stack S} (M : FPModule X) :
    (sectionPresheaf M).Elementsᵒᵖ ⥤ AffinePoint X :=
  (Functor.Elements.π (sectionPresheaf M)).leftOp

/-- A native invertible modification of actual relative stack maps. -/
structure TwoIso {X Y : Stack S} (p q : StackHom X Y) where
  app : ∀ T : Over S, StackCycleGeometry.component p T ≅ StackCycleGeometry.component q T
  naturality : ∀ {T V : Over S} (a : V ⟶ T),
    Functor.whiskerLeft (pull X a) (app V).hom ≫
      (Cat.Hom.toNatIso (q.naturality a.op.toLoc)).hom =
    (Cat.Hom.toNatIso (p.naturality a.op.toLoc)).hom ≫
      Functor.whiskerRight (app T).hom (pull Y a)

/-- A rank-r vector bundle on the actual stack, with its represented
module-section total space and genuine scheme fibres. -/
structure VectorBundle (X : Stack S) where
  rank : ℕ
  module : VectorModule X rank
  total : Stack S
  projection : StackHom total X
  comparison : AffinePoint total ≌ (sectionPresheaf module.val).Elementsᵒᵖ
  overBase : comparison.functor ⋙ sectionForget module.val ≅ affineMap projection
  fibres : ∀ (T : Over S) (x : X.Fibre T), SchemeFibreModel projection T x

def sectionMap {X : Stack S} {M N : FPModule X}
    (f : M.presheaf ⟶ N.presheaf) : sectionPresheaf M ⟶ sectionPresheaf N where
  app a := ↾fun m => f.app a m
  naturality {a b} g := by
    apply ConcreteCategory.hom_ext
    intro m
    exact PresheafOfModules.naturality_apply f g m

/-- The total-space map is normalized through the actual linear map on
sections, retaining its square over X. -/
structure BundleMap {X : Stack S} (F E : VectorBundle X) where
  linear : F.module.val.presheaf ⟶ E.module.val.presheaf
  total : StackHom F.total E.total
  overBase : TwoIso (Pseudofunctor.StrongTrans.vcomp total E.projection) F.projection
  normalized : F.comparison.functor ⋙ (sectionMap linear).mapElements.op ≅
    affineMap total ⋙ E.comparison.functor

def BundleMap.IsSurjective {X : Stack S} {F E : VectorBundle X}
    (f : BundleMap F E) : Prop :=
  ∀ a : (AffinePoint X)ᵒᵖ, Function.Surjective (f.linear.app a)

end AlgebraicGeometry.StackVectorBundles
