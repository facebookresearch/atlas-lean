/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.POTConeFunctorModels
public import MathlibExt.AlgebraicGeometry.StackBundleCones

/-!
# Source-normalized affine frames of the actual bundle-stack diagram

The coefficient points are the literal affine points over the given
scheme-valued stack point. Every base arrow is fixed on its actual
scheme map and its based point arrow. Module frames commute with every
coefficient ring map and with the actual differential.
Source: Behrend--Fantechi, arXiv:alg-geom/9601010, Section4;
Kresch, arXiv:math/9810166v1, and the native affine dictionaries in the imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.POTAffineModuleFrames

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open StackCycleGeometry StackAffineModules StackFibreModels StackBundleCones AffineConeAtlas

variable {S : Scheme.{0}} {X : Stack S} (E : VectorBundleStack X)
  (U : Over S) [IsAffine U.left] (x : X.Fibre U)
  {k : Type} [CommRing k] [Algebra k Γ(U.left, ⊤)]
  (P : _root_.Algebra.Extension.{0} k Γ(U.left, ⊤)) (F : ConePresentation P)

structure Coefficients where
  functor : (CommAlgCat.{0} Γ(U.left, ⊤))ᵒᵖ ⥤ AffinePoint X
  objects : ∀ B, functor.obj (op B) = ringPoint U x B

variable (C : Coefficients U x)

def schemeIso (B : CommAlgCat.{0} Γ(U.left, ⊤)) :
    (pointScheme X).obj (C.functor.obj (op B)) ≅ Spec (.of B) :=
  eqToIso (by rw [C.objects B]; rfl)

def pointArrow (B : CommAlgCat.{0} Γ(U.left, ⊤)) :
    (C.functor.obj (op B)).obj ⟶ point U x :=
  eqToHom (congrArg (fun a : AffinePoint X => a.obj) (C.objects B)) ≫ ringPointArrow U x B

def scalar (B : CommAlgCat.{0} Γ(U.left, ⊤)) :
    B →+* (rings X).obj (op (C.functor.obj (op B))) := ringPointScalar C.objects B

def zeroModule (B : CommAlgCat.{0} Γ(U.left, ⊤)) : ModuleCat.{0} B :=
  (ModuleCat.restrictScalars (scalar U x C B)).obj (E.linear.diagram.modules (C.functor.obj (op B))).degreeZero

def oneModule (B : CommAlgCat.{0} Γ(U.left, ⊤)) : ModuleCat.{0} B :=
  (ModuleCat.restrictScalars (scalar U x C B)).obj (E.linear.diagram.modules (C.functor.obj (op B))).degreeOne

structure Frame where
  arrows : ∀ {B D : CommAlgCat.{0} Γ(U.left, ⊤)} (f : B ⟶ D),
    ((C.functor.map f.op).hom.base.left) =
      (schemeIso U x C D).hom ≫ Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ (schemeIso U x C B).inv
  points : ∀ {B D : CommAlgCat.{0} Γ(U.left, ⊤)} (f : B ⟶ D),
    (C.functor.map f.op).hom ≫ pointArrow U x C B = pointArrow U x C D
  zero : ∀ B : CommAlgCat.{0} Γ(U.left, ⊤), zeroModule E U x C B ≅ ModuleCat.of B (Fin F.zeroRank → B)
  one : ∀ B : CommAlgCat.{0} Γ(U.left, ⊤), oneModule E U x C B ≅ ModuleCat.of B (Fin F.negativeRank → B)
  differential : ∀ (B : CommAlgCat.{0} Γ(U.left, ⊤)) (v : zeroModule E U x C B),
    (one B).hom ((E.linear.diagram.modules (C.functor.obj (op B))).differential v) =
      POTConeFunctorModels.differential P F B ((zero B).hom v)
  zero_naturality : ∀ {B D : CommAlgCat.{0} Γ(U.left, ⊤)} (f : B ⟶ D)
    (v : zeroModule E U x C B) (j : Fin F.zeroRank),
    (zero D).hom ((E.linear.diagram.restriction (C.functor.map f.op)).degreeZero v) j =
      f.hom ((zero B).hom v j)
  one_naturality : ∀ {B D : CommAlgCat.{0} Γ(U.left, ⊤)} (f : B ⟶ D)
    (v : oneModule E U x C B) (j : Fin F.negativeRank),
    (one D).hom ((E.linear.diagram.restriction (C.functor.map f.op)).degreeOne v) j =
      f.hom ((one B).hom v j)

end MathlibExt.AlgebraicGeometry.POTAffineModuleFrames
