/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FrobeniusPerfectionModels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Global qcqs Fp perfection normalized on the entire affine source

Affine objects and every affine map use the native Frobenius DIRECT
colimit rings. The global functor has a whole affine natural comparison,
the original projection and cartesian squares on every actual affine
open restriction. Arbitrary non-open affine tests are not substituted
for this chart normalization. Zero rings and empty schemes remain.

Perfectness is the literal coordinate Frobenius-bijectivity test on all
actual affine opens. The global universal map is composition with the
original projection from perfect source schemes.

Sources: Bhatt--Mathew1807.04725v4, Section5.4/Theorem5.16;
Stacks Project, perfection of characteristic-p schemes. Native Spec,
algebra maps and direct-colimit stages retain their source attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open GeneralArcCoverModels FrobeniusPerfectionModels

variable {p : ℕ} (F : FrobeniusSource p)

/-- The original Fp coefficient structure of the actual affine algebra. -/
def fpStructure (A : FpAlgebras p) : CommRingCat.of (ZMod p) ⟶ (coordinateRings (p := p)).obj A :=
  CommRingCat.ofHom (algebraMap (ZMod p) A)

/-- Every actual algebra map preserves the original coefficient ring map. -/
theorem fpStructure_natural {A B : FpAlgebras p} (f : A ⟶ B) :
    fpStructure A ≫ (coordinateRings (p := p)).map f = fpStructure B := by
  ext x
  exact f.hom.commutes x

/-- The actual affine scheme over Fp, including the zero algebra. -/
def affineFp (A : FpAlgebras p) : FpSchemes p :=
  Over.mk (Y := affine ((coordinateRings (p := p)).obj A)) (Spec.map (fpStructure A))

/-- The affine base equation is proved in the actual native scheme category. -/
theorem affineFp_base_map {A B : FpAlgebras p} (f : A ⟶ B) :
    Spec.map ((coordinateRings (p := p)).map f) ≫ Spec.map (fpStructure A) =
      Spec.map (fpStructure B) := by
  rw [← Spec.map_comp, fpStructure_natural]

theorem affineFp_map_id (A : FpAlgebras p) :
    Spec.map ((coordinateRings (p := p)).map (𝟙 A)) = 𝟙 (Spec ((coordinateRings (p := p)).obj A)) := by
  simp

theorem affineFp_map_comp {A B C : FpAlgebras p} (f : A ⟶ B) (g : B ⟶ C) :
    Spec.map ((coordinateRings (p := p)).map (f ≫ g)) =
      Spec.map ((coordinateRings (p := p)).map g) ≫ Spec.map ((coordinateRings (p := p)).map f) := by
  rw [_root_.CategoryTheory.Functor.map_comp, Spec.map_comp]

/-- The whole actual contravariant affine source functor. -/
def affineFpFunctor : (FpAlgebras p)ᵒᵖ ⥤ FpSchemes p where
  obj A := affineFp A.unop
  map {A B} f := Over.homMk (Spec.map ((coordinateRings (p := p)).map f.unop)) (affineFp_base_map f.unop)
  map_id A := by
    apply (Over.forget (affine (CommRingCat.of (ZMod p)))).map_injective
    exact affineFp_map_id A.unop
  map_comp f g := by
    apply (Over.forget (affine (CommRingCat.of (ZMod p)))).map_injective
    exact affineFp_map_comp g.unop f.unop

/-- The Fp structure on the native affine direct-colimit ring is its actual zero-stage composition. -/
def perfectFpStructure (A : FpAlgebras p) : CommRingCat.of (ZMod p) ⟶ perfectionRing F A :=
  fpStructure A ≫ (stage F 0).app A

/-- Every native direct-colimit algebra map preserves this same zero-stage structure. -/
theorem perfectFpStructure_natural {A B : FpAlgebras p} (f : A ⟶ B) :
    perfectFpStructure F A ≫ (perfectionFunctor F).map f = perfectFpStructure F B := by
  unfold perfectFpStructure
  rw [Category.assoc, ← (stage F 0).naturality f, ← Category.assoc, fpStructure_natural]

/-- The native affine perfection over the original Fp scheme. -/
def affinePerfectFp (A : FpAlgebras p) : FpSchemes p :=
  Over.mk (Y := affine (perfectionRing F A)) (Spec.map (perfectFpStructure F A))

theorem affinePerfection_base_map (A : FpAlgebras p) :
    Spec.map ((stage F 0).app A) ≫ Spec.map (fpStructure A) = Spec.map (perfectFpStructure F A) := by
  rw [← Spec.map_comp]
  rfl

/-- Every affine perfection map is the original native zero-stage Spec map. -/
def affinePerfectionOver (A : FpAlgebras p) : affinePerfectFp F A ⟶ affineFp A :=
  Over.homMk (Spec.map ((stage F 0).app A)) (affinePerfection_base_map F A)

theorem affinePerfect_base_map {A B : FpAlgebras p} (f : A ⟶ B) :
    Spec.map ((perfectionFunctor F).map f) ≫ Spec.map (perfectFpStructure F A) =
      Spec.map (perfectFpStructure F B) := by
  rw [← Spec.map_comp, perfectFpStructure_natural]

theorem affinePerfect_map_id (A : FpAlgebras p) :
    Spec.map ((perfectionFunctor F).map (𝟙 A)) = 𝟙 (Spec (perfectionRing F A)) := by
  simp

theorem affinePerfect_map_comp {A B C : FpAlgebras p} (f : A ⟶ B) (g : B ⟶ C) :
    Spec.map ((perfectionFunctor F).map (f ≫ g)) =
      Spec.map ((perfectionFunctor F).map g) ≫ Spec.map ((perfectionFunctor F).map f) := by
  rw [_root_.CategoryTheory.Functor.map_comp, Spec.map_comp]

/-- The entire affine perfected functor retains every native direct-colimit map. -/
def affinePerfectFpFunctor : (FpAlgebras p)ᵒᵖ ⥤ FpSchemes p where
  obj A := affinePerfectFp F A.unop
  map {A B} f := Over.homMk (Spec.map ((perfectionFunctor F).map f.unop)) (affinePerfect_base_map F f.unop)
  map_id A := by
    apply (Over.forget (affine (CommRingCat.of (ZMod p)))).map_injective
    exact affinePerfect_map_id F A.unop
  map_comp f g := by
    apply (Over.forget (affine (CommRingCat.of (ZMod p)))).map_injective
    exact affinePerfect_map_comp F g.unop f.unop

/-- Coordinate perfectness is tested on all genuine affine open Fp charts. -/
def IsPerfectFpScheme (X : FpSchemes p) : Prop :=
  ∀ (A : FpAlgebras p) (j : affineFp A ⟶ X), IsOpenImmersion j.left →
    Function.Bijective (F.endomorphism.app A).hom

/-- Global perfection is fixed by the whole affine functor, native open squares and universal projection. -/
structure GlobalPerfectionSource where
  functor : FpSchemes p ⥤ FpSchemes p
  projection : functor ⟶ 𝟭 (FpSchemes p)
  affine_comparison : affineFpFunctor ⋙ functor ≅ affinePerfectFpFunctor F
  affine_projection : ∀ A : FpAlgebras p,
    (affine_comparison.app (op A)).hom ≫ affinePerfectionOver F A = projection.app (affineFp A)
  perfect : ∀ X : FpSchemes p, IsPerfectFpScheme F (functor.obj X)
  open_cartesian : ∀ {X Y : FpSchemes p} (j : Y ⟶ X), IsOpenImmersion j.left →
    IsPullback (functor.map j) (projection.app Y) (projection.app X) j
  universal : ∀ (X W : FpSchemes p), IsPerfectFpScheme F W →
    Function.Bijective (fun f : W ⟶ functor.obj X => f ≫ projection.app X)

end MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels
