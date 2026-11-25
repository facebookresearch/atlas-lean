/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.UliftComposition
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic

/-!
# Cyclic coefficient maps at a common height

Lifted cyclic bicomplex maps have the tensor
coefficient values, composed with the natural
flattening of repeated module lifts. Totalization
then gives the cyclic homology map at the
specified common carrier height.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Native further lifting of the original independent-universe cyclic coefficient bicomplex map. -/
def cyclicBicomplexMapAtHeight (f : A →ₙₐ[k] B) :
    (((ModuleCat.uliftFunctor.{max u v w z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicBicomplex k A) ⟶
    (((ModuleCat.uliftFunctor.{max u v w z, max u w} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicBicomplex k B) := by
  let U := ModuleCat.uliftFunctor.{max u v w z, max u v w} k
  let eA := ModuleCat.uliftFunctorCompIso.{w,max u v w z,max u v,u} k
  let eB := ModuleCat.uliftFunctorCompIso.{v,max u v w z,max u w,u} k
  let eA₁ := Functor.mapHomologicalComplexCompIso eA (ComplexShape.down ℕ)
  let eB₁ := Functor.mapHomologicalComplexCompIso eB (ComplexShape.down ℕ)
  let eA₂ := Functor.mapHomologicalComplexCompIso eA₁ (ComplexShape.down ℕ)
  let eB₂ := Functor.mapHomologicalComplexCompIso eB₁ (ComplexShape.down ℕ)
  exact eA₂.inv.app (cyclicBicomplex k A) ≫
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (cyclicBicomplexMap f) ≫ eB₂.hom.app (cyclicBicomplex k B)

/-- The common-height coefficient map keeps precisely the original tensor-cell value. -/
theorem cyclicBicomplexMapAtHeight_f_f_up (f : A →ₙₐ[k] B) (p q : ℕ)
    (x : chainLevel k A A q) :
    (((cyclicBicomplexMapAtHeight.{u,v,w,z} f).f p).f q).hom (ULift.up x) =
      ULift.up (TensorPower.consLevelMap (f : A →ₗ[k] B) q x) := by
  change ULift.up (((((cyclicBicomplexMap f).f p).f q).hom (ULift.up x)).down) =
    ULift.up (TensorPower.consLevelMap (f : A →ₗ[k] B) q x)
  have h := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (cyclicBicomplexMap_f_f f p q)) (ULift.up x)
  have hv := h.trans (levelMapLift_apply (f : A →ₗ[k] B) q (ULift.up x))
  exact congrArg ULift.up (congrArg ULift.down hv)

/-- Native totalization of the common-height cyclic coefficient bicomplex map. -/
def cyclicTotalMapAtHeight (f : A →ₙₐ[k] B) :=
  HomologicalComplex₂.total.map (cyclicBicomplexMapAtHeight.{u,v,w,z} f) (ComplexShape.down ℕ)

/-- Actual HC coefficient maps across both original worlds and the independent further height. -/
def cyclicHomologyMapAtHeight (f : A →ₙₐ[k] B) (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v w z, max u v} k).obj (cyclicHomology k A n) ⟶
      (ModuleCat.uliftFunctor.{max u v w z, max u w} k).obj (cyclicHomology k B n) :=
  (cyclicHomologyLiftIso.{max u v w z} k A n).hom ≫
    HomologicalComplex.homologyMap (cyclicTotalMapAtHeight.{u,v,w,z} f) n ≫
      (cyclicHomologyLiftIso.{max u v w z} k B n).inv

/-- The common-world total map characterizes the prescribed HC coefficient map. -/
theorem cyclicHomologyMapAtHeight_lift (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMapAtHeight.{u,v,w,z} f n ≫ (cyclicHomologyLiftIso.{max u v w z} k B n).hom =
      (cyclicHomologyLiftIso.{max u v w z} k A n).hom ≫
        HomologicalComplex.homologyMap (cyclicTotalMapAtHeight.{u,v,w,z} f) n := by
  let eA := cyclicHomologyLiftIso.{max u v w z} k A n
  let eB := cyclicHomologyLiftIso.{max u v w z} k B n
  let m := HomologicalComplex.homologyMap (cyclicTotalMapAtHeight.{u,v,w,z} f) n
  have h : (m ≫ eB.inv) ≫ eB.hom = m :=
    (Category.assoc m eB.inv eB.hom).trans
      ((congrArg (fun q => m ≫ q) eB.inv_hom_id).trans (Category.comp_id m))
  exact (Category.assoc eA.hom (m ≫ eB.inv) eB.hom).trans (congrArg (fun q => eA.hom ≫ q) h)

end ModuleCat.Algebra.Hochschild.NonUnital
