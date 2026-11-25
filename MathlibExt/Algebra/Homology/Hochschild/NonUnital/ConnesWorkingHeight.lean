/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.CyclicWorkingHeight
public import MathlibExt.Algebra.Homology.HomologicalComplex.MapColimits

/-!
# Connes quotient maps at a common carrier height

The Connes model is the first-column cokernel of
the lifted cyclic bicomplex. Cokernel functoriality
gives its coefficient maps and the comparison
with the lift of the original Connes complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The cyclic bicomplex carried through the native full working-height module lift. -/
abbrev cyclicBicomplexAtHeight :=
  (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)

/-- The original first-column cokernel at the chosen module height. -/
abbrev connesComplexAtHeight :=
  HomologicalComplex₂.firstColumnCokernel (cyclicBicomplexAtHeight.{u,v,z} k A)

/-- Native cokernel preservation identifies the lifted Connes quotient model. -/
def connesComplexLiftIsoAtHeight :
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (connesComplex k A) ≅ connesComplexAtHeight.{u,v,z} k A :=
  PreservesCokernel.iso
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ))
    ((cyclicBicomplex k A).d 1 0)

/-- The lifted quotient comparison preserves the original cokernel projection. -/
@[reassoc]
theorem connesComplexLiftIsoAtHeight_π :
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (cokernel.π ((cyclicBicomplex k A).d 1 0)) ≫
      (connesComplexLiftIsoAtHeight.{u,v,z} k A).hom =
        cokernel.π ((cyclicBicomplexAtHeight.{u,v,z} k A).d 1 0) :=
  PreservesCokernel.π_iso_hom
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ))
    ((cyclicBicomplex k A).d 1 0)

/-- The original cokernel projection, evaluated in its native degree. -/
def connesProjectionAtHeight (n : ℕ) :=
  (cokernel.π ((cyclicBicomplexAtHeight.{u,v,z} k A).d 1 0)).f n

variable {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Original independent-world cyclic coefficient maps induce their native Connes cokernel maps. -/
def connesComplexHomAtHeight (f : A →ₙₐ[k] B) :
    connesComplexAtHeight.{u,v,max u v w z} k A ⟶
      connesComplexAtHeight.{u,w,max u v w z} k B :=
  let φ : cyclicBicomplexAtHeight.{u,v,max u v w z} k A ⟶
      cyclicBicomplexAtHeight.{u,w,max u v w z} k B := cyclicBicomplexMapAtHeight.{u,v,w,z} f
  HomologicalComplex₂.firstColumnCokernelMap φ

/-- The full-height coefficient quotient retains the original first-column projection square. -/
@[reassoc]
theorem connesProjectionAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    connesProjectionAtHeight.{u,v,max u v w z} k A n ≫
        (connesComplexHomAtHeight.{u,v,w,z} k A f).f n =
      ((cyclicBicomplexMapAtHeight.{u,v,w,z} f).f 0).f n ≫
        connesProjectionAtHeight.{u,w,max u v w z} k B n := by
  let φ : cyclicBicomplexAtHeight.{u,v,max u v w z} k A ⟶
      cyclicBicomplexAtHeight.{u,w,max u v w z} k B := cyclicBicomplexMapAtHeight.{u,v,w,z} f
  let E := HomologicalComplex.eval (ModuleCat.{max u v w z} k) (ComplexShape.down ℕ) n
  have h := E.congr_map (HomologicalComplex₂.firstColumnCokernelMap_π φ)
  simpa only [E, φ, Functor.map_comp, HomologicalComplex.eval_map, HomologicalComplex.eval_obj,
    HomologicalComplex.comp_f, connesComplexHomAtHeight, connesProjectionAtHeight,
    connesComplexAtHeight, cyclicBicomplexAtHeight] using h

/-- Native homology of the full-height Connes quotient. -/
abbrev connesHomologyAtHeight (n : ℕ) := (connesComplexAtHeight.{u,v,z} k A).homology n

/-- Actual independent-world coefficient maps on the native working-height Connes homology. -/
def connesHomologyMapAtHeight (f : A →ₙₐ[k] B) (n : ℕ) :
    connesHomologyAtHeight.{u,v,max u v w z} k A n ⟶
      connesHomologyAtHeight.{u,w,max u v w z} k B n :=
  HomologicalComplex.homologyMap (connesComplexHomAtHeight.{u,v,w,z} k A f) n

end ModuleCat.Algebra.Hochschild.NonUnital
