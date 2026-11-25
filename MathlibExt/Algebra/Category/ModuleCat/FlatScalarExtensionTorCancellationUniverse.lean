/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionResolutionUniverse
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseCompatibility

/-!
# Scalar tensor cancellation for Tor

The coefficient may be an arbitrary module over the extended ring.
Scalar tensor cancellation identifies the tensor complexes. A flat map
sends a projective resolution to a projective resolution, and exact scalar
restriction identifies homology. This gives flat base change for graph
intersections.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w

open scoped ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]

/-- Canonical scalar tensor cancellation for a coefficient module defined
only over the extended ring. -/
def scalarTensorCancellationIso (f : R →+* S)
    (N : ModuleCat.{max u v w} S) (X : ModuleCat.{max u v w} R) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,max v w} (R := R)
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.tensorStructure.{v,max u w} (R := S)
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
    (restrictScalars.{max u v w,u,v} f).obj (N ⊗ (extendScalars.{u,v,max u v w} f).obj X) ≅
      (restrictScalars.{max u v w,u,v} f).obj N ⊗ X := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,max v w} (R := R)
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.tensorStructure.{v,max u w} (R := S)
  letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
  letI : Algebra R S := f.toAlgebra
  letI : Module R N := Module.compHom N f
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N X).restrictScalars R).toModuleIso

/-- The actual coefficient cancellation is natural in the original
module, hence commutes with every original resolution differential. -/
def scalarTensorCancellationNatIso (f : R →+* S) (N : ModuleCat.{max u v w} S) :
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
    extendScalars.{u,v,max u v w} f ⋙ (tensoringLeft (ModuleCat.{max u v w} S)).obj N ⋙
      restrictScalars.{max u v w,u,v} f ≅
      (tensoringLeft (ModuleCat.{max u v w} R)).obj ((restrictScalars.{max u v w,u,v} f).obj N) := by
  letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
  exact NatIso.ofComponents (fun X => scalarTensorCancellationIso R S f N X) (by
    intro X Y g
    let : Algebra R S := f.toAlgebra
    let : Module R N := Module.compHom N f
    let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have h := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
      R S S (M := N) g.hom
    exact congrArg (fun k : (N ⊗[S] (S ⊗[R] X)) →ₗ[S] (N ⊗[R] Y) => k z) h.symm)


/-- Flat base change for original Tor with arbitrary coefficients over
S, expressed in the original base-ring module category. -/
def flatScalarExtensionTorCancellationIso [Algebra R S] [Module.Flat R S]
    (N : ModuleCat.{max u v w} S) (X : ModuleCat.{max u v w} R) (q : ℕ) :
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,max v w} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{v,max u w} (R := S)
    (restrictScalars.{max u v w,u,v} (algebraMap R S)).obj
      (((Tor (ModuleCat.{max u v w} S) q).obj N).obj
        ((extendScalars.{u,v,max u v w} (algebraMap R S)).obj X)) ≅
      ((Tor (ModuleCat.{max u v w} R) q).obj
        ((restrictScalars.{max u v w,u,v} (algebraMap R S)).obj N)).obj X := by
  letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,max v w} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{v,max u w} (R := S)
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u,v,max u v w} (algebraMap R S)
  let G : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} R :=
    restrictScalars.{max u v w,u,v} (algebraMap R S)
  letI : F.PreservesHomology := ModuleCat.preservesHomology_extendScalars_of_flat.{u,v,w} (algebraMap R S) (by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance)
  let P := projectiveResolution X
  let Q := flatScalarExtensionProjectiveResolution R S P
  let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj (G.obj N)
  let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj N
  let K := (L'.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  exact G.mapIso (Q.isoLeftDerivedObj L' q) ≪≫
    ((K.sc q).mapHomologyIso G).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R)
        (ComplexShape.down ℕ) q).mapIso
          ((NatIso.mapHomologicalComplex
            (scalarTensorCancellationNatIso R S (algebraMap R S) N)
              (ComplexShape.down ℕ)).app P.complex) ≪≫
                (P.isoLeftDerivedObj L q).symm

end ModuleCat.UniverseTensor
