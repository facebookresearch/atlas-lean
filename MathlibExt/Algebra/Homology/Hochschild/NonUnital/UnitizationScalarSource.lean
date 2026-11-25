/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationHochschild

/-!
# The original scalar source of the unitization cokernel

The scalar complex used in the common carrier world is canonically the
native module-functor lift of the original regular Hochschild complex of k.
The equivalence lifts each coefficient and tensor factor. Thus the
source cokernel really compares the original scalar inclusion; the scalar
carrier change is and visible.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Every original scalar coefficient and tail factor is lifted through its native module equivalence. -/
def scalarRegularLevelLiftEquiv (n : ℕ) :
    (ModuleCat.uliftFunctor.{v, u} k).obj (chainLevel k k k n) ≃ₗ[k]
      chainLevel k (ULift.{v} k) (ULift.{v} k) n :=
  ULift.moduleEquiv ≪≫ₗ TensorProduct.congr
    (ULift.moduleEquiv (R := k) (M := k)).symm
    (PiTensorProduct.congr (fun _ : Fin n => (ULift.moduleEquiv (R := k) (M := k)).symm))

/-- The scalar carrier bridge is on the original Hochschild complexes, using native map naturality. -/
def scalarRegularLiftIso :
    ((ModuleCat.uliftFunctor.{v, u} k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (bComplex k k) ≅ bComplex k (ULift.{v} k) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (scalarRegularLevelLiftEquiv.{u, v} k n).toModuleIso)
    (fun i j hij => by
      have h : j + 1 = i := hij
      subst i
      apply ModuleCat.hom_ext
      ext x
      change ((bComplex k (ULift.{v} k)).d (j + 1) j).hom
          (TensorPower.consLevelMap (ULift.moduleEquiv (R := k) (M := k)).symm.toLinearMap
            (j + 1) x.down) =
        TensorPower.consLevelMap (ULift.moduleEquiv (R := k) (M := k)).symm.toLinearMap j
          (((bComplex k k).d (j + 1) j).hom x.down)
      exact (DFunLike.congr_fun (bComplex_d_natural
        (ULift.algEquiv (R := k) (A := k)).symm.toAlgHom.toNonUnitalAlgHom j) x.down).symm)

/-- The original ground scalar complex maps by precisely its native unitization scalar inclusion. -/
def unitizationOriginalScalarComplexInclusion :
    ((ModuleCat.uliftFunctor.{v, u} k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (bComplex k k) ⟶ bComplex k (Unitization k A) :=
  (scalarRegularLiftIso.{u, v} k).hom ≫ unitizationScalarComplexInclusion k A

/-- This inclusion retains the original scalar coefficient and each scalar tensor factor. -/
theorem unitizationOriginalScalarComplexInclusion_tprod (n : ℕ) (m : k) (a : Fin n → k) :
    ((unitizationOriginalScalarComplexInclusion k A).f n).hom
        (ULift.up (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      Unitization.inl m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => Unitization.inl (a i)) := by
  change TensorPower.consLevelMap (unitizationGroundScalarSection k A).toLinearMap n
    (TensorPower.consLevelMap (ULift.moduleEquiv (R := k) (M := k)).symm.toLinearMap n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  simp only [TensorPower.consLevelMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  rfl

/-- The literal cokernel of the original scalar HH map agrees with the explicit common-carrier presentation. -/
def unitizationOriginalScalarCokernelIso (n : ℕ) :
    cokernel (HomologicalComplex.homologyMap (unitizationOriginalScalarComplexInclusion k A) n) ≅
      unitizationHochschildHomology k A n :=
  (cokernelIsoOfEq (HomologicalComplex.homologyMap_comp (scalarRegularLiftIso.{u, v} k).hom
    (unitizationScalarComplexInclusion k A) n)) ≪≫
    cokernelEpiComp (HomologicalComplex.homologyMap (scalarRegularLiftIso.{u, v} k).hom n)
      (HomologicalComplex.homologyMap (unitizationScalarComplexInclusion k A) n)

end ModuleCat.Algebra.Hochschild.NonUnital
