/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationHochschild

/-!
# The lifted scalar source of unitization Hochschild cokernels

Let `k : Type u` be a commutative ring and let `A : Type v` be a nonunital ground algebra.
Lifting the regular Hochschild complex of `k` by the module functor `ULift.{v}` gives a chain
complex isomorphic to the regular Hochschild complex of the lifted scalar algebra `ULift.{v}
k`.

The component equivalence lifts the scalar coefficient and every tail factor. Composing it
with the scalar section into `A⁺` gives the scalar chain inclusion in the common carrier
universe. Its homology cokernel is isomorphic to the unitization Hochschild cokernel defined
using the lifted scalar algebra.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The tensor-level comparison for a lifted scalar Hochschild complex.

The module-functor lift of a scalar degree-`n` tensor level is linearly equivalent to the
tensor level with coefficient and all tail factors in `ULift.{v} k`. -/
def scalarRegularLevelLiftEquiv (n : ℕ) :
    (ModuleCat.uliftFunctor.{v, u} k).obj (chainLevel k k k n) ≃ₗ[k]
      chainLevel k (ULift.{v} k) (ULift.{v} k) n :=
  ULift.moduleEquiv ≪≫ₗ TensorProduct.congr
    (ULift.moduleEquiv (R := k) (M := k)).symm
    (PiTensorProduct.congr (fun _ : Fin n => (ULift.moduleEquiv (R := k) (M := k)).symm))

/-- The scalar Hochschild chain comparison under a carrier lift.

The lifted regular `b`-complex of `k` is chain-isomorphic to the regular `b`-complex of
`ULift.{v} k`, by lifting each coefficient and tail value. -/
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

/-- The unitization inclusion from a lifted scalar Hochschild complex.

The scalar lift comparison followed by the lifted scalar section gives a chain map from the
module-functor lift of `b(k)` into `b(A⁺)`. -/
def unitizationOriginalScalarComplexInclusion :
    ((ModuleCat.uliftFunctor.{v, u} k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (bComplex k k) ⟶ bComplex k (Unitization k A) :=
  (scalarRegularLiftIso.{u, v} k).hom ≫ unitizationScalarComplexInclusion k A

/-- The scalar tensor formula for the lifted unitization inclusion.

The inclusion sends `up(m ⊗ ⊗ᵢ aᵢ)` to `inl(m) ⊗ ⊗ᵢ inl(aᵢ)`, applying the scalar section to
every entry. -/
theorem unitizationOriginalScalarComplexInclusion_tprod (n : ℕ) (m : k) (a : Fin n → k) :
    ((unitizationOriginalScalarComplexInclusion k A).f n).hom
        (ULift.up (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      Unitization.inl m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => Unitization.inl (a i)) := by
  change TensorPower.consLevelMap (unitizationGroundScalarSection k A).toLinearMap n
    (TensorPower.consLevelMap (ULift.moduleEquiv (R := k) (M := k)).symm.toLinearMap n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  simp only [TensorPower.consLevelMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  rfl

/-- The scalar-source comparison of unitization homology cokernels.

The cokernel of the homology map from the functor-lifted scalar complex is isomorphic to the
unitization Hochschild model defined using `b(ULift.{v} k)`. -/
def unitizationOriginalScalarCokernelIso (n : ℕ) :
    cokernel (HomologicalComplex.homologyMap (unitizationOriginalScalarComplexInclusion k A) n) ≅
      unitizationHochschildHomology k A n :=
  (cokernelIsoOfEq (HomologicalComplex.homologyMap_comp (scalarRegularLiftIso.{u, v} k).hom
    (unitizationScalarComplexInclusion k A) n)) ≪≫
    cokernelEpiComp (HomologicalComplex.homologyMap (scalarRegularLiftIso.{u, v} k).hom n)
      (HomologicalComplex.homologyMap (unitizationScalarComplexInclusion k A) n)

end ModuleCat.Algebra.Hochschild.NonUnital
