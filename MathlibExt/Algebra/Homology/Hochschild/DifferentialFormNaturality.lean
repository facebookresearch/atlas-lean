/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjection
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEnvelopingBarComparison

/-!
# coefficient naturality of the differential-form projection

Algebra-linear coefficient maps act on the original coefficient head and
leave every original tensor or differential tail unchanged. The projection
square is proved on the tensor representatives, across independent
coefficient worlds. In a common carrier category these maps form the native
chain and homology naturality squares.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w w'

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module A N]
  [SMulCommClass k A M] [SMulCommClass k A N]
  [IsScalarTower k A M] [IsScalarTower k A N]

local notation "Ω" => KaehlerDifferential k A

/-- Original algebra-linear coefficient maps preserve the form projection,
without identifying the independent source and target carrier worlds. -/
theorem coefficientFormProjection_coefficient (f : M →ₗ[A] N) (n : ℕ) :
    ((TensorProduct.map f (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k).comp
        (coefficientFormProjection k A M n) =
      (coefficientFormProjection k A N n).comp
        (TensorProduct.map (f.restrictScalars k) (LinearMap.id : TensorPower k n A →ₗ[k] TensorPower k n A)) := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, coefficientFormProjection_tprod]

section CommonWorld

variable {P : Type w} [AddCommGroup P] [Module k P] [Module A P]
  [SMulCommClass k A P] [IsScalarTower k A P]

/-- The coefficient-head map on the original zero-differential form complex. -/
def coefficientDifferentialFormComplexMap (f : M →ₗ[A] P) :
    coefficientDifferentialFormComplex k A M ⟶ coefficientDifferentialFormComplex k A P where
  f n := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{u} (P ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
      P ⊗[A] (⋀[A]^n Ω)).symm.toLinearMap.comp
        (((TensorProduct.map f (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k).comp
          (ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
            M ⊗[A] (⋀[A]^n Ω)).toLinearMap))
  comm' i j _h := by
    rw [coefficientDifferentialFormComplex_d_eq_zero,
      coefficientDifferentialFormComplex_d_eq_zero]
    erw [CategoryTheory.Limits.comp_zero]

/-- Every original form component retains the exact coefficient-head map. -/
theorem coefficientDifferentialFormComplexMap_f (f : M →ₗ[A] P) (n : ℕ) :
    ((coefficientDifferentialFormComplexMap k A f).f n).hom =
      (ULift.moduleEquiv : ULift.{u} (P ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
        P ⊗[A] (⋀[A]^n Ω)).symm.toLinearMap.comp
          (((TensorProduct.map f (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k).comp
            (ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
              M ⊗[A] (⋀[A]^n Ω)).toLinearMap) := rfl

/-- The original Hochschild coefficient chain map has the native tensor coefficient component. -/
theorem symmetricOriginalCoefficientChainMap_tensor (f : M →ₗ[A] P) (n : ℕ) :
    ((symmetricOriginalCoefficientChainMap k A M f).f n).hom =
      TensorProduct.map (f.restrictScalars k)
        (LinearMap.id : TensorPower k n A →ₗ[k] TensorPower k n A) := by
  rw [symmetricOriginalCoefficientChainMap_f]
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.restrictScalars_apply, algebraCoefficientLevelMap_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- The coefficient chain maps preserve the original form projection. -/
@[reassoc]
theorem coefficientDifferentialFormChainMap_coefficient (f : M →ₗ[A] P) :
    symmetricOriginalCoefficientChainMap k A M f ≫ coefficientDifferentialFormChainMap k A P =
      coefficientDifferentialFormChainMap k A M ≫ coefficientDifferentialFormComplexMap k A f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  let word := m ⊗ₜ[k] PiTensorProduct.tprod k a
  have hhead : ((symmetricOriginalCoefficientChainMap k A M f).f n).hom word =
      f m ⊗ₜ[k] PiTensorProduct.tprod k a := by
    exact (LinearMap.congr_fun (symmetricOriginalCoefficientChainMap_tensor k A f n) word).trans
      ((TensorProduct.map_tmul (f.restrictScalars k)
        (LinearMap.id : TensorPower k n A →ₗ[k] TensorPower k n A) m
          (PiTensorProduct.tprod k a)).trans (by rfl))
  have hleft := (LinearMap.comp_apply
    ((coefficientDifferentialFormChainMap k A P).f n).hom
    ((symmetricOriginalCoefficientChainMap k A M f).f n).hom word).trans
      ((congrArg ((coefficientDifferentialFormChainMap k A P).f n).hom hhead).trans
        (coefficientDifferentialFormChainMap_tprod k A P n (f m) a))
  let raw : M ⊗[A] (⋀[A]^n Ω) →ₗ[k] P ⊗[A] (⋀[A]^n Ω) :=
    (TensorProduct.map f (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k
  have hup (x : M ⊗[A] (⋀[A]^n Ω)) :
      ((coefficientDifferentialFormComplexMap k A f).f n).hom (ULift.up x) =
        ULift.up (raw x) := rfl
  have hraw : raw (m ⊗ₜ[A] exteriorPower.ιMulti A n
      (fun j => KaehlerDifferential.D k A (a j))) =
        f m ⊗ₜ[A] exteriorPower.ιMulti A n
          (fun j => KaehlerDifferential.D k A (a j)) := by
    simp only [raw, LinearMap.restrictScalars_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  have hright := (LinearMap.comp_apply
    ((coefficientDifferentialFormComplexMap k A f).f n).hom
    ((coefficientDifferentialFormChainMap k A M).f n).hom word).trans
      ((congrArg ((coefficientDifferentialFormComplexMap k A f).f n).hom
        (coefficientDifferentialFormChainMap_tprod k A M n m a)).trans
          ((hup _).trans (congrArg ULift.up hraw)))
  exact hleft.trans hright.symm

/-- The original coefficient morphism on the degree form object. -/
def coefficientDifferentialFormObjectMap (f : M →ₗ[A] P) (n : ℕ) :
    ModuleCat.of k (ULift.{u} (M ⊗[A] (⋀[A]^n Ω))) ⟶
      ModuleCat.of k (ULift.{u} (P ⊗[A] (⋀[A]^n Ω))) :=
  (coefficientDifferentialFormComplexMap k A f).f n

/-- The original homology naturality square follows from the chain square
and native zero-differential homology coordinates. -/
@[reassoc]
theorem coefficientDifferentialFormHomologyMap_coefficient (f : M →ₗ[A] P) (n : ℕ) :
    HomologicalComplex.homologyMap (symmetricOriginalCoefficientChainMap k A M f) n ≫
        coefficientDifferentialFormHomologyMap k A P n =
      coefficientDifferentialFormHomologyMap k A M n ≫ coefficientDifferentialFormObjectMap k A f n := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (coefficientDifferentialFormChainMap_coefficient k A f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have hnat := HomologicalComplex.zeroDifferentialHomologyIso_naturality
    (coefficientDifferentialFormComplexMap k A f) n
    (coefficientDifferentialFormComplex_d_eq_zero k A M)
    (coefficientDifferentialFormComplex_d_eq_zero k A P)
  unfold coefficientDifferentialFormHomologyMap coefficientDifferentialFormObjectMap
  let a := HomologicalComplex.homologyMap (symmetricOriginalCoefficientChainMap k A M f) n
  let b := HomologicalComplex.homologyMap (coefficientDifferentialFormChainMap k A P) n
  let c := HomologicalComplex.homologyMap (coefficientDifferentialFormChainMap k A M) n
  let d := HomologicalComplex.homologyMap (coefficientDifferentialFormComplexMap k A f) n
  let qM := (HomologicalComplex.zeroDifferentialHomologyIso (coefficientDifferentialFormComplex k A M) n
    (coefficientDifferentialFormComplex_d_eq_zero k A M)).hom
  let qP := (HomologicalComplex.zeroDifferentialHomologyIso (coefficientDifferentialFormComplex k A P) n
    (coefficientDifferentialFormComplex_d_eq_zero k A P)).hom
  let F := (coefficientDifferentialFormComplexMap k A f).f n
  exact (Category.assoc a b qP).symm.trans
    ((congrArg (fun g : (chainComplex k A M).homology n ⟶
      (coefficientDifferentialFormComplex k A P).homology n => g ≫ qP) h).trans
        ((Category.assoc c d qP).trans
          ((congrArg (fun g : (coefficientDifferentialFormComplex k A M).homology n ⟶
            (coefficientDifferentialFormComplex k A P).X n => c ≫ g) hnat).trans
              (Category.assoc c qM F).symm)))

end CommonWorld

end ModuleCat.Algebra.Hochschild.Symmetric
