/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesWorkingHeight
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicAlternatization

/-!
# Universe lifts of cyclic exterior maps

The Connes projection and `TensorPower.consEquiv` give representatives at a
common universe height. Full alternatization is integral; with `Algebra ℚ k`,
the normalized map uses the factor `1/(n+1)`. The signed variant retains
`(-1)^n`.

Naturality across independent carrier universes follows from the quotient
projection square and the tensor-power map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct BigOperators

universe u v w z

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- Carrier lift into the first-column tensor object. -/
def connesConsUpAtHeight (n : ℕ) : (A ⊗[k] TensorPower k n A) →ₗ[k]
    ((ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexAtHeight.{u,v,z} k A).X 0).X n :=
  { toFun := ULift.up
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The typed native lift still has the original prescribed point value. -/
theorem connesConsUpAtHeight_apply (n : ℕ) (x : A ⊗[k] TensorPower k n A) :
    connesConsUpAtHeight.{u,v,z} k A n x = ULift.up x := rfl

/-- Carrier lift into the lifted Connes term. -/
def connesTermUpAtHeight (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A).X n →ₗ[k]
      (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).X n :=
  (ULift.moduleEquiv :
    (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).X n ≃ₗ[k]
        (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A).X n).symm.toLinearMap

/-- The original whole tensor representative followed by the higher Connes quotient. -/
def connesTensorRepresentativeAtHeight (n : ℕ) :
    TensorPower k (n + 1) A →ₗ[k]
      (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  ((ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight.{u,v,z} k A n).hom).comp
    ((connesConsUpAtHeight.{u,v,z} k A n).comp (TensorPower.consEquiv k A n).symm.toLinearMap)

/-- The new representative is precisely the native lift image of the original Connes
representative. -/
theorem connesTensorRepresentativeAtHeight_image (n : ℕ) (x : TensorPower k (n + 1) A) :
    connesTensorRepresentativeAtHeight.{u,v,z} k A n x =
      ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom
        (connesTermUpAtHeight.{u,v,z} k A n
          (ModuleCat.Algebra.Hochschild.Matrix.connesTensorRepresentative k A n x)) := by
  let E := HomologicalComplex.eval (ModuleCat.{max u v z} k) (ComplexShape.down ℕ) n
  have hπ := E.congr_map
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight_π.{u,v,z} k A)
  simp only [E, Functor.map_comp, HomologicalComplex.eval_map, HomologicalComplex.eval_obj,
    HomologicalComplex.comp_f] at hπ
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hπ)
    (connesConsUpAtHeight.{u,v,z} k A n ((TensorPower.consEquiv k A n).symm x))
  change ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom
      (connesTermUpAtHeight.{u,v,z} k A n
        (ModuleCat.Algebra.Hochschild.Matrix.connesTensorRepresentative k A n x)) =
    connesTensorRepresentativeAtHeight.{u,v,z} k A n x at h
  exact h.symm

variable {B : Type w} [Ring B] [Algebra k B]

/-- Every original independent-universe coefficient map keeps the same tensor representative. -/
theorem connesTensorRepresentativeAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ)
    (x : TensorPower k (n + 1) A) :
    ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom
        (connesTensorRepresentativeAtHeight.{u,v,max u v w z} k A n x) =
      connesTensorRepresentativeAtHeight.{u,w,max u v w z} k B n
        (PiTensorProduct.map (fun _ : Fin (n + 1) => (f : A →ₗ[k] B)) x) := by
  let a := (TensorPower.consEquiv k A n).symm x
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight_naturality.{u,v,w,z} k A f n))
      (connesConsUpAtHeight.{u,v,max u v w z} k A n a)
  change ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom
      ((ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight.{u,v,max u v w z} k A n).hom
        (connesConsUpAtHeight.{u,v,max u v w z} k A n a)) =
    (ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight.{u,w,max u v w z} k B n).hom
      ((((ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexMapAtHeight.{u,v,w,z} f).f 0).f n).hom
        (connesConsUpAtHeight.{u,v,max u v w z} k A n a)) at h
  have hm : (((ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexMapAtHeight.{u,v,w,z} f).f 0).f n).hom
      (connesConsUpAtHeight.{u,v,max u v w z} k A n a) =
    connesConsUpAtHeight.{u,w,max u v w z} k B n (TensorPower.consLevelMap (f : A →ₗ[k] B) n a) :=
      by
        rw [connesConsUpAtHeight_apply, connesConsUpAtHeight_apply]
        exact ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexMapAtHeight_f_f_up.{u,v,w,z} f 0 n a
  rw [hm] at h
  have hc := LinearMap.congr_fun (TensorPower.consEquiv_naturality (f : A →ₗ[k] B) n) a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
  dsimp only [a] at hc
  rw [LinearEquiv.apply_symm_apply] at hc
  have hc' := congrArg (TensorPower.consEquiv k B n).symm hc
  simp only [LinearEquiv.symm_apply_apply] at hc'
  let qB := ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight.{u,w,max u v w z} k B n
  exact h.trans (congrArg
    (fun y => qB.hom (connesConsUpAtHeight.{u,w,max u v w z} k B n y)) hc')

/-- Native integral full alternatization in the common-height Connes object. -/
def cyclicFullAlternatingAtHeight (n : ℕ) :
    A [⋀^Fin (n + 1)]→ₗ[k]
      (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  ((connesTensorRepresentativeAtHeight.{u,v,z} k A n).compMultilinearMap
    (PiTensorProduct.tprod k)).alternatization

/-- The integral exterior map at the prescribed native working height. -/
def cyclicFullExteriorAtHeight (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k]
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  exteriorPower.alternatingMapLinearEquiv (cyclicFullAlternatingAtHeight.{u,v,z} k A n)

/-- The full-permutation formula retains all original ordered tensor terms and signs. -/
theorem cyclicFullExteriorAtHeight_pure (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicFullExteriorAtHeight.{u,v,z} k A n (exteriorPower.ιMulti k (n + 1) a) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), σ.sign • connesTensorRepresentativeAtHeight.{u,v,z} k A n
        (PiTensorProduct.tprod k (a ∘ σ)) := by
  rw [cyclicFullExteriorAtHeight, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    cyclicFullAlternatingAtHeight, MultilinearMap.alternatization_apply]
  rfl

/-- Full alternatization at the working height is the native lift of the original integral
exterior map. -/
theorem cyclicFullExteriorAtHeight_image (n : ℕ) :
    cyclicFullExteriorAtHeight.{u,v,z} k A n =
      (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom).comp
        ((connesTermUpAtHeight.{u,v,z} k A n).comp (cyclicFullExterior k A n)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change cyclicFullExteriorAtHeight.{u,v,z} k A n (exteriorPower.ιMulti k (n + 1) a) =
    ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom
      (connesTermUpAtHeight.{u,v,z} k A n (cyclicFullExterior k A n (exteriorPower.ιMulti k (n + 1) a)))
  rw [cyclicFullExteriorAtHeight_pure, cyclicFullExterior_pure, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul_unit, map_zsmul_unit]
  exact congrArg (fun y => σ.sign • y)
    (connesTensorRepresentativeAtHeight_image.{u,v,z} k A n (PiTensorProduct.tprod k (a ∘ σ)))

/-- Integral full alternatization keeps the independent-universe coefficient square. -/
theorem cyclicFullExteriorAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom).comp
        (cyclicFullExteriorAtHeight.{u,v,max u v w z} k A n) =
      (cyclicFullExteriorAtHeight.{u,w,max u v w z} k B n).comp
        (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom
      (cyclicFullExteriorAtHeight.{u,v,max u v w z} k A n (exteriorPower.ιMulti k (n + 1) a)) =
    cyclicFullExteriorAtHeight.{u,w,max u v w z} k B n
      (exteriorPower.map (n + 1) (f : A →ₗ[k] B) (exteriorPower.ιMulti k (n + 1) a))
  rw [exteriorPower.map_apply_ιMulti, cyclicFullExteriorAtHeight_pure, cyclicFullExteriorAtHeight_pure, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul_unit]
  have h := connesTensorRepresentativeAtHeight_naturality.{u,v,w,z} k A f n
    (PiTensorProduct.tprod k (a ∘ σ))
  simp only [PiTensorProduct.map_tprod] at h
  exact congrArg (fun y => σ.sign • y) h

section Rational

variable [Algebra ℚ k]

/-- The rational exterior map uses only the original factor 1/(n+1). -/
def cyclicExteriorAtHeight (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k]
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  algebraMap ℚ k ((n + 1 : ℚ)⁻¹) • cyclicFullExteriorAtHeight.{u,v,z} k A n

/-- The normalized higher exterior map is exactly the native lift of the original prescribed map. -/
theorem cyclicExteriorAtHeight_image (n : ℕ) :
    cyclicExteriorAtHeight.{u,v,z} k A n =
      (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom).comp
        ((connesTermUpAtHeight.{u,v,z} k A n).comp (cyclicExterior k A n)) := by
  rw [cyclicExteriorAtHeight, cyclicExterior, cyclicFullExteriorAtHeight_image,
    LinearMap.comp_smul, LinearMap.comp_smul]

/-- The original rational normalization leaves independent-universe coefficient naturality
intact. -/
theorem cyclicExteriorAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom).comp
        (cyclicExteriorAtHeight.{u,v,max u v w z} k A n) =
      (cyclicExteriorAtHeight.{u,w,max u v w z} k B n).comp
        (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  rw [cyclicExteriorAtHeight, cyclicExteriorAtHeight, LinearMap.comp_smul, LinearMap.smul_comp,
    cyclicFullExteriorAtHeight_naturality]

/-- The signed exterior map at a common height has degree factor `(-1)^n`. -/
def cyclicExteriorWeibelAtHeight (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k]
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  (-1 : k) ^ n • cyclicExteriorAtHeight.{u,v,z} k A n

/-- The lift preserves the signed cyclic exterior map, including `(-1)^n`. -/
theorem cyclicExteriorWeibelAtHeight_image (n : ℕ) :
    cyclicExteriorWeibelAtHeight.{u,v,z} k A n =
      (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom).comp
        ((connesTermUpAtHeight.{u,v,z} k A n).comp (cyclicExteriorWeibel k A n)) := by
  rw [cyclicExteriorWeibelAtHeight, cyclicExteriorWeibel, cyclicExteriorAtHeight_image,
    LinearMap.comp_smul, LinearMap.comp_smul]

/-- The degree factor preserves the coefficient square across independent universes. -/
theorem cyclicExteriorWeibelAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom).comp
        (cyclicExteriorWeibelAtHeight.{u,v,max u v w z} k A n) =
      (cyclicExteriorWeibelAtHeight.{u,w,max u v w z} k B n).comp
        (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  rw [cyclicExteriorWeibelAtHeight, cyclicExteriorWeibelAtHeight, LinearMap.comp_smul, LinearMap.smul_comp,
    cyclicExteriorAtHeight_naturality]

end Rational
end ChevalleyEilenberg
