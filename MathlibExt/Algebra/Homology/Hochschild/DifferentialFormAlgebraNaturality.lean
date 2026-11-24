/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormNaturality
public import MathlibExt.Algebra.Homology.Hochschild.Maps
public import MathlibExt.LinearAlgebra.ExteriorPower.Semilinear

/-!
# Algebra naturality of the differential-form projection

An algebra map and a compatible ground-linear coefficient map induce
semilinear maps on coefficient forms. These maps preserve universal
differentials and exterior powers and commute with the unscaled
Hochschild form projection.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe uk uA uB uM uN

namespace ModuleCat.Algebra.Hochschild.Symmetric

section Raw

variable {k : Type uk} [CommRing k]
  {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [SMulCommClass k A M] [SMulCommClass k B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- The native universal differential map along the specified algebra
homomorphism, retaining its target scalar action. -/
def kaehlerAlgebraMap (g : A →ₐ[k] B) :
    KaehlerDifferential k A →ₛₗ[g.toRingHom] KaehlerDifferential k B := by
  letI : Algebra A B := g.toRingHom.toAlgebra
  letI : IsScalarTower k A B := inferInstance
  let F := KaehlerDifferential.map k k A B
  exact
    { toFun := F
      map_add' := F.map_add
      map_smul' := F.map_smul }

/-- Actual algebra images are differentiated by the native map. -/
theorem kaehlerAlgebraMap_D (g : A →ₐ[k] B) (a : A) :
    kaehlerAlgebraMap g (KaehlerDifferential.D k A a) =
      KaehlerDifferential.D k B (g a) := by
  let _ : Algebra A B := g.toRingHom.toAlgebra
  let _ : IsScalarTower k A B := inferInstance
  exact KaehlerDifferential.map_D k k A B a

/-- The original coefficient map with its semilinear algebra action. -/
def algebraCoefficientSemilinearMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) : M →ₛₗ[g.toRingHom] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := hf

/-- The scalar-changing tensor map on coefficient differential forms. -/
def coefficientFormAlgebraSemilinearMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    M ⊗[A] (⋀[A]^n (KaehlerDifferential k A)) →ₛₗ[g.toRingHom]
      N ⊗[B] (⋀[B]^n (KaehlerDifferential k B)) :=
  TensorProduct.map (algebraCoefficientSemilinearMap g f hf)
    (exteriorPower.mapSemilinear g.toRingHom (kaehlerAlgebraMap g) n)

/-- The same map is ground-linear, by the original algebra scalar law. -/
def coefficientFormAlgebraLinearMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    M ⊗[A] (⋀[A]^n (KaehlerDifferential k A)) →ₗ[k]
      N ⊗[B] (⋀[B]^n (KaehlerDifferential k B)) where
  toFun := coefficientFormAlgebraSemilinearMap g f hf n
  map_add' := map_add _
  map_smul' c x := by
    rw [← IsScalarTower.algebraMap_smul A c x, map_smulₛₗ]
    have hgc : g.toRingHom (algebraMap k A c) = algebraMap k B c := g.commutes c
    rw [hgc, IsScalarTower.algebraMap_smul B]
    rfl

omit [SMulCommClass k A M] [SMulCommClass k B N] in
/-- The coefficient head and every differential image are retained. -/
theorem coefficientFormAlgebraLinearMap_differentialWord
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (m : M) (a : Fin n → A) :
    coefficientFormAlgebraLinearMap g f hf n
      (m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (a j))) =
        f m ⊗ₜ[B] exteriorPower.ιMulti B n (fun j => KaehlerDifferential.D k B (g (a j))) := by
  change TensorProduct.map (algebraCoefficientSemilinearMap g f hf)
    (exteriorPower.mapSemilinear g.toRingHom (kaehlerAlgebraMap g) n) _ = _
  rw [TensorProduct.map_tmul, exteriorPower.mapSemilinear_ιMulti]
  simp only [kaehlerAlgebraMap_D]
  rfl

end Raw

section Complexes

variable (k : Type uk) [CommRing k]
  {A B : Type uA} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {M N : Type uM} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [SMulCommClass k A M] [SMulCommClass k B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- The coefficient/algebra map on the zero-differential form complexes. -/
def coefficientFormAlgebraComplexMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    coefficientDifferentialFormComplex k A M ⟶ coefficientDifferentialFormComplex k B N where
  f n := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{uk} (N ⊗[B] (⋀[B]^n (KaehlerDifferential k B))) ≃ₗ[k]
      N ⊗[B] (⋀[B]^n (KaehlerDifferential k B))).symm.toLinearMap.comp
        ((coefficientFormAlgebraLinearMap g f hf n).comp
          (ULift.moduleEquiv : ULift.{uk} (M ⊗[A] (⋀[A]^n (KaehlerDifferential k A))) ≃ₗ[k]
            M ⊗[A] (⋀[A]^n (KaehlerDifferential k A))).toLinearMap))
  comm' i j _h := by
    rw [coefficientDifferentialFormComplex_d_eq_zero,
      coefficientDifferentialFormComplex_d_eq_zero]
    exact CategoryTheory.Limits.comp_zero.trans CategoryTheory.Limits.zero_comp.symm

/-- The native raw Hochschild map retains the original coefficient carrier. -/
def originalAlgebraCoefficientChainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) : chainComplex k A M ⟶ chainComplex k B N := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  letI := opModule B N
  letI := actionsComm B N
  letI := kOpComm k B N
  letI := kOpTower k B N
  exact ModuleCat.Algebra.Hochschild.mapInSameUniverse g.toNonUnitalAlgHom f hf
    (by intro a m; exact hf a m)

/-- The chain-map constructor stores the original coefficient tensor map in every degree. -/
theorem originalAlgebraCoefficientChainMap_f
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    ((originalAlgebraCoefficientChainMap k g f hf).f n).hom =
      ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n := by
  let _ := opModule A M
  let _ := actionsComm A M
  let _ := kOpComm k A M
  let _ := kOpTower k A M
  let _ := opModule B N
  let _ := actionsComm B N
  let _ := kOpComm k B N
  let _ := kOpTower k B N
  have hleft : ∀ a m, f (a • m) = g.toNonUnitalAlgHom a • f m := by
    intro a m
    exact hf a m
  have hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g.toNonUnitalAlgHom a) • f m := by
    intro a m
    exact hf a m
  change ((ModuleCat.Algebra.Hochschild.mapInSameUniverse g.toNonUnitalAlgHom f hleft hright).f n).hom = _
  exact ModuleCat.Algebra.Hochschild.mapInSameUniverse_f g.toNonUnitalAlgHom f hleft hright n

/-- Every component is the original coefficient-first tensor map. -/
theorem originalAlgebraCoefficientChainMap_tprod
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (m : M) (a : Fin n → A) :
    ((originalAlgebraCoefficientChainMap k g f hf).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        f m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => g (a j)) := by
  have h := originalAlgebraCoefficientChainMap_f k g f hf n
  exact (LinearMap.congr_fun h (m ⊗ₜ[k] PiTensorProduct.tprod k a)).trans
    (ModuleCat.Algebra.Hochschild.linearMap_tprod g.toNonUnitalAlgHom f n m a)

/-- The form map preserves the lifted original differential word. -/
theorem coefficientFormAlgebraComplexMap_word
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (m : M) (a : Fin n → A) :
    ((coefficientFormAlgebraComplexMap k g f hf).f n).hom
      (ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (a j)))) =
      ULift.up (f m ⊗ₜ[B] exteriorPower.ιMulti B n
        (fun j => KaehlerDifferential.D k B (g (a j)))) :=
  congrArg ULift.up (coefficientFormAlgebraLinearMap_differentialWord g f hf n m a)

/-- Algebra and coefficient naturality of the unscaled original projection,
proved on the tensor representatives. -/
@[reassoc]
theorem coefficientDifferentialFormChainMap_algebra
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    originalAlgebraCoefficientChainMap k g f hf ≫ coefficientDifferentialFormChainMap k B N =
      coefficientDifferentialFormChainMap k A M ≫ coefficientFormAlgebraComplexMap k g f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  change ((coefficientDifferentialFormChainMap k B N).f n).hom
    (((originalAlgebraCoefficientChainMap k g f hf).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    ((coefficientFormAlgebraComplexMap k g f hf).f n).hom
      (((coefficientDifferentialFormChainMap k A M).f n).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  rw [originalAlgebraCoefficientChainMap_tprod, coefficientDifferentialFormChainMap_tprod,
    coefficientDifferentialFormChainMap_tprod, coefficientFormAlgebraComplexMap_word]

end Complexes

end ModuleCat.Algebra.Hochschild.Symmetric
