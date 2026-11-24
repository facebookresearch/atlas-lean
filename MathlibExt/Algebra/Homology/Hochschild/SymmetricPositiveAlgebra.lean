/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveNormalized
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Algebra actions on proper shuffle quotients

The coefficient-head A-action preserves the Hochschild
boundary and proper both-positive shuffle relations.
It gives an A-linear quotient complex whose restriction
to k agrees with the ground-linear quotient.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidalCategory BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The native coefficient-ring construction applied to the original algebra scalar action. -/
def scalarChainEndRingHom : A →+* End (chainComplex k A M) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.coefficientEndRingHom
    (Algebra.lsmul k k M).toRingHom
    (fun a b m => by
      change a • (b • m) = b • (a • m)
      exact smul_comm a b m)
    (fun a b m => by
      change a • (b • m) = b • (a • m)
      exact smul_comm a b m)

/-- Each original algebra scalar acts by its coefficient chain map. -/
def scalarChainMap (a : A) : chainComplex k A M ⟶ chainComplex k A M :=
  (scalarChainEndRingHom k A M a).asHom

/-- The scalar chain map scales only the original coefficient slot. -/
theorem scalarChainMap_f_tprod (a : A) (n : ℕ) (m : M) (t : Fin n → A) :
    ((scalarChainMap k A M a).f n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k t) =
      (a • m) ⊗ₜ[k] PiTensorProduct.tprod k t := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.coefficientEndRingHom_f_tprod
    (Algebra.lsmul k k M).toRingHom
    (fun c b m => by
      change c • (b • m) = b • (c • m)
      exact smul_comm c b m)
    (fun c b m => by
      change c • (b • m) = b • (c • m)
      exact smul_comm c b m) a n m t

/-- The scalar map is the original first-factor A-module action on every raw tensor. -/
theorem scalarChainMap_f_apply (a : A) (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    ((scalarChainMap k A M a).f n).hom x = a • x := by
  let s : (M ⊗[k] TensorPower k n A) →ₗ[k] M ⊗[k] TensorPower k n A :=
    ((scalarChainMap k A M a).f n).hom
  have h : s =
      TensorProduct.map (Algebra.lsmul k k M a) LinearMap.id := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m t
    have ht : TensorProduct.map (Algebra.lsmul k k M a) LinearMap.id
        (m ⊗ₜ[k] PiTensorProduct.tprod k t) = (a • m) ⊗ₜ[k] PiTensorProduct.tprod k t := by
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
      rfl
    exact (scalarChainMap_f_tprod k A M a n m t).trans ht.symm
  change s x = a • x
  rw [h]
  exact (TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor a x).symm

/-- The Hochschild boundary is linear over the original coefficient algebra. -/
def algebraBoundary (n : ℕ) :
    M ⊗[k] TensorPower k (n + 1) A →ₗ[A] M ⊗[k] TensorPower k n A where
  toFun := ((chainComplex k A M).d (n + 1) n).hom
  map_add' x y := ((chainComplex k A M).d (n + 1) n).hom.map_add x y
  map_smul' a x := by
    let d : (M ⊗[k] TensorPower k (n + 1) A) →ₗ[k] M ⊗[k] TensorPower k n A :=
      ((chainComplex k A M).d (n + 1) n).hom
    have h := ConcreteCategory.congr_hom ((scalarChainMap k A M a).comm (n + 1) n) x
    change d
        (((scalarChainMap k A M a).f (n + 1)).hom x) =
      ((scalarChainMap k A M a).f n).hom (d x) at h
    have hs : ((scalarChainMap k A M a).f (n + 1)).hom x = a • x :=
      scalarChainMap_f_apply k A M a (n + 1) x
    have ht : ((scalarChainMap k A M a).f n).hom (d x) = a • d x :=
      scalarChainMap_f_apply k A M a n (d x)
    change d (a • x) = a • d x
    exact (congrArg d hs).symm.trans (h.trans ht)

omit [SMulCommClass k A M] in
/-- The coefficient product is tensored with the original signed proper tail word. -/
theorem pairing_pair_tprod_as_tmul (p q : ℕ) (a0 : ULift.{w} A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  ((pairing.{u, v, w} k A M).pair p q).hom
      ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    (a0.down • m) ⊗ₜ[k]
      (∑ σ : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ σ •
          PiTensorProduct.tprod k (fun j => Fin.append a b (σ.perm.symm j))) := by
  classical
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  rw [pairing_pair_tprod, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact (map_zsmul (TensorProduct.mk k M (TensorPower k (p + q) A) (a0.down • m)) _ _).symm

/-- The proper shuffle pairing respects the algebra scalar maps in its coefficient input. -/
theorem pairing_scalar_naturality (a : A) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  HomologicalComplex.tensorHom (𝟙 (chainComplex k A (ULift.{w} A))) (scalarChainMap k A M a) ≫
      pairing.{u, v, w} k A M = pairing.{u, v, w} k A M ≫ scalarChainMap k A M a := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  have component (p q : ℕ) :
      (𝟙 _ ⊗ₘ (scalarChainMap k A M a).f q) ≫ (pairing.{u, v, w} k A M).pair p q =
        (pairing.{u, v, w} k A M).pair p q ≫ (scalarChainMap k A M a).f (p + q) := by
    let B : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k]
        (M ⊗[k] TensorPower k q A)) →ₗ[k] M ⊗[k] TensorPower k (p + q) A :=
      ((pairing.{u, v, w} k A M).pair p q).hom
    let s₀ : (M ⊗[k] TensorPower k q A) →ₗ[k] M ⊗[k] TensorPower k q A :=
      ((scalarChainMap k A M a).f q).hom
    let s₁ : (M ⊗[k] TensorPower k (p + q) A) →ₗ[k] M ⊗[k] TensorPower k (p + q) A :=
      ((scalarChainMap k A M a).f (p + q)).hom
    apply ModuleCat.hom_ext
    apply TensorProduct.curry_injective
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro a0 t
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m s
    change B
        (TensorProduct.map LinearMap.id s₀
          ((a0 ⊗ₜ[k] PiTensorProduct.tprod k t) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k s))) =
      s₁
        (B
          ((a0 ⊗ₜ[k] PiTensorProduct.tprod k t) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k s)))
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    have hs : s₀ (m ⊗ₜ[k] PiTensorProduct.tprod k s) =
        (a • m) ⊗ₜ[k] PiTensorProduct.tprod k s := scalarChainMap_f_tprod k A M a q m s
    rw [hs]
    have hleft := pairing_pair_tprod k A M p q a0 (a • m) t s
    have hright := pairing_pair_tprod k A M p q a0 m t s
    have hleft' : B ((a0 ⊗ₜ[k] PiTensorProduct.tprod k t) ⊗ₜ[k]
        ((a • m) ⊗ₜ[k] PiTensorProduct.tprod k s)) =
        ∑ σ : AlgebraicTopology.EilenbergZilber.Shuffle p q,
          AlgebraicTopology.EilenbergZilber.shuffleSignZ σ •
            ((a0.down • (a • m)) ⊗ₜ[k] PiTensorProduct.tprod k
              (fun j => Fin.append t s (σ.perm.symm j))) := hleft
    have hright' : B ((a0 ⊗ₜ[k] PiTensorProduct.tprod k t) ⊗ₜ[k]
        (m ⊗ₜ[k] PiTensorProduct.tprod k s)) =
        ∑ σ : AlgebraicTopology.EilenbergZilber.Shuffle p q,
          AlgebraicTopology.EilenbergZilber.shuffleSignZ σ •
            ((a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k
              (fun j => Fin.append t s (σ.perm.symm j))) := hright
    change B ((a0 ⊗ₜ[k] PiTensorProduct.tprod k t) ⊗ₜ[k]
        ((a • m) ⊗ₜ[k] PiTensorProduct.tprod k s)) = _
    rw [hleft', hright', map_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [map_zsmul]
    have hs₁ := scalarChainMap_f_tprod k A M a (p + q) (a0.down • m)
      (fun j => Fin.append t s (σ.perm.symm j))
    have hs₁' : s₁ ((a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k
        (fun j => Fin.append t s (σ.perm.symm j))) =
        (a • (a0.down • m)) ⊗ₜ[k] PiTensorProduct.tprod k
          (fun j => Fin.append t s (σ.perm.symm j)) := hs₁
    rw [hs₁', smul_comm a0.down a m]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  subst n
  change HomologicalComplex.ιTensorObj (chainComplex k A (ULift.{w} A)) (chainComplex k A M)
      p q (p + q) rfl ≫
      ((HomologicalComplex.tensorHom (𝟙 (chainComplex k A (ULift.{w} A)))
        (scalarChainMap k A M a)).f (p + q) ≫ (pairing.{u, v, w} k A M).f (p + q)) =
    HomologicalComplex.ιTensorObj (chainComplex k A (ULift.{w} A)) (chainComplex k A M)
      p q (p + q) rfl ≫
      ((pairing.{u, v, w} k A M).f (p + q) ≫ (scalarChainMap k A M a).f (p + q))
  calc
    _ = (𝟙 ((chainComplex k A (ULift.{w} A)).X p) ⊗ₘ (scalarChainMap k A M a).f q) ≫
        (HomologicalComplex.ιTensorObj (chainComplex k A (ULift.{w} A)) (chainComplex k A M)
          p q (p + q) rfl ≫ (pairing.{u, v, w} k A M).f (p + q)) := by
      have hi := HomologicalComplex.ι_mapBifunctorMap_assoc (𝟙 (chainComplex k A (ULift.{w} A)))
        (scalarChainMap k A M a)
        (MonoidalCategory.curriedTensor (ModuleCat.{max u v w} k)) (ComplexShape.down ℕ)
        p q (p + q) rfl ((pairing.{u, v, w} k A M).f (p + q))
      calc
        _ = (HomologicalComplex.ιTensorObj (chainComplex k A (ULift.{w} A)) (chainComplex k A M)
            p q (p + q) rfl ≫
            (HomologicalComplex.tensorHom (𝟙 (chainComplex k A (ULift.{w} A)))
              (scalarChainMap k A M a)).f (p + q)) ≫ (pairing.{u, v, w} k A M).f (p + q) :=
          (Category.assoc _ _ _).symm
        _ = _ := by
          simpa only [HomologicalComplex.id_f, MonoidalCategory.curriedTensor_obj_obj,
            MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app,
            MonoidalCategory.tensorHom_def_assoc, Category.assoc] using hi
    _ = (HomologicalComplex.ιTensorObj (chainComplex k A (ULift.{w} A)) (chainComplex k A M)
        p q (p + q) rfl ≫ (pairing.{u, v, w} k A M).f (p + q)) ≫
        (scalarChainMap k A M a).f (p + q) :=
      component p q
    _ = _ := Category.assoc _ _ _

/-- The fixed ground-linear relation family in the explicit native tensor dictionary. -/
def rawPositiveRelations (n : ℕ) : Submodule k (M ⊗[k] TensorPower k n A) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, w} k A M) n

/-- Original algebra scalars preserve the proper-shuffle relation sum. -/
theorem rawPositiveRelations_smul (a : A) (n : ℕ) {x : M ⊗[k] TensorPower k n A}
    (hx : x ∈ rawPositiveRelations k A M n) : a • x ∈ rawPositiveRelations k A M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  have h := HomologicalComplex.ChainGradedPairing.positiveImages_naturality
    (pairing.{u, v, w} k A M) (pairing.{u, v, w} k A M)
    (𝟙 _) (scalarChainMap k A M a) (scalarChainMap k A M a)
    (pairing_scalar_naturality k A M a) n hx
  change ((scalarChainMap k A M a).f n).hom x ∈ rawPositiveRelations k A M n at h
  exact (scalarChainMap_f_apply k A M a n x) ▸ h

/-- The same relation set, now with its original A-module structure. -/
def algebraPositiveRelations (n : ℕ) : Submodule A (M ⊗[k] TensorPower k n A) where
  carrier := rawPositiveRelations k A M n
  zero_mem' := (rawPositiveRelations k A M n).zero_mem
  add_mem' := (rawPositiveRelations k A M n).add_mem
  smul_mem' := fun a _ hx => rawPositiveRelations_smul k A M a n hx

/-- Restriction of scalars returns the original fixed ground relation submodule. -/
theorem algebraPositiveRelations_restrictScalars (n : ℕ) :
    (algebraPositiveRelations k A M n).restrictScalars k = rawPositiveRelations k A M n := by
  ext x
  rfl

/-- The original complete boundary preserves those algebra relation modules. -/
theorem algebraPositiveRelations_boundary (n : ℕ) :
    algebraPositiveRelations k A M (n + 1) ≤
      (algebraPositiveRelations k A M n).comap (algebraBoundary k A M n) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  intro x hx
  have h := HomologicalComplex.ChainGradedPairing.positiveImages_d
    (pairing.{u, v, w} k A M) (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M) n hx
  change ((chainComplex k A M).d (n + 1) n).hom x ∈ rawPositiveRelations k A M n at h
  exact h

/-- The A-linear differential of the proper-shuffle quotient. -/
def algebraPositiveQuotientDifferential (n : ℕ) :
    ModuleCat.of A ((M ⊗[k] TensorPower k (n + 1) A) ⧸ algebraPositiveRelations k A M (n + 1)) ⟶
      ModuleCat.of A ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) :=
  ModuleCat.ofHom ((algebraPositiveRelations k A M (n + 1)).mapQ
    (algebraPositiveRelations k A M n) (algebraBoundary k A M n)
    (algebraPositiveRelations_boundary k A M n))

/-- Its square is zero by the original Hochschild differential. -/
theorem algebraPositiveQuotientDifferential_comp (n : ℕ) :
    algebraPositiveQuotientDifferential k A M (n + 1) ≫ algebraPositiveQuotientDifferential k A M n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  change (algebraPositiveRelations k A M n).mkQ
    (((chainComplex k A M).d (n + 1) n).hom
      (((chainComplex k A M).d (n + 2) (n + 1)).hom x)) = 0
  have h := ConcreteCategory.congr_hom ((chainComplex k A M).d_comp_d (n + 2) (n + 1) n) x
  change ((chainComplex k A M).d (n + 1) n).hom
    (((chainComplex k A M).d (n + 2) (n + 1)).hom x) = 0 at h
  exact (congrArg (algebraPositiveRelations k A M n).mkQ h).trans (map_zero _)

/-- The original ground-tensor positive quotient, with its algebra-linear boundary. -/
def algebraPositiveQuotientComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of
    (fun n => ModuleCat.of A ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n))
    (algebraPositiveQuotientDifferential k A M) (algebraPositiveQuotientDifferential_comp k A M)

/-- Native quotient scalar restriction identifies the original quotient classes. -/
def algebraPositiveQuotientLevelEquiv (n : ℕ) :
    ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) ≃ₗ[k]
      (positiveQuotient k A M).X n :=
  (Submodule.Quotient.restrictScalarsEquiv k (algebraPositiveRelations k A M n)).symm.trans
    (Submodule.quotEquivOfEq _ _ (algebraPositiveRelations_restrictScalars k A M n))

/-- The scalar-restriction coordinates retain the same original quotient representative. -/
theorem algebraPositiveQuotientLevelEquiv_mk (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    algebraPositiveQuotientLevelEquiv k A M n ((algebraPositiveRelations k A M n).mkQ x) =
      (rawPositiveRelations k A M n).mkQ x := by
  change Submodule.quotEquivOfEq _ _ (algebraPositiveRelations_restrictScalars k A M n)
    ((Submodule.Quotient.restrictScalarsEquiv k (algebraPositiveRelations k A M n)).symm
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  exact Submodule.quotEquivOfEq_mk _ _ (algebraPositiveRelations_restrictScalars k A M n) x

/-- The native restriction functor retains the original quotient's ground action. -/
def algebraPositiveQuotientRestrictionLevelIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k A)).obj ((algebraPositiveQuotientComplex k A M).X n) ≅
      (positiveQuotient k A M).X n := by
  let e := algebraPositiveQuotientLevelEquiv k A M n
  let f : (ModuleCat.restrictScalars (algebraMap k A)).obj
      ((algebraPositiveQuotientComplex k A M).X n) ≃ₗ[k]
        ModuleCat.of k ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        refine Quotient.inductionOn' x ?_
        intro y
        change (algebraPositiveRelations k A M n).mkQ ((algebraMap k A r) • y) =
          (algebraPositiveRelations k A M n).mkQ (r • y)
        have h : (algebraMap k A r) • y = r • y := by
          simpa only [Algebra.smul_def, mul_one, one_smul] using smul_assoc r (1 : A) y
        exact congrArg (algebraPositiveRelations k A M n).mkQ h }
  exact (f.trans e).toModuleIso

/-- The restriction map sends the original quotient class to that same raw class. -/
theorem algebraPositiveQuotientRestrictionLevelIso_mk (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    (algebraPositiveQuotientRestrictionLevelIso k A M n).hom.hom
        ((algebraPositiveRelations k A M n).mkQ x) =
      (rawPositiveRelations k A M n).mkQ x :=
  algebraPositiveQuotientLevelEquiv_mk k A M n x

/-- The raw proper quotient differential retains the original A-linear boundary value. -/
theorem positiveQuotient_d_mk (n : ℕ) (x : M ⊗[k] TensorPower k (n + 1) A) :
    ((positiveQuotient k A M).d (n + 1) n).hom ((rawPositiveRelations k A M (n + 1)).mkQ x) =
      (rawPositiveRelations k A M n).mkQ (algebraBoundary k A M n x) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  change ((HomologicalComplex.ChainGradedPairing.positiveImageQuotient
    (pairing.{u, v, w} k A M) (boundary_one_zero k A (ULift.{w} A))
      (boundary_one_zero k A M)).d (n + 1) n).hom _ = _
  dsimp only [HomologicalComplex.ChainGradedPairing.positiveImageQuotient]
  rw [ChainComplex.of_d]
  rfl

/-- The A-linear quotient is the original positive quotient after native scalar restriction. -/
def algebraPositiveQuotientRestrictionIso :
    ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (algebraPositiveQuotientComplex k A M) ≅ positiveQuotient k A M :=
  HomologicalComplex.Hom.isoOfComponents (algebraPositiveQuotientRestrictionLevelIso k A M) (by
    intro i j h
    change j + 1 = i at h
    subst i
    let S := ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (algebraPositiveQuotientComplex k A M)
    let T := positiveQuotient k A M
    let f₁ : S.X (j + 1) →ₗ[k] T.X (j + 1) :=
      (algebraPositiveQuotientRestrictionLevelIso k A M (j + 1)).hom.hom
    let f₀ : S.X j →ₗ[k] T.X j :=
      (algebraPositiveQuotientRestrictionLevelIso k A M j).hom.hom
    let d : T.X (j + 1) →ₗ[k] T.X j := (T.d (j + 1) j).hom
    let e : S.X (j + 1) →ₗ[k] S.X j := (S.d (j + 1) j).hom
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change d (f₁ z) = f₀ (e z)
    refine Quotient.inductionOn' z ?_
    intro x
    have hd : e ((algebraPositiveRelations k A M (j + 1)).mkQ x) =
        (algebraPositiveRelations k A M j).mkQ (algebraBoundary k A M j x) := by
      change ((algebraPositiveQuotientComplex k A M).d (j + 1) j).hom _ = _
      dsimp only [algebraPositiveQuotientComplex]
      rw [ChainComplex.of_d]
      rfl
    have hf₁ : f₁ ((algebraPositiveRelations k A M (j + 1)).mkQ x) =
        (rawPositiveRelations k A M (j + 1)).mkQ x :=
      algebraPositiveQuotientRestrictionLevelIso_mk k A M (j + 1) x
    have hf₀ : f₀ ((algebraPositiveRelations k A M j).mkQ (algebraBoundary k A M j x)) =
        (rawPositiveRelations k A M j).mkQ (algebraBoundary k A M j x) :=
      algebraPositiveQuotientRestrictionLevelIso_mk k A M j (algebraBoundary k A M j x)
    let y : T.X j := (rawPositiveRelations k A M j).mkQ (algebraBoundary k A M j x)
    have hd' : d ((rawPositiveRelations k A M (j + 1)).mkQ x) = y :=
      positiveQuotient_d_mk k A M j x
    have hf₀' : f₀ ((algebraPositiveRelations k A M j).mkQ (algebraBoundary k A M j x)) = y := hf₀
    exact (congrArg d hf₁).trans
      (hd'.trans (hf₀'.symm.trans (congrArg f₀ hd.symm))))

end ModuleCat.Algebra.Hochschild.Symmetric
