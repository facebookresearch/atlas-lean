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
# Coefficient algebra actions on proper-shuffle quotients

Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Multiplication by a ∈ A on the coefficient slot defines a Hochschild
chain endomorphism. It commutes with the complete Hochschild boundary and with the coefficient
input of the symmetric shuffle pairing.

The proper relation submodule in degree n is the sum of all pairing component images with p,q >
0 and p+q=n. This k-submodule is stable under the coefficient A-action and under the boundary.
It therefore defines an A-linear quotient chain complex with differential [x] ↦ [bx].
Restriction along k → A identifies this algebra-linear complex with the ground-linear proper
quotient, through maps that retain every quotient representative.

For the both-positive proper-shuffle relations in Harrison homology, see J.-L. Loday, Cyclic
Homology, second edition, §4.2.
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. The
coefficient action defines a ring homomorphism A → End(C(A,M)) in the category of k-module chain
complexes. A scalar a acts in degree n by a·(m ⊗ w) = (a·m) ⊗ w. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For a ∈
A, scalarChainMap is the Hochschild chain endomorphism given in every degree by multiplication
by a on M and the identity on the algebra tail. -/
def scalarChainMap (a : A) : chainComplex k A M ⟶ chainComplex k A M :=
  (scalarChainEndRingHom k A M a).asHom

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For a ∈
A, n : ℕ, m ∈ M and t : Fin n → A, the nth scalar chain map component sends m ⊗ ⊗ⱼtⱼ to (a·m) ⊗
⊗ⱼtⱼ. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For a ∈
A, n : ℕ and x ∈ Cₙ, the underlying degree-n map of scalarChainMap k A M a sends x to a·x under
the coefficient A-action. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. The
Hochschild differential Cₙ₊₁ → Cₙ is A-linear for the coefficient action. algebraBoundary is
this A-linear map, with underlying function equal to the full Hochschild boundary. -/
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
/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For p,q :
ℕ, a lifted regular coefficient a₀, m ∈ M and words a,b of lengths p,q, the shuffle pairing is
(a₀·m) ⊗ ∑s sign(s)·⊗ⱼ(append(a,b)(s⁻¹j)). The sum ranges over (p,q)-shuffles, and a₀ denotes
its underlying A-element in the coefficient product. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For a ∈
A, write S_a for the coefficient scalar chain map and P for the pairing C(A,A_lift) ⊗ C(A,M) →
C(A,M). Then (id ⊗ S_a) ≫ P = P ≫ S_a. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. In degree
n, rawPositiveRelations is the sum of the ranges of the pairing components C_p(A,A_lift) ⊗
C_q(A,M) → Cₙ for p,q > 0 and p+q=n. It is a k-submodule of Cₙ generated by all these component
images. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For a ∈
A, n : ℕ and x ∈ rawPositiveRelations k A M n, the coefficient scalar a·x also lies in
rawPositiveRelations k A M n. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. The
k-submodule rawPositiveRelations is stable under the coefficient A-action. With the same
underlying set, it defines the A-submodule algebraPositiveRelations k A M n of Cₙ. -/
def algebraPositiveRelations (n : ℕ) : Submodule A (M ⊗[k] TensorPower k n A) where
  carrier := rawPositiveRelations k A M n
  zero_mem' := (rawPositiveRelations k A M n).zero_mem
  add_mem' := (rawPositiveRelations k A M n).add_mem
  smul_mem' := fun a _ hx => rawPositiveRelations_smul k A M a n hx

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient.
Restricting algebraPositiveRelations k A M n along k → A gives rawPositiveRelations k A M n as a
k-submodule of Cₙ. -/
theorem algebraPositiveRelations_restrictScalars (n : ℕ) :
    (algebraPositiveRelations k A M n).restrictScalars k = rawPositiveRelations k A M n := by
  ext x
  rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For n :
ℕ, algebraBoundary maps algebraPositiveRelations in degree n+1 into algebraPositiveRelations in
degree n. Equivalently Sₙ₊₁ ≤ bₙ⁻¹(Sₙ). -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. Let Sₙ be
algebraPositiveRelations. The boundary bₙ : Cₙ₊₁ → Cₙ induces an A-linear quotient differential
Cₙ₊₁/Sₙ₊₁ → Cₙ/Sₙ sending [x] to [bₙx]. -/
def algebraPositiveQuotientDifferential (n : ℕ) :
    ModuleCat.of A ((M ⊗[k] TensorPower k (n + 1) A) ⧸ algebraPositiveRelations k A M (n + 1)) ⟶
      ModuleCat.of A ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) :=
  ModuleCat.ofHom ((algebraPositiveRelations k A M (n + 1)).mapQ
    (algebraPositiveRelations k A M n) (algebraBoundary k A M n)
    (algebraPositiveRelations_boundary k A M n))

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For n :
ℕ, the quotient differential from degree n+2 to n+1 followed by that from n+1 to n is zero. This
is the Hochschild identity b²=0 after descent to the proper quotient. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. The terms
Cₙ/algebraPositiveRelations k A M n and the induced algebra-linear boundaries form an ℕ-indexed
chain complex of A-modules, algebraPositiveQuotientComplex. -/
def algebraPositiveQuotientComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of
    (fun n => ModuleCat.of A ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n))
    (algebraPositiveQuotientDifferential k A M) (algebraPositiveQuotientDifferential_comp k A M)

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient.
Restricting the quotient by the A-submodule algebraPositiveRelations to k identifies it
k-linearly with the degree-n ground proper quotient positiveQuotient k A M. The equivalence is
induced by the identity on representatives. -/
def algebraPositiveQuotientLevelEquiv (n : ℕ) :
    ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) ≃ₗ[k]
      (positiveQuotient k A M).X n :=
  (Submodule.Quotient.restrictScalarsEquiv k (algebraPositiveRelations k A M n)).symm.trans
    (Submodule.quotEquivOfEq _ _ (algebraPositiveRelations_restrictScalars k A M n))

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For n : ℕ
and x ∈ Cₙ, algebraPositiveQuotientLevelEquiv sends the class of x modulo
algebraPositiveRelations to the class of x modulo rawPositiveRelations. -/
theorem algebraPositiveQuotientLevelEquiv_mk (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    algebraPositiveQuotientLevelEquiv k A M n ((algebraPositiveRelations k A M n).mkQ x) =
      (rawPositiveRelations k A M n).mkQ x := by
  change Submodule.quotEquivOfEq _ _ (algebraPositiveRelations_restrictScalars k A M n)
    ((Submodule.Quotient.restrictScalarsEquiv k (algebraPositiveRelations k A M n)).symm
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  exact Submodule.quotEquivOfEq_mk _ _ (algebraPositiveRelations_restrictScalars k A M n) x

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. In each n
: ℕ, restriction of the A-module quotient term along k → A gives a k-module object canonically
isomorphic to (positiveQuotient k A M).X n, via the identity on quotient representatives. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For n : ℕ
and x ∈ Cₙ, the forward map of algebraPositiveQuotientRestrictionLevelIso sends [x] in the
A-linear quotient term, restricted to k, to [x] in the ground proper quotient term. -/
theorem algebraPositiveQuotientRestrictionLevelIso_mk (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    (algebraPositiveQuotientRestrictionLevelIso k A M n).hom.hom
        ((algebraPositiveRelations k A M n).mkQ x) =
      (rawPositiveRelations k A M n).mkQ x :=
  algebraPositiveQuotientLevelEquiv_mk k A M n x

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. For n : ℕ
and x ∈ Cₙ₊₁, the differential of positiveQuotient sends [x] modulo rawPositiveRelations in
degree n+1 to [algebraBoundary k A M n x] modulo rawPositiveRelations in degree n. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Put Cₙ = M ⊗[k] A^{⊗n}, with A acting only on the coefficient. The
degreewise representative-preserving restriction isomorphisms commute with the quotient
differentials and give an isomorphism between algebraPositiveQuotientComplex restricted along k
→ A and positiveQuotient k A M as k-module chain complexes. -/
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
