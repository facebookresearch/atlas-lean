/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveAlgebra
public import MathlibExt.Algebra.Homology.LinearHomCochainComplex
public import MathlibExt.Algebra.Homology.HomologicalComplex.ChangeObjects
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Algebra-linear cochains on proper shuffle quotients

The regular chain coefficient is A, its tensor tails are over k
and cochain values lie in an A-module M. The complex Hom_A(-, M)
of the proper quotient identifies with ground-linear tensor
cochains annihilating the proper shuffle relations. Canonical
whole-module lifts accommodate independent carrier universes.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The ordinary tensor-cochain condition is annihilation of the regular proper relation set. -/
def properAlgebraCochains (n : ℕ) : Submodule A (TensorPower k n A →ₗ[k] M) where
  carrier := {F | ∀ x ∈ algebraPositiveRelations k A A n, F.liftBaseChange A x = 0}
  zero_mem' := by
    intro x hx
    change (LinearMap.liftBaseChangeEquiv A (0 : TensorPower k n A →ₗ[k] M)) x = 0
    rw [map_zero]
    rfl
  add_mem' := by
    intro F G hF hG x hx
    change (LinearMap.liftBaseChangeEquiv A (F + G)) x = 0
    rw [map_add, LinearMap.add_apply, hF x hx, hG x hx, add_zero]
  smul_mem' := by
    intro a F hF x hx
    change (LinearMap.liftBaseChangeEquiv A (a • F)) x = 0
    rw [map_smul, LinearMap.smul_apply, hF x hx, smul_zero]

/-- Ordinary proper-shuffle cochains are exactly the tensor cochains annihilating the signed words. -/
theorem mem_properAlgebraCochains_iff (n : ℕ) (F : TensorPower k n A →ₗ[k] M) :
    F ∈ properAlgebraCochains k A M n ↔
      ∀ (p q : ℕ) (h : p + q = n), 0 < p → 0 < q →
        ∀ (a : Fin p → A) (b : Fin q → A),
          F (TensorPower.cast k A h
            (∑ σ : AlgebraicTopology.EilenbergZilber.Shuffle p q,
              AlgebraicTopology.EilenbergZilber.shuffleSignZ σ •
                PiTensorProduct.tprod k (fun j => Fin.append a b (σ.perm.symm j)))) = 0 := by
  classical
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, v} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, v} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, v} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, v} (R := k)
  constructor
  · intro hF p q h hp hq a b
    subst n
    let x : (ULift.{v} A ⊗[k] TensorPower k p A) ⊗[k]
        (A ⊗[k] TensorPower k q A) :=
      (ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
        ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k b)
    have hx := HomologicalComplex.ChainGradedPairing.pairAt_mem_positiveImages
      (pairing.{u, v, v} k A A) p q (p + q) rfl hp hq x
    have hzero := hF _ hx
    change F.liftBaseChange A (((pairing.{u, v, v} k A A).pair p q).hom x) = 0 at hzero
    let W : TensorPower k (p + q) A :=
      ∑ σ : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ σ •
          PiTensorProduct.tprod k (fun j => Fin.append a b (σ.perm.symm j))
    have hv : (((pairing.{u, v, v} k A A).pair p q).hom x) = (1 : A) ⊗ₜ[k] W := by
      have h := pairing_pair_tprod_as_tmul k A A p q (ULift.up (1 : A)) (1 : A) a b
      have h' : (((pairing.{u, v, v} k A A).pair p q).hom x) =
          ((1 : A) • (1 : A)) ⊗ₜ[k] W := h
      exact h'.trans (congrArg (fun z : A => z ⊗ₜ[k] W) (by simp : (1 : A) • (1 : A) = 1))
    have he : F.liftBaseChange A (((pairing.{u, v, v} k A A).pair p q).hom x) = F W :=
      (congrArg (F.liftBaseChange A) hv).trans (LinearMap.liftBaseChange_one_tmul A F W)
    have hFW : F W = 0 := he.symm.trans hzero
    simpa only [TensorPower.cast_refl, LinearEquiv.refl_apply] using hFW
  · intro hF
    change rawPositiveRelations k A A n ≤ (LinearMap.ker (F.liftBaseChange A)).restrictScalars k
    change HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, v} k A A) n ≤ _
    apply iSup_le
    rintro ⟨⟨p, q⟩, hp, hq, hn⟩
    subst n
    apply LinearMap.range_le_ker_iff.mpr
    apply TensorProduct.curry_injective
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro a0 a
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro b0 b
    change F.liftBaseChange A
      (((pairing.{u, v, v} k A A).pair p q).hom
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (b0 ⊗ₜ[k] PiTensorProduct.tprod k b))) = 0
    have hv := pairing_pair_tprod_as_tmul k A A p q a0 b0 a b
    rw [hv, LinearMap.liftBaseChange_tmul A]
    have hword := hF p q rfl hp hq a b
    have hzero : F
        (∑ σ : AlgebraicTopology.EilenbergZilber.Shuffle p q,
          AlgebraicTopology.EilenbergZilber.shuffleSignZ σ •
            PiTensorProduct.tprod k (fun j => Fin.append a b (σ.perm.symm j))) = 0 := by
      simpa only [TensorPower.cast_refl, LinearEquiv.refl_apply] using hword
    rw [hzero, smul_zero]

/-- Native base-change Hom adjunction followed by the quotient universal property. -/
def properAlgebraCochainEquiv (n : ℕ) :
    (((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) →ₗ[A] M) ≃ₗ[A]
      properAlgebraCochains k A M n where
  toFun φ :=
    ⟨(LinearMap.liftBaseChangeEquiv A).symm
        (φ.comp (algebraPositiveRelations k A A n).mkQ), by
      intro x hx
      change (LinearMap.liftBaseChangeEquiv A
          ((LinearMap.liftBaseChangeEquiv A).symm
            (φ.comp (algebraPositiveRelations k A A n).mkQ))) x = 0
      rw [LinearEquiv.apply_symm_apply]
      have hq : (algebraPositiveRelations k A A n).mkQ x = 0 := by
        change x ∈ LinearMap.ker (algebraPositiveRelations k A A n).mkQ
        simpa only [Submodule.ker_mkQ] using hx
      change φ ((algebraPositiveRelations k A A n).mkQ x) = 0
      rw [hq, map_zero]⟩
  invFun F := (algebraPositiveRelations k A A n).liftQ
    (F.val.liftBaseChange A) (by
      intro x hx
      exact F.property x hx)
  left_inv φ := by
    apply LinearMap.ext
    intro z
    refine Quotient.inductionOn' z ?_
    intro x
    change (LinearMap.liftBaseChangeEquiv A
        ((LinearMap.liftBaseChangeEquiv A).symm
          (φ.comp (algebraPositiveRelations k A A n).mkQ))) x =
      φ ((algebraPositiveRelations k A A n).mkQ x)
    rw [LinearEquiv.apply_symm_apply]
    rfl
  right_inv F := by
    apply Subtype.ext
    change (LinearMap.liftBaseChangeEquiv A).symm
        (((algebraPositiveRelations k A A n).liftQ (F.val.liftBaseChange A)
          (by intro x hx; exact F.property x hx)).comp (algebraPositiveRelations k A A n).mkQ) = F.val
    have h := Submodule.liftQ_mkQ (algebraPositiveRelations k A A n) (F.val.liftBaseChange A)
      (by intro x hx; exact F.property x hx)
    exact (congrArg (LinearMap.liftBaseChangeEquiv A).symm h).trans
      ((LinearMap.liftBaseChangeEquiv A).symm_apply_apply F.val)
  map_add' φ ψ := by
    apply Subtype.ext
    change (LinearMap.liftBaseChangeEquiv A).symm
        ((φ + ψ).comp (algebraPositiveRelations k A A n).mkQ) = _
    rw [LinearMap.add_comp, map_add]
    rfl
  map_smul' a φ := by
    apply Subtype.ext
    change (LinearMap.liftBaseChangeEquiv A).symm
        ((a • φ).comp (algebraPositiveRelations k A A n).mkQ) = _
    rw [LinearMap.smul_comp, map_smul]
    rfl

/-- Forward degree coordinates are evaluation on the original coefficient head one. -/
theorem properAlgebraCochainEquiv_tprod (n : ℕ)
    (φ : ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) →ₗ[A] M)
    (t : Fin n → A) :
    (properAlgebraCochainEquiv k A M n φ).val (PiTensorProduct.tprod k t) =
      φ ((algebraPositiveRelations k A A n).mkQ ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k t)) := by
  exact LinearMap.liftBaseChangeEquiv_symm_apply A
    (φ.comp (algebraPositiveRelations k A A n).mkQ) (PiTensorProduct.tprod k t)

/-- The inverse coordinates retain the original A-linear coefficient value. -/
theorem properAlgebraCochainEquiv_symm_tprod (n : ℕ)
    (F : properAlgebraCochains k A M n) (a0 : A) (t : Fin n → A) :
    (properAlgebraCochainEquiv k A M n).symm F
        ((algebraPositiveRelations k A A n).mkQ (a0 ⊗ₜ[k] PiTensorProduct.tprod k t)) =
      a0 • F.val (PiTensorProduct.tprod k t) :=
  LinearMap.liftBaseChange_tmul A F.val _ _

/-- The regular quotient is lifted by the native whole-module universe functor. -/
def regularAlgebraPositiveQuotientForHom : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (algebraPositiveQuotientComplex k A A)

/-- Native linear Hom_A of the regular quotient complex. -/
def nativePositiveAlgebraCochainComplex : CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).obj
      (Opposite.op (regularAlgebraPositiveQuotientForHom.{u, v, w} k A))

/-- Covariance in the A-module cochain target is the native linear Hom bifunctor. -/
def nativePositiveAlgebraCochainFunctor :
    ModuleCat.{max u v w} A ⥤ CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  HomologicalComplex.linearHomCochainComplexBifunctor A (ModuleCat.{max u v w} A) ⋙
    (evaluation _ _).obj (Opposite.op (regularAlgebraPositiveQuotientForHom.{u, v, w} k A))

/-- Every cohomology degree varies functorially in the original A-module target. -/
def nativePositiveAlgebraCohomologyFunctor (n : ℕ) :
    ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} A :=
  HomologicalComplex.linearHomCochainComplexHomologyFunctor A (ModuleCat.{max u v w} A)
    (regularAlgebraPositiveQuotientForHom.{u, v, w} k A) n

/-- Native whole-level ULift coordinates are the original algebra-linear quotient cochains. -/
def positiveAlgebraCochainLevelEquiv (n : ℕ) :
    (nativePositiveAlgebraCochainComplex k A M).X n ≃ₗ[A]
      (((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) →ₗ[A] M) where
  toFun φ := by
    let ψ : ModuleCat.of A (ULift.{w}
        ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n)) ⟶
        ModuleCat.of A (ULift.{max u v} M) := φ
    exact
      (ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[A] M).toLinearMap.comp
        (ψ.hom.comp
          (ULift.moduleEquiv : ULift.{w}
            ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) ≃ₗ[A]
              ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n)).symm.toLinearMap)
  invFun φ := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[A] M).symm.toLinearMap.comp
       (φ.comp (ULift.moduleEquiv : ULift.{w}
         ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) ≃ₗ[A]
           ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n)).toLinearMap))
  left_inv φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    let s : ULift.{w} ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) ≃ₗ[A]
        ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) := ULift.moduleEquiv
    let t : ULift.{max u v} M ≃ₗ[A] M := ULift.moduleEquiv
    let ψ : ModuleCat.of A (ULift.{w}
        ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n)) ⟶
        ModuleCat.of A (ULift.{max u v} M) := φ
    change t.symm (t (ψ.hom (s.symm (s (ULift.up x))))) = ψ.hom (ULift.up x)
    rw [s.symm_apply_apply, t.symm_apply_apply]
  right_inv φ := by
    apply LinearMap.ext
    intro x
    rfl
  map_add' φ ψ := rfl
  map_smul' a φ := rfl

/-- The Hom_A complex in literal original-world quotient-cochain coordinates. -/
def positiveAlgebraCochainComplex : CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  (nativePositiveAlgebraCochainComplex k A M).changeObjects
    (fun n => (positiveAlgebraCochainLevelEquiv k A M n).toModuleIso)

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- Its differential is precomposition with the A-linear quotient differential. -/
theorem positiveAlgebraCochainComplex_d_apply (n : ℕ)
    (φ : ((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) →ₗ[A] M)
    (x : (A ⊗[k] TensorPower k (n + 1) A) ⧸ algebraPositiveRelations k A A (n + 1)) :
    let d :
        (((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) →ₗ[A] M) →ₗ[A]
          (((A ⊗[k] TensorPower k (n + 1) A) ⧸ algebraPositiveRelations k A A (n + 1)) →ₗ[A] M) :=
      ((positiveAlgebraCochainComplex k A M).d n (n + 1)).hom
    d φ x = φ ((algebraPositiveQuotientDifferential k A A n).hom x) := by
  dsimp only [positiveAlgebraCochainComplex, HomologicalComplex.changeObjects]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  let K := regularAlgebraPositiveQuotientForHom.{u, v, w} k A
  let F := ((linearYoneda A (ModuleCat.{max u v w} A)).obj
    (ModuleCat.of A (ULift.{max u v} M))).mapHomologicalComplex (ComplexShape.up ℕ)
  let L : CochainComplex (ModuleCat.{max u v w} A) ℕ := F.obj K.op
  have hd : (nativePositiveAlgebraCochainComplex k A M).d n (n + 1) = L.d n (n + 1) := rfl
  rw [hd]
  dsimp only [L, F, Functor.mapHomologicalComplex]
  simp only [HomologicalComplex.op_d, CategoryTheory.linearYoneda_obj_map]
  dsimp only [K, regularAlgebraPositiveQuotientForHom, Functor.mapHomologicalComplex]
  dsimp only [algebraPositiveQuotientComplex]
  rw [ChainComplex.of_d]
  rfl

/-- Transport to the conventional ground-linear tensor cochains satisfying the proper relations. -/
def properAlgebraCochainComplex : CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  (positiveAlgebraCochainComplex k A M).changeObjects
    (fun n => (properAlgebraCochainEquiv k A M n).toModuleIso)

/-- The Hom_A complex and its conventional tensor-cochain representation agree as complexes. -/
def properAlgebraCochainComplexIso :
    positiveAlgebraCochainComplex k A M ≅ properAlgebraCochainComplex k A M :=
  (positiveAlgebraCochainComplex k A M).changeObjectsIso
    (fun n => (properAlgebraCochainEquiv k A M n).toModuleIso)

/-- The complete source coboundary is evaluated by the original signed Hochschild faces. -/
theorem properAlgebraCochainComplex_d_tprod (n : ℕ)
    (F : properAlgebraCochains k A M n) (t : Fin (n + 1) → A) :
  letI := opModule A A
  letI := actionsComm A A
  letI := kOpComm k A A
  letI := kOpTower k A A
  ((((properAlgebraCochainComplex k A M).d n (n + 1)).hom F).val) (PiTensorProduct.tprod k t) =
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      F.val.liftBaseChange A (ModuleCat.Algebra.Hochschild.faceValue k A A n j 1 t) := by
  letI := opModule A A
  letI := actionsComm A A
  letI := kOpComm k A A
  letI := kOpTower k A A
  let D : properAlgebraCochains k A M n →ₗ[A] properAlgebraCochains k A M (n + 1) :=
    ((properAlgebraCochainComplex k A M).d n (n + 1)).hom
  let φ := (properAlgebraCochainEquiv k A M n).symm F
  have hD : (D F).val (PiTensorProduct.tprod k t) =
      φ ((algebraPositiveQuotientDifferential k A A n).hom
        ((algebraPositiveRelations k A A (n + 1)).mkQ
          ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k t))) := by
    change (properAlgebraCochainEquiv k A M (n + 1)
      (((positiveAlgebraCochainComplex k A M).d n (n + 1)).hom φ)).val _ = _
    let δ :
        (((A ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A A n) →ₗ[A] M) →ₗ[A]
          (((A ⊗[k] TensorPower k (n + 1) A) ⧸ algebraPositiveRelations k A A (n + 1)) →ₗ[A] M) :=
      ((positiveAlgebraCochainComplex k A M).d n (n + 1)).hom
    have h₁ := properAlgebraCochainEquiv_tprod k A M (n + 1) (δ φ) t
    have h₂ := positiveAlgebraCochainComplex_d_apply k A M n φ
      ((algebraPositiveRelations k A A (n + 1)).mkQ ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k t))
    exact h₁.trans h₂
  have he : (D F).val (PiTensorProduct.tprod k t) =
      F.val.liftBaseChange A (algebraBoundary k A A n
        ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k t)) := by
    rw [hD]
    rfl
  change (D F).val (PiTensorProduct.tprod k t) = _
  rw [he]
  change F.val.liftBaseChange A
      (((ModuleCat.Algebra.Hochschild.chainComplex k A A).d (n + 1) n).hom
        ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k t)) = _
  have hb := ModuleCat.Algebra.Hochschild.boundary_tprod k A A n (1 : A) t
  have heval :
      ((ModuleCat.Algebra.Hochschild.chainComplex k A A).d (n + 1) n).hom
        ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k t) =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
          ModuleCat.Algebra.Hochschild.faceValue k A A n j 1 t := by
    rw [ModuleCat.Algebra.Hochschild.chainComplex_d]
    exact hb
  exact (congrArg (F.val.liftBaseChange A) heval).trans (by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact map_zsmul (F.val.liftBaseChange A) _ _)

/-- Actual algebra-linear proper-shuffle cohomology in every nonnegative degree. -/
def positiveAlgebraCohomology (n : ℕ) : ModuleCat.{max u v w} A :=
  (positiveAlgebraCochainComplex k A M).homology n

/-- The tensor-cochain representation induces the all-degree cohomology isomorphism. -/
def properAlgebraCohomologyIso (n : ℕ) :
    positiveAlgebraCohomology k A M n ≅ (properAlgebraCochainComplex k A M).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) n).mapIso
    (properAlgebraCochainComplexIso k A M)

end ModuleCat.Algebra.Hochschild.Symmetric
