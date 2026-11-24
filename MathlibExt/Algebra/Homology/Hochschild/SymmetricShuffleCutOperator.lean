/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveAlgebra
public import MathlibExt.Combinatorics.Perm.EulerianElements

/-!
# coefficient-head shuffle cuts

The original coefficient stays in the second block; a head one is
inserted into the regular first coefficient. Applying the original native
symmetric Hochschild pairing gives exactly the coefficient-fixed signed
shuffle cut. Thus the explicit rational Eulerian value at two is two unit
cuts plus the original proper shuffle pairings, without a supplied cut law.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The coefficient-fixed tensor cut, with a head one in the original regular factor. -/
def coefficientShuffleCutInput {n : ℕ} (z : TensorPower.ShuffleDegreeCut n) :
    M ⊗[k] TensorPower k n A →ₗ[k]
      (ULift.{w} A ⊗[k] TensorPower k z.1.1 A) ⊗[k]
        (M ⊗[k] TensorPower k z.1.2 A) :=
  (TensorProduct.map
      (TensorProduct.mk k (ULift.{w} A) (TensorPower k z.1.1 A) (ULift.up (1 : A)))
      LinearMap.id).comp
    ((TensorProduct.leftComm k M (TensorPower k z.1.1 A) (TensorPower k z.1.2 A)).toLinearMap.comp
      ((TensorProduct.map LinearMap.id
        (TensorPower.mulEquiv (R := k) (M := A) (n := z.1.1) (m := z.1.2)).symm.toLinearMap).comp
          (TensorProduct.map LinearMap.id (TensorPower.cast k A z.2).symm.toLinearMap)))

/-- The original shuffle pairing applied to the coefficient-head cut. -/
def coefficientShuffleCutEnd {n : ℕ} (z : TensorPower.ShuffleDegreeCut n) :
    Module.End k (M ⊗[k] TensorPower k n A) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact (HomologicalComplex.ChainGradedPairing.pairAt
    (pairing.{u, v, w} k A M) z.1.1 z.1.2 n z.2).hom.comp
      (coefficientShuffleCutInput k A M z)

omit [Module A M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- The original coefficient-head input has the literal value on any two original tail tensors. -/
theorem coefficientShuffleCutInput_concat_tmul (p q : ℕ) (m : M)
    (a : TensorPower k p A) (b : TensorPower k q A) :
    coefficientShuffleCutInput k A M ⟨(p, q), rfl⟩
      (m ⊗ₜ[k] TensorPower.mulEquiv (a ⊗ₜ[k] b)) =
        (ULift.up (1 : A) ⊗ₜ[k] a) ⊗ₜ[k] (m ⊗ₜ[k] b) := by
  simp [coefficientShuffleCutInput, TensorPower.cast_refl,
    LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.leftComm_tmul]

/-- The original head-one pairing has exactly the coefficient-fixed signed shuffle value. -/
theorem coefficientShuffleCutEnd_concat_tprod (p q : ℕ) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
    coefficientShuffleCutEnd k A M ⟨(p, q), rfl⟩
      (m ⊗ₜ[k] TensorPower.mulEquiv (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) =
        m ⊗ₜ[k] TensorPower.signedShuffleProduct (V := A) p q
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  let B : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k]
      (M ⊗[k] TensorPower k q A)) →ₗ[k] M ⊗[k] TensorPower k (p + q) A :=
    ((pairing.{u, v, w} k A M).pair p q).hom
  let x := m ⊗ₜ[k] TensorPower.mulEquiv (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)
  have hEval : coefficientShuffleCutEnd k A M ⟨(p, q), rfl⟩ x =
      B (coefficientShuffleCutInput k A M ⟨(p, q), rfl⟩ x) := by
    simp only [coefficientShuffleCutEnd, HomologicalComplex.ChainGradedPairing.pairAt_rfl]
    rfl
  have hPair : B ((ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
      (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
        m ⊗ₜ[k] (∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
          AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
            PiTensorProduct.tprod k (fun j => Fin.append a b (s.perm.symm j))) := by
    let S : TensorPower k (p + q) A :=
      ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
          PiTensorProduct.tprod k (fun j => Fin.append a b (s.perm.symm j))
    have hP : B ((ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
        (m ⊗ₜ[k] PiTensorProduct.tprod k b)) = ((1 : A) • m) ⊗ₜ[k] S :=
      pairing_pair_tprod_as_tmul.{u, v, w} k A M p q (ULift.up (1 : A)) m a b
    exact hP.trans (congrArg (fun c : M => c ⊗ₜ[k] S) (one_smul A m))
  exact hEval.trans ((congrArg B (coefficientShuffleCutInput_concat_tmul k A M p q m
    (PiTensorProduct.tprod k a) (PiTensorProduct.tprod k b))).trans
      (hPair.trans (congrArg (fun z => m ⊗ₜ[k] z)
        (TensorPower.signedShuffleProduct_tprod p q a b)).symm))

/-- The original pairing cut is exactly the coefficient-fixed signed tail cut. -/
theorem coefficientShuffleCutEnd_eq_map {n : ℕ} (z : TensorPower.ShuffleDegreeCut n) :
    coefficientShuffleCutEnd k A M z =
      TensorProduct.map LinearMap.id (TensorPower.shuffleCutEnd (V := A) z) := by
  rcases z with ⟨⟨p, q⟩, h⟩
  subst n
  let L := coefficientShuffleCutEnd k A M ⟨(p, q), rfl⟩
  let R : Module.End k (M ⊗[k] TensorPower k (p + q) A) :=
    TensorProduct.map (LinearMap.id : M →ₗ[k] M) (TensorPower.shuffleCutEnd (V := A) ⟨(p, q), rfl⟩)
  let e : M ⊗[k] (TensorPower k p A ⊗[k] TensorPower k q A) ≃ₗ[k]
      M ⊗[k] TensorPower k (p + q) A :=
    TensorProduct.congr (LinearEquiv.refl k M)
      (TensorPower.mulEquiv (R := k) (M := A) (n := p) (m := q))
  have hcomp : L.comp e.toLinearMap = R.comp e.toLinearMap := by
    apply TensorProduct.curry_injective
    apply LinearMap.ext
    intro m
    apply TensorProduct.curry_injective
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro b
    change L (e (m ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b))) =
      R (e (m ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)))
    have hL : L (e (m ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b))) =
        m ⊗ₜ[k] TensorPower.signedShuffleProduct (V := A) p q
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) :=
      coefficientShuffleCutEnd_concat_tprod k A M p q m a b
    have hR : R (e (m ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b))) =
        m ⊗ₜ[k] TensorPower.signedShuffleProduct (V := A) p q
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) := by
      simp [R, e, TensorProduct.map_tmul, TensorProduct.congr_tmul,
        TensorPower.shuffleCutEnd_eq_cast, TensorPower.cast_refl,
        TensorPower.signedShuffleProduct, LinearMap.comp_apply]
    exact hL.trans hR.symm
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hcomp (e.symm x)
  change L (e (e.symm x)) = R (e (e.symm x)) at hx
  have he : e (e.symm x) = x := e.apply_symm_apply x
  exact (congrArg L he).symm.trans (hx.trans (congrArg R he))

/-- The finite sum of the original proper coefficient-head pairings. -/
def totalProperCoefficientShuffleCutEnd (n : ℕ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  ∑ z : TensorPower.ProperShuffleDegreeCut n, coefficientShuffleCutEnd k A M z.val

/-- The original proper native pairing sum is exactly the coefficient-fixed proper signed cut sum. -/
theorem totalProperCoefficientShuffleCutEnd_eq_map (n : ℕ) :
    totalProperCoefficientShuffleCutEnd k A M n =
      TensorProduct.map LinearMap.id (TensorPower.properShuffleConvolutionTwo (V := A) n) := by
  classical
  unfold totalProperCoefficientShuffleCutEnd TensorPower.properShuffleConvolutionTwo
  simp_rw [coefficientShuffleCutEnd_eq_map]
  let T := TensorPower k n A
  let F : Module.End k T →ₗ[k] Module.End k (M ⊗[k] T) :=
    (TensorProduct.mapBilinear (M := M) (N := T) (M₂ := M) (N₂ := T)
      (σ₁₂ := RingHom.id k)) (LinearMap.id : M →ₗ[k] M)
  change (∑ z : TensorPower.ProperShuffleDegreeCut n,
      F (TensorPower.shuffleCutEnd (V := A) z.val)) =
    F (∑ z : TensorPower.ProperShuffleDegreeCut n, TensorPower.shuffleCutEnd (V := A) z.val)
  exact (map_sum F _ _).symm

/-- The rational Eulerian evaluation at two has exactly the original proper shuffle cuts. -/
theorem coefficientEulerianLambda_two_eq_proper_pairings [Algebra ℚ k] (n : ℕ) (hn : 0 < n) :
    TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
        (Equiv.Perm.eulerianLambda n 2) =
      (2 : k) • LinearMap.id + totalProperCoefficientShuffleCutEnd k A M n := by
  rw [TensorPower.coefficientEulerianLambda_two_eq_properCuts n hn,
    totalProperCoefficientShuffleCutEnd_eq_map]

end ModuleCat.Algebra.Hochschild.Symmetric
