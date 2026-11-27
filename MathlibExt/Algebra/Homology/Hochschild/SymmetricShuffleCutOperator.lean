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
# Coefficient-head shuffle cuts and Eulerian evaluation

Let k be a commutative ring, A a commutative k-algebra and M a compatible symmetric coefficient
module. A weak cut p+q=n splits a raw tensor tail into two blocks, inserts coefficient 1 into
the regular first block and retains M as the coefficient of the second block. Recombining with
the symmetric shuffle pairing fixes the coefficient and applies the signed tail shuffle-cut
operator.

Each coefficient cut therefore equals id_M ⊗ shuffleCutEnd. Summing over cuts with p,q > 0 gives
id_M tensored with the proper shuffle convolution at two. If k is a ℚ-algebra and n>0, the
coefficient action of the Eulerian element Λₙ(2) is 2·id plus this sum of proper cuts, the two
identity terms coming from the empty-block cuts.

For Eulerian elements and shuffle convolution, see J.-L. Loday, Cyclic Homology, second edition,
§4.5.
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a k-module. For a weak cut z=(p,q)
with p+q=n, coefficientShuffleCutInput splits the degree-n tail into its two blocks and sends m
⊗ concat(a,b) to (1 ⊗ a) ⊗ (m ⊗ b). The first coefficient 1 is in the chosen lift of A. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. For a weak cut z=(p,q) with p+q=n, compose coefficientShuffleCutInput
with the (p,q)-pairing component, transported to degree n. This gives coefficientShuffleCutEnd,
a k-linear endomorphism of M ⊗_k A^{⊗n}. -/
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
/-- Let k be a commutative ring, A a commutative k-algebra and M a k-module. For p,q : ℕ, m ∈ M, a ∈
A^{⊗p} and b ∈ A^{⊗q}, coefficientShuffleCutInput for the cut (p,q) sends m ⊗ concat(a,b) to (1
⊗ a) ⊗ (m ⊗ b). No A-action on M is needed for this tensor-splitting formula. -/
theorem coefficientShuffleCutInput_concat_tmul (p q : ℕ) (m : M)
    (a : TensorPower k p A) (b : TensorPower k q A) :
    coefficientShuffleCutInput k A M ⟨(p, q), rfl⟩
      (m ⊗ₜ[k] TensorPower.mulEquiv (a ⊗ₜ[k] b)) =
        (ULift.up (1 : A) ⊗ₜ[k] a) ⊗ₜ[k] (m ⊗ₜ[k] b) := by
  simp [coefficientShuffleCutInput, TensorPower.cast_refl,
    LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.leftComm_tmul]

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. For p,q : ℕ, m ∈ M and tail words a,b, coefficientShuffleCutEnd for
(p,q) sends m ⊗ concat(⊗a,⊗b) to m ⊗ signedShuffleProduct(⊗a,⊗b). The tail is ∑s
sign(s)·⊗ᵢappend(a,b)(s.perm⁻¹i), and the coefficient is fixed. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. For any weak degree cut z=(p,q) with p+q=n, coefficientShuffleCutEnd k A
M z equals id_M ⊗ shuffleCutEnd(A,z). Thus the coefficient-head construction agrees with the
signed tail cut in all degree coordinates. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. In degree n : ℕ, totalProperCoefficientShuffleCutEnd is the finite sum
of coefficientShuffleCutEnd over all cuts p,q > 0 with p+q=n. It is an endomorphism of M ⊗_k
A^{⊗n}. -/
def totalProperCoefficientShuffleCutEnd (n : ℕ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  ∑ z : TensorPower.ProperShuffleDegreeCut n, coefficientShuffleCutEnd k A M z.val

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. For every n : ℕ, totalProperCoefficientShuffleCutEnd equals id_M ⊗
properShuffleConvolutionTwo(A,n), where the tail convolution is the sum of all signed
shuffle-cut endomorphisms with both block degrees positive. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. Assume k is a ℚ-algebra and n : ℕ satisfies 0<n. The coefficient
rational permutation action of the Eulerian element Λₙ(2) equals 2·id +
totalProperCoefficientShuffleCutEnd k A M n. The two empty-block cuts give the identity terms,
while the remaining cuts have both degrees positive. -/
theorem coefficientEulerianLambda_two_eq_proper_pairings [Algebra ℚ k] (n : ℕ) (hn : 0 < n) :
    TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
        (Equiv.Perm.eulerianLambda n 2) =
      (2 : k) • LinearMap.id + totalProperCoefficientShuffleCutEnd k A M n := by
  rw [TensorPower.coefficientEulerianLambda_two_eq_properCuts n hn,
    totalProperCoefficientShuffleCutEnd_eq_map]

end ModuleCat.Algebra.Hochschild.Symmetric
