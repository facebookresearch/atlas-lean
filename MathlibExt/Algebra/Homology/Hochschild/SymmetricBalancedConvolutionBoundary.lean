/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricBalancedCutsBoundary
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricBalancedShuffleBoundary
public import MathlibExt.LinearAlgebra.TensorPower.ProperShuffleDegreeCutSuccessor

/-!
# Proper shuffle convolution commutes with the Hochschild boundary

Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module. For a cut
p+q=n, deconcatenation followed by the A-balanced signed shuffle gives an A-linear
endomorphism of M ⊗[k] A⊗n. Summing only cuts with p,q>0 gives the proper convolution
operator. It commutes with the Hochschild boundary; the middle coefficient terms cancel by
A-balancing and the degree-one endpoint boundary is zero.

See J.-L. Loday, Cyclic Homology, 2nd ed., §4.5, for both-positive shuffle relations and
Eulerian convolution.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The A-linear shuffle endomorphism of a fixed degree cut.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, for a weak cut z=(p,q) of n, algebraShuffleCutEnd is balanced signed shuffle after
deconcatenation at z. Its coefficient factor is M and its tensor tails are over k. -/
def algebraShuffleCutEnd {n : ℕ} (z : TensorPower.ShuffleDegreeCut n) :
    Module.End A (M ⊗[k] TensorPower k n A) :=
  (algebraShufflePairCutAt k A M z.val.1 z.val.2 n z.property).comp
    (algebraDeconcatCutAt k A M z.val.1 z.val.2 n z.property)

/-- The ground-linear action of an A-balanced shuffle cut.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, restricting algebraShuffleCutEnd(z) from A to k gives coefficientShuffleCutEnd(z) on
M ⊗[k] A⊗n. -/
theorem algebraShuffleCutEnd_restrictScalars {n : ℕ} (z : TensorPower.ShuffleDegreeCut n) :
    (algebraShuffleCutEnd k A M z).restrictScalars k = coefficientShuffleCutEnd k A M z := by
  rcases z with ⟨⟨p, q⟩, h⟩
  subst n
  rw [coefficientShuffleCutEnd_eq_map]
  apply TensorProduct.ext'
  intro m x
  change algebraShuffleCutEnd k A M ⟨(p, q), rfl⟩ (m ⊗ₜ[k] x) =
    TensorProduct.map LinearMap.id (TensorPower.shuffleCutEnd ⟨(p, q), rfl⟩) (m ⊗ₜ[k] x)
  simp only [algebraShuffleCutEnd, algebraShufflePairCutAt_refl,
    algebraDeconcatCutAt_refl, algebraShufflePairCut, algebraDeconcatCut,
    LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
    TensorProduct.AlgebraTensorModule.lTensor_tmul,
    TensorPower.shuffleCutEnd, TensorPower.cast_refl,
    LinearEquiv.refl_apply, LinearEquiv.refl_toLinearMap,
    LinearMap.id_apply, TensorProduct.map_tmul]
  rfl

/-- The A-linear sum over both-positive shuffle cuts.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, this endomorphism of M ⊗[k] A⊗n sums deconcatenation followed by signed shuffle over
p+q=n with p,q>0. -/
def algebraProperShuffleConvolutionTwo (n : ℕ) :
    Module.End A (M ⊗[k] TensorPower k n A) :=
  ∑ z : TensorPower.ProperShuffleDegreeCut n, algebraShuffleCutEnd k A M z.val

/-- Restriction of the proper A-linear convolution to ground scalars.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, the k-linear restriction of algebraProperShuffleConvolutionTwo(n) equals
totalProperCoefficientShuffleCutEnd(n), with the same both-positive cut index. -/
theorem algebraProperShuffleConvolutionTwo_restrictScalars (n : ℕ) :
    (algebraProperShuffleConvolutionTwo k A M n).restrictScalars k =
      totalProperCoefficientShuffleCutEnd k A M n := by
  classical
  apply LinearMap.ext
  intro x
  simp only [algebraProperShuffleConvolutionTwo, totalProperCoefficientShuffleCutEnd,
    LinearMap.restrictScalars_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro z _
  exact DFunLike.congr_fun (algebraShuffleCutEnd_restrictScalars k A M z.val) x

/-- The symmetric Hochschild boundary from degree one to zero vanishes.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, algebraBoundary(0) is zero: the two coefficient actions in b₁ agree because A is
commutative and M is symmetric. -/
@[simp]
theorem algebraBoundary_zero : algebraBoundary k A M 0 = 0 := by
  apply LinearMap.restrictScalars_injective k
  change ((chainComplex k A M).d 1 0).hom = 0
  rw [boundary_one_zero]
  rfl

private def leftBoundaryCutTerm (n : ℕ) (z : TensorPower.ProperShuffleDegreeCut (n + 2)) :
    M ⊗[k] TensorPower k (n + 2) A →ₗ[A] M ⊗[k] TensorPower k (n + 1) A := by
  have hpq := z.val.property
  have hp := z.property.1
  change z.val.val.1 + z.val.val.2 = n + 2 at hpq
  change 0 < z.val.val.1 at hp
  have hpSucc : Nat.pred z.val.val.1 + 1 = z.val.val.1 := Nat.succ_pred_eq_of_pos hp
  exact (algebraShufflePairCutAt k A M (Nat.pred z.val.val.1) z.val.val.2 (n + 1) (by omega)).comp
    ((TensorProduct.map (algebraBoundary k A (ULift.{w} A) (Nat.pred z.val.val.1)) LinearMap.id).comp
      (algebraDeconcatCutAt k A M (Nat.pred z.val.val.1 + 1) z.val.val.2 (n + 2) (by omega)))

private def rightBoundaryCutTerm (n : ℕ) (z : TensorPower.ProperShuffleDegreeCut (n + 2)) :
    M ⊗[k] TensorPower k (n + 2) A →ₗ[A] M ⊗[k] TensorPower k (n + 1) A := by
  have hpq := z.val.property
  have hq := z.property.2
  change z.val.val.1 + z.val.val.2 = n + 2 at hpq
  change 0 < z.val.val.2 at hq
  have hqSucc : Nat.pred z.val.val.2 + 1 = z.val.val.2 := Nat.succ_pred_eq_of_pos hq
  exact (-1 : ℤ) ^ z.val.val.1 •
    (algebraShufflePairCutAt k A M z.val.val.1 (Nat.pred z.val.val.2) (n + 1) (by omega)).comp
      ((TensorProduct.map LinearMap.id (algebraBoundary k A M (Nat.pred z.val.val.2))).comp
        (algebraDeconcatCutAt k A M z.val.val.1 (Nat.pred z.val.val.2 + 1) (n + 2) (by omega)))

private theorem algebraShuffleCutEnd_boundary (n : ℕ)
    (z : TensorPower.ProperShuffleDegreeCut (n + 2)) :
    (algebraBoundary k A M (n + 1)).comp (algebraShuffleCutEnd k A M z.val) =
      leftBoundaryCutTerm k A M n z + rightBoundaryCutTerm k A M n z := by
  rcases z with ⟨⟨⟨p, q⟩, hpq⟩, hp, hq⟩
  change p + q = n + 2 at hpq
  change 0 < p at hp
  change 0 < q at hq
  cases p with
  | zero => omega
  | succ r =>
    cases q with
    | zero => omega
    | succ s =>
      have hn : n = r + s := by omega
      subst n
      have h := congrArg
        (fun f => f.comp
          (algebraDeconcatCutAt k A M (r + 1) (s + 1) (r + s + 2) (by omega)))
        (algebraShufflePairCutAt_boundary_successors k A M r s)
      change (algebraBoundary k A M (r + s + 1)).comp
          ((algebraShufflePairCutAt k A M (r + 1) (s + 1) (r + s + 2) (by omega)).comp
            (algebraDeconcatCutAt k A M (r + 1) (s + 1) (r + s + 2) (by omega))) =
        (algebraShufflePairCutAt k A M r (s + 1) (r + s + 1) (by omega)).comp
          ((TensorProduct.map (algebraBoundary k A (ULift.{w} A) r) LinearMap.id).comp
            (algebraDeconcatCutAt k A M (r + 1) (s + 1) (r + s + 2) (by omega))) +
        (-1 : ℤ) ^ (r + 1) •
          (algebraShufflePairCutAt k A M (r + 1) s (r + s + 1) (by omega)).comp
            ((TensorProduct.map LinearMap.id (algebraBoundary k A M s)).comp
              (algebraDeconcatCutAt k A M (r + 1) (s + 1) (r + s + 2) (by omega)))
      simpa only [LinearMap.comp_assoc, LinearMap.add_comp, LinearMap.smul_comp] using h

private theorem leftBoundaryCutTerm_first (n : ℕ) :
    leftBoundaryCutTerm k A M n (TensorPower.firstProperDegreeCut n) = 0 := by
  change (algebraShufflePairCutAt k A M 0 (n + 1) (n + 1) (by omega)).comp
      ((TensorProduct.map (algebraBoundary k A (ULift.{w} A) 0) LinearMap.id).comp
        (algebraDeconcatCutAt k A M 1 (n + 1) (n + 2) (by omega))) = 0
  simp only [algebraBoundary_zero, TensorProduct.map_zero_left, LinearMap.zero_comp,
    LinearMap.comp_zero]

private theorem rightBoundaryCutTerm_last (n : ℕ) :
    rightBoundaryCutTerm k A M n (TensorPower.lastProperDegreeCut n) = 0 := by
  dsimp only [rightBoundaryCutTerm, TensorPower.lastProperDegreeCut, Nat.pred]
  simp only [algebraBoundary_zero, TensorProduct.map_zero_right, LinearMap.zero_comp,
    LinearMap.comp_zero, smul_zero]

private theorem algebraShuffleCutEnd_incoming_boundary (n : ℕ)
    (z : TensorPower.ProperShuffleDegreeCut (n + 1)) :
    (algebraShuffleCutEnd k A M z.val).comp (algebraBoundary k A M (n + 1)) =
      leftBoundaryCutTerm k A M n (TensorPower.leftSuccessorProperDegreeCut z) +
        rightBoundaryCutTerm k A M n (TensorPower.rightSuccessorProperDegreeCut z) := by
  have h := congrArg
    (fun f => (algebraShufflePairCutAt k A M z.val.val.1 z.val.val.2
      (n + 1) z.val.property).comp f)
    (algebraDeconcatCutAt_boundary k A M z.val.val.1 z.val.val.2 (n + 1) z.val.property)
  have hz := z.val.property
  change z.val.val.1 + z.val.val.2 = n + 1 at hz
  change ((algebraShufflePairCutAt k A M z.val.val.1 z.val.val.2 (n + 1) z.val.property).comp
      (algebraDeconcatCutAt k A M z.val.val.1 z.val.val.2 (n + 1) z.val.property)).comp
        (algebraBoundary k A M (n + 1)) =
    (algebraShufflePairCutAt k A M z.val.val.1 z.val.val.2 (n + 1) z.val.property).comp
      ((TensorProduct.map (algebraBoundary k A (ULift.{w} A) z.val.val.1) LinearMap.id).comp
        (algebraDeconcatCutAt k A M (z.val.val.1 + 1) z.val.val.2 (n + 2) (by omega))) +
    (-1 : ℤ) ^ z.val.val.1 •
      (algebraShufflePairCutAt k A M z.val.val.1 z.val.val.2 (n + 1) z.val.property).comp
        ((TensorProduct.map LinearMap.id (algebraBoundary k A M z.val.val.2)).comp
          (algebraDeconcatCutAt k A M z.val.val.1 (z.val.val.2 + 1) (n + 2) (by omega)))
  simpa only [LinearMap.comp_assoc, LinearMap.comp_add, LinearMap.comp_smul] using h

/-- The proper balanced convolution is a Hochschild chain operator.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, writing Cₙ for algebraProperShuffleConvolutionTwo(n) and bₙ : C(n+1) → C(n) for
algebraBoundary(n), bₙ₊₁ ∘ Cₙ₊₂ = Cₙ₊₁ ∘ bₙ₊₁ for every n≥0. -/
theorem algebraProperShuffleConvolutionTwo_boundary (n : ℕ) :
    (algebraBoundary k A M (n + 1)).comp (algebraProperShuffleConvolutionTwo k A M (n + 2)) =
      (algebraProperShuffleConvolutionTwo k A M (n + 1)).comp (algebraBoundary k A M (n + 1)) := by
  classical
  have hleftSum : (algebraBoundary k A M (n + 1)).comp
      (∑ z : TensorPower.ProperShuffleDegreeCut (n + 2), algebraShuffleCutEnd k A M z.val) =
    ∑ z : TensorPower.ProperShuffleDegreeCut (n + 2),
      (algebraBoundary k A M (n + 1)).comp (algebraShuffleCutEnd k A M z.val) := by
    apply LinearMap.ext
    intro x
    have h := map_sum (algebraBoundary k A M (n + 1))
      (fun z : TensorPower.ProperShuffleDegreeCut (n + 2) => algebraShuffleCutEnd k A M z.val x) Finset.univ
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using h
  have hrightSum : (∑ z : TensorPower.ProperShuffleDegreeCut (n + 1), algebraShuffleCutEnd k A M z.val).comp
      (algebraBoundary k A M (n + 1)) =
    ∑ z : TensorPower.ProperShuffleDegreeCut (n + 1),
      (algebraShuffleCutEnd k A M z.val).comp (algebraBoundary k A M (n + 1)) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [algebraProperShuffleConvolutionTwo, hleftSum]
  simp_rw [algebraShuffleCutEnd_boundary]
  rw [Finset.sum_add_distrib,
    TensorPower.sum_properDegreeCuts_left_successor n (leftBoundaryCutTerm k A M n),
    TensorPower.sum_properDegreeCuts_right_successor n (rightBoundaryCutTerm k A M n),
    leftBoundaryCutTerm_first, rightBoundaryCutTerm_last, zero_add, add_zero,
    ← Finset.sum_add_distrib]
  simp_rw [← algebraShuffleCutEnd_incoming_boundary]
  exact hrightSum.symm

end ModuleCat.Algebra.Hochschild.Symmetric
