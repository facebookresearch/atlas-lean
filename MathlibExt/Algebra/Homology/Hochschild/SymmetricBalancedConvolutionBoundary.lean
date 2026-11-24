/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
UNEXECUTED source proposal. The original algebraBoundary, A-balanced cuts,
signed shuffle multiplication and coefficient carriers are retained.
-/
module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricBalancedCutsBoundary
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricBalancedShuffleBoundary
public import MathlibExt.LinearAlgebra.TensorPower.ProperShuffleDegreeCutSuccessor

/-!
# Boundary compatibility of proper shuffle convolution

Each deconcatenation cut followed by balanced signed
shuffle satisfies the convolution boundary identity.
The finite successor-cut sum cancels the interior
terms; the endpoint terms vanish by the symmetric
degree-one boundary formula.
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

/-- The original cut and signed shuffle, with their original target degree. -/
def algebraShuffleCutEnd {n : ℕ} (z : TensorPower.ShuffleDegreeCut n) :
    Module.End A (M ⊗[k] TensorPower k n A) :=
  (algebraShufflePairCutAt k A M z.val.1 z.val.2 n z.property).comp
    (algebraDeconcatCutAt k A M z.val.1 z.val.2 n z.property)

/-- Changing the balancing and returning to the original level gives the
original coefficient-fixed signed cut, without changing any tail. -/
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

/-- The A-linear sum of the original both-positive shuffle cuts. -/
def algebraProperShuffleConvolutionTwo (n : ℕ) :
    Module.End A (M ⊗[k] TensorPower k n A) :=
  ∑ z : TensorPower.ProperShuffleDegreeCut n, algebraShuffleCutEnd k A M z.val

/-- The balanced sum retains the original coefficient proper-cut sum. -/
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

/-- The original symmetric degree-one boundary is zero also in the original
coefficient-head A-module structure. -/
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

/-- The proper shuffle convolution commutes with the original
Hochschild boundary in every incoming degree at least two. Both successor
sums come from the original balanced cut boundary; their extra endpoint
terms vanish by the original symmetric degree-one boundary. -/
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
