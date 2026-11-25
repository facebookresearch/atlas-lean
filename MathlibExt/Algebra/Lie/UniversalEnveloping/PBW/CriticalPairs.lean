/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Filtration
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing

/-!
# The Jacobi identity in the overlapping PBW reductions

The calculation takes place in the original tensor algebra, before its
enveloping quotient. Reducing the two adjacent pairs of a triple in the two
orders leaves a difference that is a sum of relation errors on two vectors.
Jacobi cancels the remaining degree-one term. Basis expansion expresses these
errors as finite combinations of actual basis-pair relation errors.

This supplies the algebraic critical-pair calculation. The full induction
showing invariance of the ordered-word normalizer remains separate.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "T" => TensorAlgebra R L
local notation "τ" => TensorAlgebra.ι R

/-- The literal defining relation error in the original tensor algebra. -/
def relationError (x y : L) : T := τ x * τ y - τ y * τ x - τ ⁅x, y⁆

@[simp]
theorem relationError_self (x : L) : relationError R L x x = 0 := by
  simp only [relationError, lie_self, map_zero, sub_self]

theorem relationError_swap (x y : L) :
    relationError R L x y = -relationError R L y x := by
  have h : τ ⁅x, y⁆ = -τ ⁅y, x⁆ := by
    rw [← lie_skew x y, map_neg]
  simp only [relationError, h]
  abel

/-- The tensor relation error is linear in its second vector. -/
def relationErrorLinear (x : L) : L →ₗ[R] T where
  toFun y := relationError R L x y
  map_add' y z := by
    simp only [relationError, lie_add, map_add, mul_add, add_mul]
    abel
  map_smul' r y := by
    simp only [relationError, lie_smul, map_smul, mul_smul_comm,
      smul_mul_assoc, smul_sub, RingHom.id_apply]

@[simp]
theorem relationErrorLinear_apply (x y : L) :
    relationErrorLinear R L x y = relationError R L x y := rfl

/-- The defining relation errors form an actual bilinear map. -/
def relationErrorBilinear : L →ₗ[R] L →ₗ[R] T where
  toFun x := relationErrorLinear R L x
  map_add' x y := by
    ext z
    simp only [LinearMap.add_apply, relationErrorLinear_apply,
      relationError, add_lie, map_add, mul_add, add_mul]
    abel
  map_smul' r x := by
    ext y
    simp only [LinearMap.smul_apply, relationErrorLinear_apply,
      relationError, smul_lie, map_smul, mul_smul_comm,
      smul_mul_assoc, smul_sub, RingHom.id_apply]

/-- The error on arbitrary vectors is a finite combination of errors on
actual basis pairs; no spanning or independence claim about the quotient is used. -/
theorem relationError_basis_expand {I : Type w} (b : Module.Basis I R L) (x y : L) :
    relationError R L x y =
      (b.repr x).sum (fun i r =>
        (b.repr y).sum (fun j s => (r * s) • relationError R L (b i) (b j))) := by
  have happly (z t : L) : relationErrorBilinear R L z t = relationError R L z t := rfl
  have houter : relationError R L x y =
      (b.repr x).sum (fun i r => r • relationError R L (b i) y) := by
    have h := congrArg (fun f : L →ₗ[R] T => f y)
      (congrArg (relationErrorBilinear R L) (b.linearCombination_repr x))
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, happly] using h.symm
  have hinner (i : I) : relationError R L (b i) y =
      (b.repr y).sum (fun j s => s • relationError R L (b i) (b j)) := by
    have h := congrArg (relationErrorLinear R L (b i)) (b.linearCombination_repr y)
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      relationErrorLinear_apply] using h.symm
  rw [houter]
  simp only [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hinner]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul]

/-- The expansion after first swapping the left adjacent pair of a triple. -/
def overlapLeft (x y z : L) : T :=
  τ z * τ y * τ x + τ ⁅y, z⁆ * τ x + τ y * τ ⁅x, z⁆ + τ ⁅x, y⁆ * τ z

/-- The expansion after first swapping the right adjacent pair of a triple. -/
def overlapRight (x y z : L) : T :=
  τ z * τ y * τ x + τ z * τ ⁅x, y⁆ + τ ⁅x, z⁆ * τ y + τ x * τ ⁅y, z⁆

/-- The two overlapping reduction paths differ only by degree-two relation
errors. Jacobi removes the potential degree-one remainder over every ring. -/
theorem overlap_difference_eq_relationErrors (x y z : L) :
    overlapLeft R L x y z - overlapRight R L x y z =
      relationError R L ⁅y, z⁆ x + relationError R L y ⁅x, z⁆ +
        relationError R L ⁅x, y⁆ z := by
  have hj : ⁅⁅y, z⁆, x⁆ + ⁅y, ⁅x, z⁆⁆ + ⁅⁅x, y⁆, z⁆ = 0 := by
    rw [← lie_skew ⁅y, z⁆ x, leibniz_lie x y z]
    abel
  have ht : τ ⁅⁅y, z⁆, x⁆ + τ ⁅y, ⁅x, z⁆⁆ + τ ⁅⁅x, y⁆, z⁆ = 0 := by
    rw [← map_add, ← map_add, hj, map_zero]
  have hcalc : overlapLeft R L x y z - overlapRight R L x y z =
      relationError R L ⁅y, z⁆ x + relationError R L y ⁅x, z⁆ +
        relationError R L ⁅x, y⁆ z +
          (τ ⁅⁅y, z⁆, x⁆ + τ ⁅y, ⁅x, z⁆⁆ + τ ⁅⁅x, y⁆, z⁆) := by
    unfold overlapLeft overlapRight relationError
    noncomm_ring
  simpa only [ht, add_zero] using hcalc

/-- Fixed left and right tensor factors give an actual scalar-linear context. -/
def tensorContext (p s : T) : T →ₗ[R] T where
  toFun a := p * a * s
  map_add' a b := by simp only [mul_add, add_mul]
  map_smul' r a := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

/-- Every relation error in a fixed context lies in the span of the errors
on actual basis pairs in that same context. -/
theorem tensorContext_relationError_mem_span {I : Type w}
    (b : Module.Basis I R L) (p s : T) (x y : L) :
    tensorContext R L p s (relationError R L x y) ∈
      Submodule.span R (Set.range (fun ij : I × I =>
        tensorContext R L p s (relationError R L (b ij.1) (b ij.2)))) := by
  rw [relationError_basis_expand R L b x y]
  simp only [Finsupp.sum, map_sum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (i, j)))

/-- The Jacobi overlap difference is generated by relation errors with one
fewer tensor factor in the overlapping segment. -/
theorem tensorContext_overlap_difference_mem_span {I : Type w}
    (b : Module.Basis I R L) (p s : T) (x y z : L) :
    tensorContext R L p s (overlapLeft R L x y z - overlapRight R L x y z) ∈
      Submodule.span R (Set.range (fun ij : I × I =>
        tensorContext R L p s (relationError R L (b ij.1) (b ij.2)))) := by
  rw [overlap_difference_eq_relationErrors, map_add, map_add]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (tensorContext_relationError_mem_span R L b p s ⁅y, z⁆ x)
      (tensorContext_relationError_mem_span R L b p s y ⁅x, z⁆))
    (tensorContext_relationError_mem_span R L b p s ⁅x, y⁆ z)

/-- Disjoint reductions commute by distributivity in the original tensor
algebra. Their four finite summands agree without taking a quotient. -/
theorem disjoint_reductions_commute (a b c d m : T) :
    ((a * m * c + a * m * d) + (b * m * c + b * m * d)) =
      ((a * m * c + b * m * c) + (a * m * d + b * m * d)) := by
  noncomm_ring

/-- Every literal relation error is killed by the actual native quotient map. -/
@[simp]
theorem mkAlgHom_relationError (x y : L) :
    mkAlgHom R L (relationError R L x y) = 0 := by
  simp only [relationError, map_sub, map_mul]
  change UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
      UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x -
        UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ = 0
  rw [ι_mul_sub_mul_ι, sub_self]

end UniversalEnvelopingAlgebra.PBW
