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
# Jacobi cancellation for overlapping enveloping relations

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `τ : L → T_R(L)` the tensor-algebra
inclusion. The defining relation error is `r(x,y) = τ(x)τ(y) - τ(y)τ(x) - τ([x,y])`. It is
bilinear, vanishes when `x=y`, and changes sign when the two arguments are exchanged.

The two adjacent-pair reductions of a three-letter word differ by `r([y,z],x) + r(y,[x,z]) +
r([x,y],z)`: Jacobi cancels the remaining degree-one term. With any `R`-basis, these errors
expand as finite linear combinations of basis-pair errors, also in fixed left and right tensor
contexts. Disjoint reductions commute by distributivity, and the enveloping quotient kills
every relation error.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "T" => TensorAlgebra R L
local notation "τ" => TensorAlgebra.ι R

/-- The defining enveloping relation error in the tensor algebra.

For `x,y ∈ L`, this is `τ(x)τ(y) - τ(y)τ(x) - τ([x,y])` in `T_R(L)`. -/
def relationError (x y : L) : T := τ x * τ y - τ y * τ x - τ ⁅x, y⁆

/-- The zero relation error on an equal pair.

For every `x ∈ L`, the tensor relation error `r(x,x)` is zero. -/
@[simp]
theorem relationError_self (x : L) : relationError R L x x = 0 := by
  simp only [relationError, lie_self, map_zero, sub_self]

/-- Skew symmetry of the tensor relation error.

For `x,y ∈ L`, the defining relation errors satisfy `r(x,y) = -r(y,x)`. -/
theorem relationError_swap (x y : L) :
    relationError R L x y = -relationError R L y x := by
  have h : τ ⁅x, y⁆ = -τ ⁅y, x⁆ := by
    rw [← lie_skew x y, map_neg]
  simp only [relationError, h]
  abel

/-- The relation error as a linear map in its second argument.

For fixed `x ∈ L`, the map `y ↦ τ(x)τ(y) - τ(y)τ(x) - τ([x,y])` is `R`-linear. -/
def relationErrorLinear (x : L) : L →ₗ[R] T where
  toFun y := relationError R L x y
  map_add' y z := by
    simp only [relationError, lie_add, map_add, mul_add, add_mul]
    abel
  map_smul' r y := by
    simp only [relationError, lie_smul, map_smul, mul_smul_comm,
      smul_mul_assoc, smul_sub, RingHom.id_apply]

/-- Evaluation of the second-variable relation map.

The linear map at fixed `x` has value `r(x,y)` at `y`. -/
@[simp]
theorem relationErrorLinear_apply (x y : L) :
    relationErrorLinear R L x y = relationError R L x y := rfl

/-- The bilinear tensor relation map.

The assignment `(x,y) ↦ τ(x)τ(y) - τ(y)τ(x) - τ([x,y])` is `R`-linear in each Lie argument. -/
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

/-- The basis expansion of a tensor relation error.

For an `R`-basis `b`, the error on `x,y` is the finite sum of basis-pair errors `r(b_i,b_j)`
with coefficients equal to the products of their coordinates in `x` and `y`. -/
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

/-- The left-first expansion of a three-letter enveloping reduction.

The expansion is `τ(z)τ(y)τ(x) + τ([y,z])τ(x) + τ(y)τ([x,z]) + τ([x,y])τ(z)`. -/
def overlapLeft (x y z : L) : T :=
  τ z * τ y * τ x + τ ⁅y, z⁆ * τ x + τ y * τ ⁅x, z⁆ + τ ⁅x, y⁆ * τ z

/-- The right-first expansion of a three-letter enveloping reduction.

The expansion is `τ(z)τ(y)τ(x) + τ(z)τ([x,y]) + τ([x,z])τ(y) + τ(x)τ([y,z])`. -/
def overlapRight (x y z : L) : T :=
  τ z * τ y * τ x + τ z * τ ⁅x, y⁆ + τ ⁅x, z⁆ * τ y + τ x * τ ⁅y, z⁆

/-- The Jacobi relation among overlapping reduction paths.

The left-first expansion minus the right-first expansion equals `r([y,z],x) + r(y,[x,z]) +
r([x,y],z)`; Jacobi removes the degree-one remainder. -/
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

/-- The linear tensor map given by fixed left and right factors.

For `p,s ∈ T_R(L)`, this `R`-linear map sends `a` to `p*a*s`. -/
def tensorContext (p s : T) : T →ₗ[R] T where
  toFun a := p * a * s
  map_add' a b := by simp only [mul_add, add_mul]
  map_smul' r a := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

/-- Generation of contextual relation errors by basis pairs.

For any basis `b`, a relation error multiplied by fixed tensor factors on the left and right
belongs to the span of the basis-pair errors in the same context. -/
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

/-- Generation of an overlap difference by contextual basis relations.

The difference of the two three-letter reduction expansions in a fixed tensor context belongs
to the span of the contextual basis-pair relation errors. -/
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

/-- Commutation of disjoint additive tensor reductions.

The four terms obtained by distributing two independent two-term reductions can be grouped by
either reduction order, giving the same tensor-algebra element. -/
theorem disjoint_reductions_commute (a b c d m : T) :
    ((a * m * c + a * m * d) + (b * m * c + b * m * d)) =
      ((a * m * c + b * m * c) + (a * m * d + b * m * d)) := by
  noncomm_ring

/-- The defining relation error in the enveloping quotient.

The tensor-algebra quotient map to `U_R(L)` sends every error `r(x,y)` to zero. -/
@[simp]
theorem mkAlgHom_relationError (x y : L) :
    mkAlgHom R L (relationError R L x y) = 0 := by
  simp only [relationError, map_sub, map_mul]
  change UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
      UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x -
        UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ = 0
  rw [ι_mul_sub_mul_ι, sub_self]

end UniversalEnvelopingAlgebra.PBW
