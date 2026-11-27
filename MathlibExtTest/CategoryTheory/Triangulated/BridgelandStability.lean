/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.Triangulated.BridgelandStability

@[expose] public section

/-! # Tests for Bridgeland stability data on a triangulated category

The general structures do not require a quiver, curve, surface or proper
variety. A zero charge cannot be a provider on a category with a nonzero
object.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open MathlibExt.CategoryTheory.BridgelandStability
open MathlibExt.CategoryTheory.TriangulatedGrothendieck
open scoped ZeroObject

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

-- A stability condition on a category with a nonzero object has nonzero charge.
example (s : StabilityCondition C) (E : C) (hE : ¬ IsZero E) : s.charge ≠ 0 := by
  intro hz
  exact hE (s.isZero_of_charge_zero hz E)

-- Numerical data forget to the general datum, with charge `Z ∘ v`.
example {rank : ℕ} (s : NumericalStabilityCondition C rank) (E : C) :
    s.toStabilityCondition.charge (classOf C E) = s.numerical.objectCharge E :=
  rfl

-- An HN filtration of a nonzero object has at least one piece.
example (P : SliceFamily C) (E : C) (hE : ¬ IsZero E) (F : HNFiltration C P E) :
    0 < F.length :=
  F.length_pos C hE

-- The numerical class and the charge of the zero object vanish.
example {rank : ℕ} (N : NumericalCharge C rank) : N.ofObject (0 : C) = 0 := by
  simp [NumericalCharge.ofObject]

example {rank : ℕ} (N : NumericalCharge C rank) : N.objectCharge (0 : C) = 0 := by
  simp [NumericalCharge.objectCharge, NumericalCharge.ofObject]

-- Shifting twice by one restores the numerical class and the charge.
example {rank : ℕ} (N : NumericalCharge C rank) (E : C) :
    N.ofObject (E⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) = N.ofObject E := by
  rw [N.ofObject_shift_one, N.ofObject_shift_one, neg_neg]

example {rank : ℕ} (N : NumericalCharge C rank) (E : C) :
    N.objectCharge (E⟦(1 : ℤ)⟧) + N.objectCharge E = 0 := by
  rw [N.objectCharge_shift_one, neg_add_cancel]

-- The lattice norm is the l¹ norm.
example : latticeNorm (fun i : Fin 2 ↦ if i = 0 then (3 : ℤ) else -4) = 7 := by
  simp [latticeNorm, Fin.sum_univ_two]
  norm_num

example (rank : ℕ) : latticeNorm (0 : Fin rank → ℤ) = 0 := by
  simp [latticeNorm]
