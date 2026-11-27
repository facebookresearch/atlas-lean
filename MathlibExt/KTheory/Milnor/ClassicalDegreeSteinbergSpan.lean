/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.DegreeSymbolGeneration

/-!
# Explicit degree-n Steinberg relation span

The set of degree-`n` tensors containing an adjacent factor `a ⊗ (1-a)`
with arbitrary unit prefix and suffix, and the submodule it spans.
Its elements lie in degree `n` and in the Steinberg ideal.

## Main definitions
* `TensorRing.steinbergInsertSet`
* `TensorRing.steinbergDegreeSpan`
* `steinbergDegreeSpanInDegree`

## Main results
* `steinbergDegreeSpan_le_degree`
* `steinbergDegreeSpan_mem_steinbergIdeal`
* `steinbergDegreeSpanInDegree_le_ker`
-/

@[expose] public section

open TensorAlgebra
open scoped TensorAlgebra Pointwise

namespace MilnorK

variable (F : Type*) [Field F]

namespace TensorRing

/-- The set of degree-`n` tensor words containing a Steinberg pair
`a ⊗ (1-a)` in adjacent positions, with arbitrary prefix and suffix lists of units. -/
def steinbergInsertSet (n : ℕ) : Set (TensorRing F) :=
  { x |
    ∃ (xs ys : List Fˣ) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1),
      xs.length + ys.length + 2 = n ∧
      x = tensorList F xs *
        (TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 a ha0)) *
          TensorAlgebra.ι ℤ (Additive.ofMul
            (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)))) *
        tensorList F ys }

/-- `ℤ`-submodule spanned by degree-`n` Steinberg insertions. -/
def steinbergDegreeSpan (n : ℕ) : Submodule ℤ (TensorRing F) :=
  Submodule.span ℤ (steinbergInsertSet F n)

/-- A single Steinberg insertion lies in tensor degree `n`. -/
theorem steinbergInsert_mem_degree {n : ℕ} {x : TensorRing F}
    (hx : x ∈ steinbergInsertSet F n) : x ∈ TensorRing.degree F n := by
  rcases hx with ⟨xs, ys, a, ha0, ha1, hlen, rfl⟩
  have hxs : tensorList F xs ∈ TensorRing.degree F xs.length :=
    tensorList_mem_degree F xs
  have hys : tensorList F ys ∈ TensorRing.degree F ys.length :=
    tensorList_mem_degree F ys
  have hpair : TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 a ha0)) *
      TensorAlgebra.ι ℤ (Additive.ofMul
        (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)))
      ∈ TensorRing.degree F 2 :=
    ι_mul_ι_mem_degree_two F _ _
  have h_left : tensorList F xs *
      (TensorAlgebra.ι ℤ _ * TensorAlgebra.ι ℤ _) ∈
      TensorRing.degree F (xs.length + 2) :=
    SetLike.GradedMul.mul_mem hxs hpair
  have h_total : tensorList F xs *
      (TensorAlgebra.ι ℤ _ * TensorAlgebra.ι ℤ _) *
      tensorList F ys ∈
      TensorRing.degree F (xs.length + 2 + ys.length) :=
    SetLike.GradedMul.mul_mem h_left hys
  have h_eq1 : xs.length + 2 + ys.length = xs.length + ys.length + 2 := by
    ac_rfl
  have h_eq2 : xs.length + ys.length + 2 = n := hlen
  rw [h_eq1] at h_total
  rw [h_eq2] at h_total
  simpa [mul_assoc] using h_total

/-- The explicit Steinberg span is contained in tensor degree `n`. -/
theorem steinbergDegreeSpan_le_degree (n : ℕ) :
    steinbergDegreeSpan F n ≤ TensorRing.degree F n := by
  rw [steinbergDegreeSpan, Submodule.span_le]
  intro x hx
  exact steinbergInsert_mem_degree F hx

/-- A single Steinberg insertion lies in the Steinberg ideal. -/
theorem steinbergInsert_mem_steinbergIdeal {n : ℕ} {x : TensorRing F}
    (hx : x ∈ steinbergInsertSet F n) : x ∈ steinbergIdeal F := by
  rcases hx with ⟨xs, ys, a, ha0, ha1, hlen, rfl⟩
  have hgen : TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 a ha0)) *
      TensorAlgebra.ι ℤ (Additive.ofMul
        (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)))
      ∈ steinbergIdeal F :=
    MilnorKRing.steinberg_mem F a ha0 ha1
  have h_left : tensorList F xs *
      (TensorAlgebra.ι ℤ _ * TensorAlgebra.ι ℤ _) ∈ steinbergIdeal F :=
    TwoSidedIdeal.mul_mem_left (steinbergIdeal F) (tensorList F xs)
      (TensorAlgebra.ι ℤ _ * TensorAlgebra.ι ℤ _) hgen
  have h_total : tensorList F xs *
      (TensorAlgebra.ι ℤ _ * TensorAlgebra.ι ℤ _) *
      tensorList F ys ∈ steinbergIdeal F :=
    TwoSidedIdeal.mul_mem_right (steinbergIdeal F)
      (tensorList F xs * (TensorAlgebra.ι ℤ _ * TensorAlgebra.ι ℤ _))
      (tensorList F ys) h_left
  simpa [mul_assoc] using h_total

/-- The explicit span is contained in the Steinberg ideal. -/
theorem steinbergDegreeSpan_mem_steinbergIdeal {n : ℕ} {x : TensorRing F}
    (hx : x ∈ steinbergDegreeSpan F n) : x ∈ steinbergIdeal F := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact steinbergInsert_mem_steinbergIdeal F hy
  | zero => exact TwoSidedIdeal.zero_mem _
  | add y z _ _ hyI hzI => exact TwoSidedIdeal.add_mem _ hyI hzI
  | smul c y _ hyI => exact (steinbergIdeal F).zsmul_mem c hyI

end TensorRing

open TensorRing

/-- Explicit Steinberg span viewed as a submodule of `TensorRing.degree F n`
via comap along the subtype inclusion. -/
def steinbergDegreeSpanInDegree (n : ℕ) :
    Submodule ℤ (TensorRing.degree F n) :=
  Submodule.comap (TensorRing.degree F n).subtype (steinbergDegreeSpan F n)

/-- The explicit span lies in the kernel of the degreewise projection. -/
theorem steinbergDegreeSpanInDegree_le_ker (n : ℕ) :
    steinbergDegreeSpanInDegree F n ≤ LinearMap.ker (MilnorKRing.degreeLinear F n) := by
  intro x hx
  dsimp [steinbergDegreeSpanInDegree] at hx
  rw [Submodule.mem_comap] at hx
  have h_ideal : x.val ∈ steinbergIdeal F :=
    steinbergDegreeSpan_mem_steinbergIdeal (F := F) hx
  rw [MilnorKRing.degreeLinear_ker F n]
  rw [Submodule.mem_comap]
  rw [Submodule.restrictScalars_mem, TwoSidedIdeal.mem_asIdeal]
  exact h_ideal

end MilnorK
