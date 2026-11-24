/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.Diagonal

/-!
# Coordinate projections on completed Hilbert-module direct sums

For any set of indices, the bounded diagonal with identity entries on that set
and zero entries elsewhere gives an adjointable projection on the literal
completed module sum. Its range is the closure of the complex span of the
selected coordinate inclusions. The component modules need not be complete,
and the index type may be infinite or empty.

For an integer-indexed family, the nonnegative cut includes degree zero.
The computed operator `2P - 1` is self-adjoint and squares to the identity.
This is the projection convention used in Arici, D'Andrea and Landi,
*Pimsner algebras and circle bundles*, §3.4, Definition 3.10. The construction
here works for arbitrary module families; tensor powers, the Fock creation
operators and Kasparov classes belong to their own constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace CStarModule.DirectSum

universe uB uI uE uX

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]

section Family

variable {I : Type uI} {E : I → Type uE}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)]

/-- Adjointable maps from the completed sum are determined by their coordinate values. -/
theorem adjointable_ext_completedSingle
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X]
    {S T : AdjointableOperator B (Completed B E) X}
    (h : ∀ i x, S (completedSingle (B := B) (E := E) i x) =
      T (completedSingle (B := B) (E := E) i x)) : S = T := by
  apply AdjointableOperator.toContinuousLinearMap_injective
  apply ContinuousLinearMap.ext_on (dense_span_completedSingle (B := B) (E := E))
  rintro _ ⟨⟨i, x⟩, rfl⟩
  exact h i x

/-- The actual bounded adjointable diagonal selecting a set of coordinates. -/
def cutProjection (s : Set I) : AdjointableOperator.End B (Completed B E) := by
  classical
  exact completedDiagonal
    (fun i ↦ if i ∈ s then (1 : AdjointableOperator.End B (E i)) else 0)
    ⟨1, zero_le_one, fun i ↦ by
      split_ifs
      · change ‖ContinuousLinearMap.id ℂ (E i)‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
      · simp⟩

open Classical in
/-- A cut keeps precisely its selected coordinates, including their original values. -/
theorem cutProjection_apply_completedSingle (s : Set I) (i : I) (x : E i) :
    cutProjection (B := B) (E := E) s (completedSingle i x) =
      if i ∈ s then completedSingle (B := B) (E := E) i x else 0 := by
  classical
  rw [cutProjection, completedDiagonal_apply_completedSingle]
  by_cases hi : i ∈ s <;>
    simp only [hi, ite_true, ite_false, AdjointableOperator.one_apply,
      AdjointableOperator.zero_apply, map_zero]

/-- The cut is self-adjoint on the actual completed sum. -/
@[simp]
theorem star_cutProjection (s : Set I) :
    star (cutProjection (B := B) (E := E) s) = cutProjection s := by
  classical
  apply adjointable_ext_completedSingle
  intro i x
  rw [AdjointableOperator.star_apply, cutProjection,
    completedDiagonal_adjoint_apply_completedSingle,
    completedDiagonal_apply_completedSingle]
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi]
    rfl
  · simp only [ite_eq_right hi]
    rfl

/-- Selecting no coordinates gives the zero operator. -/
@[simp]
theorem cutProjection_empty :
    cutProjection (B := B) (E := E) (∅ : Set I) = 0 := by
  apply adjointable_ext_completedSingle
  intro i x
  rw [cutProjection_apply_completedSingle]
  simp

/-- Selecting all coordinates gives the identity on the completion. -/
@[simp]
theorem cutProjection_univ :
    cutProjection (B := B) (E := E) (Set.univ : Set I) = 1 := by
  apply adjointable_ext_completedSingle
  intro i x
  rw [cutProjection_apply_completedSingle]
  simp

/-- Composition of cuts is the cut on the intersection. -/
@[simp]
theorem cutProjection_mul (s t : Set I) :
    cutProjection (B := B) (E := E) s * cutProjection t = cutProjection (s ∩ t) := by
  classical
  apply adjointable_ext_completedSingle
  intro i x
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp only [AdjointableOperator.mul_apply, cutProjection_apply_completedSingle,
      Set.mem_inter_iff, hs, ht, ite_true, ite_false,
      and_true, and_false, map_zero]

/-- The computed cut is idempotent. -/
theorem cutProjection_mul_self (s : Set I) :
    cutProjection (B := B) (E := E) s * cutProjection s = cutProjection s := by
  rw [cutProjection_mul, Set.inter_self]

/-- A coordinate cut is a star projection in the standard projection API. -/
theorem isStarProjection_cutProjection (s : Set I) :
    IsStarProjection (cutProjection (B := B) (E := E) s) :=
  ⟨cutProjection_mul_self s, star_cutProjection s⟩

/-- Every coordinate cut is contractive, also for an empty sum or zero modules. -/
theorem norm_cutProjection_le (s : Set I) :
    ‖cutProjection (B := B) (E := E) s‖ ≤ 1 :=
  IsStarProjection.norm_le _ (isStarProjection_cutProjection s)

/-- All coordinate cuts commute. -/
theorem cutProjection_comm (s t : Set I) :
    cutProjection (B := B) (E := E) s * cutProjection t =
      cutProjection t * cutProjection s := by
  rw [cutProjection_mul, cutProjection_mul, Set.inter_comm]

/-- Disjoint cuts have zero product. -/
theorem cutProjection_mul_of_disjoint {s t : Set I} (h : Disjoint s t) :
    cutProjection (B := B) (E := E) s * cutProjection t = 0 := by
  rw [cutProjection_mul, Set.disjoint_iff_inter_eq_empty.mp h, cutProjection_empty]

/-- A complementary cut is the complementary projection. -/
@[simp]
theorem cutProjection_compl (s : Set I) :
    cutProjection (B := B) (E := E) sᶜ = 1 - cutProjection s := by
  classical
  apply adjointable_ext_completedSingle
  intro i x
  by_cases hi : i ∈ s <;>
    simp only [sub_eq_add_neg, AdjointableOperator.add_apply,
      AdjointableOperator.neg_apply, AdjointableOperator.one_apply,
      cutProjection_apply_completedSingle, Set.mem_compl_iff, hi,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false, neg_zero,
      add_zero, add_neg_cancel]

/-- A union of cuts satisfies the inclusion-exclusion formula. -/
theorem cutProjection_union (s t : Set I) :
    cutProjection (B := B) (E := E) (s ∪ t) =
      cutProjection s + cutProjection t - cutProjection (s ∩ t) := by
  classical
  apply adjointable_ext_completedSingle
  intro i x
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp only [sub_eq_add_neg, AdjointableOperator.add_apply,
      AdjointableOperator.neg_apply, cutProjection_apply_completedSingle,
      Set.mem_union, Set.mem_inter_iff, hs, ht, ite_true, ite_false,
      and_true, and_false, or_true, or_false, add_zero, zero_add, neg_zero,
      add_assoc, add_neg_cancel]

/-- The complex linear span of the inclusions of the selected component modules. -/
def coordinateSpan (s : Set I) : Submodule ℂ (Completed B E) :=
  Submodule.span ℂ (Set.range fun p : Σ i : s, E i.1 ↦
    completedSingle (B := B) (E := E) p.1.1 p.2)

/-- The cut acts identically on the closure of its selected coordinate span. -/
theorem cutProjection_eq_self_of_mem_closure_coordinateSpan
    (s : Set I) {x : Completed B E}
    (hx : x ∈ closure (coordinateSpan (B := B) (E := E) s : Set (Completed B E))) :
    cutProjection s x = x := by
  apply ContinuousLinearMap.eqOn_closure_span
    (f := (cutProjection s).toContinuousLinearMap)
    (g := ContinuousLinearMap.id ℂ (Completed B E)) ?_ hx
  rintro _ ⟨⟨i, y⟩, rfl⟩
  exact (cutProjection_apply_completedSingle s i.1 y).trans (ite_eq_left i.2)

/-- Every cut value belongs to the closure of the selected coordinate span. -/
theorem cutProjection_mem_closure_coordinateSpan (s : Set I) (x : Completed B E) :
    cutProjection s x ∈
      closure (coordinateSpan (B := B) (E := E) s : Set (Completed B E)) := by
  classical
  let S := (coordinateSpan (B := B) (E := E) s).topologicalClosure
  have hspan : Submodule.span ℂ (Set.range fun p : Σ i, E i ↦
      completedSingle (B := B) (E := E) p.1 p.2) ≤
        S.comap (cutProjection s).toContinuousLinearMap.toLinearMap := by
    apply Submodule.span_le.2
    rintro _ ⟨⟨i, y⟩, rfl⟩
    change cutProjection s (completedSingle (B := B) (E := E) i y) ∈ S
    rw [cutProjection_apply_completedSingle]
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi]
      apply (coordinateSpan s).le_topologicalClosure
      exact Submodule.subset_span ⟨⟨⟨i, hi⟩, y⟩, rfl⟩
    · rw [ite_eq_right hi]
      exact S.zero_mem
  have hclosed : IsClosed
      (S.comap (cutProjection s).toContinuousLinearMap.toLinearMap : Set (Completed B E)) :=
    (Submodule.isClosed_topologicalClosure _).preimage
      (cutProjection s).toContinuousLinearMap.continuous
  exact closure_minimal hspan hclosed (dense_span_completedSingle (B := B) (E := E) x)

/-- The actual range is exactly the closure of the selected coordinate span. -/
theorem range_cutProjection (s : Set I) :
    Set.range (cutProjection (B := B) (E := E) s) =
      closure (coordinateSpan (B := B) (E := E) s : Set (Completed B E)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact cutProjection_mem_closure_coordinateSpan s y
  · intro hx
    exact ⟨x, cutProjection_eq_self_of_mem_closure_coordinateSpan s hx⟩

/-- The range of a coordinate cut is closed. -/
theorem isClosed_range_cutProjection (s : Set I) :
    IsClosed (Set.range (cutProjection (B := B) (E := E) s)) := by
  rw [range_cutProjection]
  exact isClosed_closure

/-- Disjoint cuts have orthogonal ranges for the coefficient-valued inner product. -/
theorem rightInner_cutProjection_of_disjoint {s t : Set I} (h : Disjoint s t)
    (x y : Completed B E) :
    rightInner (B := B) (cutProjection s x) (cutProjection t y) = 0 := by
  rw [(cutProjection s).adjoint_inner]
  have hzero : (cutProjection (B := B) (E := E) s).adjoint (cutProjection t y) = 0 := by
    change star (cutProjection s) (cutProjection t y) = 0
    rw [star_cutProjection, ← AdjointableOperator.mul_apply,
      cutProjection_mul_of_disjoint h]
    exact AdjointableOperator.zero_apply y
  rw [hzero, rightInner_zero_right]

/-- The computed reflection is positive on the selected coordinates and negative elsewhere. -/
def cutInvolution (s : Set I) : AdjointableOperator.End B (Completed B E) :=
  2 * cutProjection s - 1

open Classical in
/-- The reflection acts by the literal signs fixed by the chosen cut. -/
theorem cutInvolution_apply_completedSingle (s : Set I) (i : I) (x : E i) :
    cutInvolution (B := B) (E := E) s (completedSingle i x) =
      if i ∈ s then completedSingle (B := B) (E := E) i x
        else -completedSingle (B := B) (E := E) i x := by
  classical
  by_cases hi : i ∈ s <;>
    simp only [cutInvolution, two_mul, sub_eq_add_neg,
      AdjointableOperator.add_apply, AdjointableOperator.neg_apply,
      AdjointableOperator.one_apply, cutProjection_apply_completedSingle,
      hi, ite_true, ite_false, zero_add, add_assoc, add_neg_cancel, add_zero]

/-- The reflection `2P - 1` is self-adjoint. -/
@[simp]
theorem star_cutInvolution (s : Set I) :
    star (cutInvolution (B := B) (E := E) s) = cutInvolution s := by
  simp only [cutInvolution, two_mul, star_sub, star_add, star_cutProjection, star_one]

/-- The actual reflection squares to the identity on the completion. -/
@[simp]
theorem cutInvolution_mul_self (s : Set I) :
    cutInvolution (B := B) (E := E) s * cutInvolution s = 1 := by
  classical
  apply adjointable_ext_completedSingle
  intro i x
  by_cases hi : i ∈ s <;>
    simp only [AdjointableOperator.mul_apply, cutInvolution_apply_completedSingle,
      hi, ite_true, ite_false, map_neg, neg_neg, AdjointableOperator.one_apply]

end Family

section Integer

variable {E : ℤ → Type uE}
variable [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
  [∀ n, SMul Bᵐᵒᵖ (E n)] [∀ n, CStarModule Bᵐᵒᵖ (E n)]

/-- The actual projection onto nonnegative degrees, with degree zero included. -/
def nonnegativeProjection : AdjointableOperator.End B (Completed B E) :=
  cutProjection (Set.Ici (0 : ℤ))

/-- Nonnegative degrees keep their values; strictly negative degrees are killed. -/
theorem nonnegativeProjection_apply_completedSingle (n : ℤ) (x : E n) :
    nonnegativeProjection (B := B) (E := E)
      (completedSingle (B := B) (E := E) n x) =
      if 0 ≤ n then completedSingle (B := B) (E := E) n x else 0 := by
  classical
  simpa only [nonnegativeProjection, Set.mem_Ici] using
    (cutProjection_apply_completedSingle (B := B) (E := E) (Set.Ici (0 : ℤ)) n x)

/-- The nonnegative-degree projection is self-adjoint. -/
@[simp]
theorem star_nonnegativeProjection :
    star (nonnegativeProjection (B := B) (E := E)) = nonnegativeProjection :=
  star_cutProjection (Set.Ici (0 : ℤ))

/-- The nonnegative-degree projection is idempotent. -/
@[simp]
theorem nonnegativeProjection_mul_self :
    nonnegativeProjection (B := B) (E := E) * nonnegativeProjection =
      nonnegativeProjection :=
  cutProjection_mul_self (Set.Ici (0 : ℤ))

/-- The nonnegative-degree projection is contractive. -/
theorem norm_nonnegativeProjection_le :
    ‖nonnegativeProjection (B := B) (E := E)‖ ≤ 1 :=
  norm_cutProjection_le (Set.Ici (0 : ℤ))

/-- The range of the nonnegative projection is the closed span of its actual degrees. -/
theorem range_nonnegativeProjection :
    Set.range (nonnegativeProjection (B := B) (E := E)) =
      closure (coordinateSpan (B := B) (E := E) (Set.Ici (0 : ℤ)) :
        Set (Completed B E)) :=
  range_cutProjection (Set.Ici (0 : ℤ))

/-- The source's sign convention `2P - 1` on the integer-indexed completion. -/
def nonnegativeInvolution : AdjointableOperator.End B (Completed B E) :=
  2 * nonnegativeProjection - 1

/-- The boundary reflection is positive in degree zero and every positive degree. -/
theorem nonnegativeInvolution_apply_completedSingle (n : ℤ) (x : E n) :
    nonnegativeInvolution (B := B) (E := E)
      (completedSingle (B := B) (E := E) n x) =
      if 0 ≤ n then completedSingle (B := B) (E := E) n x
        else -completedSingle (B := B) (E := E) n x := by
  classical
  simpa only [nonnegativeInvolution, nonnegativeProjection, cutInvolution, Set.mem_Ici] using
    (cutInvolution_apply_completedSingle (B := B) (E := E) (Set.Ici (0 : ℤ)) n x)

/-- The nonnegative reflection is self-adjoint. -/
@[simp]
theorem star_nonnegativeInvolution :
    star (nonnegativeInvolution (B := B) (E := E)) = nonnegativeInvolution :=
  star_cutInvolution (Set.Ici (0 : ℤ))

/-- The nonnegative reflection squares to the identity. -/
@[simp]
theorem nonnegativeInvolution_mul_self :
    nonnegativeInvolution (B := B) (E := E) * nonnegativeInvolution = 1 :=
  cutInvolution_mul_self (Set.Ici (0 : ℤ))

end Integer

end CStarModule.DirectSum
