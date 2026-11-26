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
# Coordinate cuts on completed Hilbert-module sums

For right pre-Hilbert modules `E_i` over nonunital `B` and any set `s` of indices, the
adjointable projection `P_s` keeps the inclusions `j_i x` for `i ∈ s` and kills them otherwise.
It satisfies `P_s* = P_s`, `P_s² = P_s` and `‖P_s‖ ≤ 1`; its range is the closure of the complex
span of the selected coordinate ranges. The fibers may be incomplete and the index type empty.

Cuts obey `P_s P_t = P_(s ∩ t)`, `P_(sᶜ) = 1-P_s` and `P_(s ∪ t) = P_s+P_t-P_(s ∩ t)`. The
reflection `F_s = 2P_s-1` is self-adjoint and squares to `1`. For integer indices, `P_+` selects
`n ≥ 0`, including degree zero, and `F_+` has sign `+1` there and `-1` for `n < 0`. This is the
cut convention in Arici, D'Andrea and Landi, Pimsner algebras and circle bundles, Section 3.4,
Definition 3.10.
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

/-- **Determination by completed coordinates.** Two adjointable maps from `Completed B E` are
equal if they agree on every vector `completedSingle i x`. -/
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

/-- **Projection onto a selected coordinate set.** For `s : Set I`, `cutProjection s` is the
adjointable diagonal with identity in coordinates of `s` and zero elsewhere, on the completed
direct sum. -/
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
/-- **Coordinate action of a cut projection.** `P_s (j_i x) = j_i x` when `i ∈ s`, and `P_s (j_i
x) = 0` otherwise. -/
theorem cutProjection_apply_completedSingle (s : Set I) (i : I) (x : E i) :
    cutProjection (B := B) (E := E) s (completedSingle i x) =
      if i ∈ s then completedSingle (B := B) (E := E) i x else 0 := by
  classical
  rw [cutProjection, completedDiagonal_apply_completedSingle]
  by_cases hi : i ∈ s <;>
    simp only [hi, ite_true, ite_false, AdjointableOperator.one_apply,
      AdjointableOperator.zero_apply, map_zero]

/-- **Self-adjoint coordinate cut.** `star (cutProjection s) = cutProjection s`. -/
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

/-- **Cut on the empty set.** Selecting no coordinates gives `cutProjection ∅ = 0`. -/
@[simp]
theorem cutProjection_empty :
    cutProjection (B := B) (E := E) (∅ : Set I) = 0 := by
  apply adjointable_ext_completedSingle
  intro i x
  rw [cutProjection_apply_completedSingle]
  simp

/-- **Cut on every coordinate.** Selecting all coordinates gives `cutProjection Set.univ = 1` on
the completed sum. -/
@[simp]
theorem cutProjection_univ :
    cutProjection (B := B) (E := E) (Set.univ : Set I) = 1 := by
  apply adjointable_ext_completedSingle
  intro i x
  rw [cutProjection_apply_completedSingle]
  simp

/-- **Composition of coordinate cuts.** `cutProjection s * cutProjection t = cutProjection (s ∩
t)`. -/
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

/-- **Idempotence of a coordinate cut.** `cutProjection s * cutProjection s = cutProjection s`. -/
theorem cutProjection_mul_self (s : Set I) :
    cutProjection (B := B) (E := E) s * cutProjection s = cutProjection s := by
  rw [cutProjection_mul, Set.inter_self]

/-- **Star projection of a coordinate set.** `cutProjection s` is an `IsStarProjection`, being
self-adjoint and idempotent. -/
theorem isStarProjection_cutProjection (s : Set I) :
    IsStarProjection (cutProjection (B := B) (E := E) s) :=
  ⟨cutProjection_mul_self s, star_cutProjection s⟩

/-- **Norm bound for coordinate cuts.** `‖cutProjection s‖ ≤ 1` for any index set, including an
empty direct sum or zero component modules. -/
theorem norm_cutProjection_le (s : Set I) :
    ‖cutProjection (B := B) (E := E) s‖ ≤ 1 :=
  IsStarProjection.norm_le _ (isStarProjection_cutProjection s)

/-- **Commutation of coordinate cuts.** `cutProjection s * cutProjection t = cutProjection t *
cutProjection s` for any `s,t`. -/
theorem cutProjection_comm (s t : Set I) :
    cutProjection (B := B) (E := E) s * cutProjection t =
      cutProjection t * cutProjection s := by
  rw [cutProjection_mul, cutProjection_mul, Set.inter_comm]

/-- **Disjoint coordinate cuts.** If `s,t` are disjoint, `cutProjection s * cutProjection t = 0`. -/
theorem cutProjection_mul_of_disjoint {s t : Set I} (h : Disjoint s t) :
    cutProjection (B := B) (E := E) s * cutProjection t = 0 := by
  rw [cutProjection_mul, Set.disjoint_iff_inter_eq_empty.mp h, cutProjection_empty]

/-- **Complementary coordinate projection.** `cutProjection sᶜ = 1 - cutProjection s`. -/
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

/-- **Union of coordinate projections.** `cutProjection (s ∪ t) = cutProjection s + cutProjection
t - cutProjection (s ∩ t)`. -/
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

/-- **Span of selected coordinate ranges.** `coordinateSpan s` is the complex submodule spanned by
`completedSingle i x` for `i ∈ s` and `x : E i`. -/
def coordinateSpan (s : Set I) : Submodule ℂ (Completed B E) :=
  Submodule.span ℂ (Set.range fun p : Σ i : s, E i.1 ↦
    completedSingle (B := B) (E := E) p.1.1 p.2)

/-- **Identity on the closed selected-coordinate span.** If `x` lies in the norm closure of
`coordinateSpan s`, then `cutProjection s x = x`. -/
theorem cutProjection_eq_self_of_mem_closure_coordinateSpan
    (s : Set I) {x : Completed B E}
    (hx : x ∈ closure (coordinateSpan (B := B) (E := E) s : Set (Completed B E))) :
    cutProjection s x = x := by
  apply ContinuousLinearMap.eqOn_closure_span
    (f := (cutProjection s).toContinuousLinearMap)
    (g := ContinuousLinearMap.id ℂ (Completed B E)) ?_ hx
  rintro _ ⟨⟨i, y⟩, rfl⟩
  exact (cutProjection_apply_completedSingle s i.1 y).trans (ite_eq_left i.2)

/-- **Cut values in the selected-coordinate closure.** Every `cutProjection s x` belongs to the
closure of `coordinateSpan s`. -/
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

/-- **Range of a coordinate cut.** `Set.range (cutProjection s)` equals the norm closure of
`coordinateSpan s`. -/
theorem range_cutProjection (s : Set I) :
    Set.range (cutProjection (B := B) (E := E) s) =
      closure (coordinateSpan (B := B) (E := E) s : Set (Completed B E)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact cutProjection_mem_closure_coordinateSpan s y
  · intro hx
    exact ⟨x, cutProjection_eq_self_of_mem_closure_coordinateSpan s hx⟩

/-- **Closed range of a coordinate cut.** The range of `cutProjection s` is closed in the
completed-module norm topology. -/
theorem isClosed_range_cutProjection (s : Set I) :
    IsClosed (Set.range (cutProjection (B := B) (E := E) s)) := by
  rw [range_cutProjection]
  exact isClosed_closure

/-- **Orthogonality of disjoint cuts.** For disjoint `s,t` and completed vectors `x,y`,
`rightInner (cutProjection s x) (cutProjection t y) = 0`. -/
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

/-- **Reflection of a coordinate cut.** `cutInvolution s = 2 * cutProjection s - 1`, with sign
`+1` on selected coordinates and `-1` elsewhere. -/
def cutInvolution (s : Set I) : AdjointableOperator.End B (Completed B E) :=
  2 * cutProjection s - 1

open Classical in
/-- **Coordinate signs of a cut reflection.** `F_s (j_i x) = j_i x` for `i ∈ s` and `F_s (j_i x) =
-j_i x` otherwise, where `F_s = cutInvolution s`. -/
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

/-- **Self-adjoint cut reflection.** `star (cutInvolution s) = cutInvolution s`. -/
@[simp]
theorem star_cutInvolution (s : Set I) :
    star (cutInvolution (B := B) (E := E) s) = cutInvolution s := by
  simp only [cutInvolution, two_mul, star_sub, star_add, star_cutProjection, star_one]

/-- **Square of a cut reflection.** `cutInvolution s * cutInvolution s = 1` on the completed
direct sum. -/
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

/-- **Projection onto nonnegative degrees.** For an integer-indexed family, select the coordinate
set `{n : ℤ | 0 ≤ n}`, including degree zero. -/
def nonnegativeProjection : AdjointableOperator.End B (Completed B E) :=
  cutProjection (Set.Ici (0 : ℤ))

/-- **Coordinate action of the nonnegative cut.** `P_+ (j_n x) = j_n x` when `n ≥ 0` and equals
zero when `n < 0`. -/
theorem nonnegativeProjection_apply_completedSingle (n : ℤ) (x : E n) :
    nonnegativeProjection (B := B) (E := E)
      (completedSingle (B := B) (E := E) n x) =
      if 0 ≤ n then completedSingle (B := B) (E := E) n x else 0 := by
  classical
  simpa only [nonnegativeProjection, Set.mem_Ici] using
    (cutProjection_apply_completedSingle (B := B) (E := E) (Set.Ici (0 : ℤ)) n x)

/-- **Self-adjoint nonnegative cut.** `star nonnegativeProjection = nonnegativeProjection`. -/
@[simp]
theorem star_nonnegativeProjection :
    star (nonnegativeProjection (B := B) (E := E)) = nonnegativeProjection :=
  star_cutProjection (Set.Ici (0 : ℤ))

/-- **Idempotence of the nonnegative cut.** `nonnegativeProjection * nonnegativeProjection =
nonnegativeProjection`. -/
@[simp]
theorem nonnegativeProjection_mul_self :
    nonnegativeProjection (B := B) (E := E) * nonnegativeProjection =
      nonnegativeProjection :=
  cutProjection_mul_self (Set.Ici (0 : ℤ))

/-- **Norm bound for the nonnegative cut.** `‖nonnegativeProjection‖ ≤ 1`. -/
theorem norm_nonnegativeProjection_le :
    ‖nonnegativeProjection (B := B) (E := E)‖ ≤ 1 :=
  norm_cutProjection_le (Set.Ici (0 : ℤ))

/-- **Range of the nonnegative-degree projection.** The range of `P_+` is the norm closure of the
complex span of inclusions `j_n(E_n)` for `n ≥ 0`. -/
theorem range_nonnegativeProjection :
    Set.range (nonnegativeProjection (B := B) (E := E)) =
      closure (coordinateSpan (B := B) (E := E) (Set.Ici (0 : ℤ)) :
        Set (Completed B E)) :=
  range_cutProjection (Set.Ici (0 : ℤ))

/-- **Nonnegative-degree reflection.** `nonnegativeInvolution = 2 * nonnegativeProjection - 1`,
giving sign `+1` in degree zero and positive degrees and sign `-1` in negative degrees. -/
def nonnegativeInvolution : AdjointableOperator.End B (Completed B E) :=
  2 * nonnegativeProjection - 1

/-- **Coordinate signs of the nonnegative reflection.** `F_+ (j_n x) = j_n x` for `n ≥ 0` and `F_+
(j_n x) = -j_n x` for `n < 0`. -/
theorem nonnegativeInvolution_apply_completedSingle (n : ℤ) (x : E n) :
    nonnegativeInvolution (B := B) (E := E)
      (completedSingle (B := B) (E := E) n x) =
      if 0 ≤ n then completedSingle (B := B) (E := E) n x
        else -completedSingle (B := B) (E := E) n x := by
  classical
  simpa only [nonnegativeInvolution, nonnegativeProjection, cutInvolution, Set.mem_Ici] using
    (cutInvolution_apply_completedSingle (B := B) (E := E) (Set.Ici (0 : ℤ)) n x)

/-- **Self-adjoint nonnegative reflection.**
`star nonnegativeInvolution = nonnegativeInvolution`. -/
@[simp]
theorem star_nonnegativeInvolution :
    star (nonnegativeInvolution (B := B) (E := E)) = nonnegativeInvolution :=
  star_cutInvolution (Set.Ici (0 : ℤ))

/-- **Square of the nonnegative reflection.**
`nonnegativeInvolution * nonnegativeInvolution = 1`. -/
@[simp]
theorem nonnegativeInvolution_mul_self :
    nonnegativeInvolution (B := B) (E := E) * nonnegativeInvolution = 1 :=
  cutInvolution_mul_self (Set.Ici (0 : ℤ))

end Integer

end CStarModule.DirectSum
