/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas
public import Mathlib.Order.TransfiniteIteration

/-!
# Bounded filtered subdiagrams closed under actual constraints

The native sharply-smaller-cardinal theorem enlarges a bounded subset to a
filtered bounded subset. Compatibility conditions impose additional finite
constraint functions on its indices. This file closes under those actual
functions while retaining filteredness and the larger cardinal bound.

The construction iterates for the original smaller regular ordinal. It does
not replace a diagram by a caller-supplied compatible presentation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uσ

open CategoryTheory

namespace CategoryTheory.Presentable.BoundedDiagramClosure

variable {μ κ : Cardinal.{w}} [Fact μ.IsRegular] [Fact κ.IsRegular]
variable {X : Type w}
variable {σ : Type uσ}

/-- Add the outputs of the specified finite constraint functions on existing indices. -/
def constraintStep (ops : σ → List X → X) (A : Set X) : Set X :=
  A ∪ Set.range (fun p : σ × List A => ops p.1 (p.2.map Subtype.val))

theorem subset_constraintStep (ops : σ → List X → X) (A : Set X) :
    A ⊆ constraintStep ops A := Set.subset_union_left

theorem mem_constraintStep (ops : σ → List X → X) (A : Set X)
    (s : σ) (xs : List A) : ops s (xs.map Subtype.val) ∈ constraintStep ops A :=
  Or.inr ⟨⟨s, xs⟩, rfl⟩

omit [Fact κ.IsRegular] in
private theorem list_small (hκ : Cardinal.aleph0 < κ) (A : Set X)
    (hA : HasCardinalLT A κ) : HasCardinalLT (List A) κ := by
  rw [hasCardinalLT_iff_cardinal_mk_lt] at hA ⊢
  exact (Cardinal.mk_list_le_max A).trans_lt (max_lt hκ hA)

omit [Fact κ.IsRegular] in
theorem constraintStep_small (hκ : Cardinal.aleph0 < κ)
    (ops : σ → List X → X) (hσ : HasCardinalLT σ κ) (A : Set X)
    (hA : HasCardinalLT A κ) : HasCardinalLT (constraintStep ops A) κ := by
  apply hasCardinalLT_union hκ.le hA
  exact (hasCardinalLT_prod hκ.le hσ (list_small hκ A hA)).of_surjective _
    (Set.rangeFactorization_surjective (f := fun p : σ × List A =>
      ops p.1 (p.2.map Subtype.val)))

section Construction

variable [PartialOrder X] [IsCardinalFiltered X μ]
variable (h : μ.SharplyLT κ) (ops : σ → List X → X) (hσ : HasCardinalLT σ κ)

include h in
private theorem uncountable : Cardinal.aleph0 < κ :=
  lt_of_le_of_lt (Cardinal.IsRegular.aleph0_le (Fact.out : μ.IsRegular)) h.lt

open Classical in
/-- The native bounded filtered enlargement of the actual constraint outputs. -/
private def enlargement (A : Set X) : Set X :=
  if hA : HasCardinalLT A κ then
    (h.exists_isCardinalFiltered_set (constraintStep ops A)
      (constraintStep_small (uncountable h) ops hσ A hA)).choose
  else A

private theorem enlargement_spec (A : Set X) (hA : HasCardinalLT A κ) :
    constraintStep ops A ⊆ enlargement h ops hσ A ∧
      IsCardinalFiltered (enlargement h ops hσ A) μ ∧
      HasCardinalLT (enlargement h ops hσ A) κ := by
  unfold enlargement
  rw [dite_eq_left hA]
  exact (h.exists_isCardinalFiltered_set (constraintStep ops A)
    (constraintStep_small (uncountable h) ops hσ A hA)).choose_spec

private theorem subset_enlargement (A : Set X) : A ⊆ enlargement h ops hσ A := by
  by_cases hA : HasCardinalLT A κ
  · exact (subset_constraintStep ops A).trans (enlargement_spec h ops hσ A hA).1
  · simp [enlargement, hA]

private def stage (A : Set X) (j : μ.ord.ToType) : Set X :=
  supTransfiniteIterate (enlargement h ops hσ) j A

private theorem stage_small (A : Set X) (hA : HasCardinalLT A κ) (j : μ.ord.ToType) :
    HasCardinalLT (stage h ops hσ A j) κ := by
  have : Nonempty μ.ord.ToType := Cardinal.nonempty_ord_toType
    (c := μ) (Cardinal.IsRegular.ne_zero Fact.out)
  let : OrderBot μ.ord.ToType := WellFoundedLT.toOrderBot _
  induction j using SuccOrder.limitRecOn with
  | isMin j hj => simpa only [stage, supTransfiniteIterate_of_isMin _ _ hj] using hA
  | succ j hj ih =>
    rw [stage, supTransfiniteIterate_succ_of_not_isMax _ _ hj]
    exact (enlargement_spec h ops hσ _ ih).2.2
  | isSuccLimit j hj ih =>
    rw [stage, supTransfiniteIterate_limit _ _ hj, Set.iSup_eq_iUnion]
    apply hasCardinalLT_iUnion
    · apply HasCardinalLT.of_injective _ _ Subtype.val_injective
      simpa [hasCardinalLT_iff_cardinal_mk_lt] using h.lt
    · rintro ⟨k, hk⟩
      exact ih k hk

private theorem stage_monotone (A : Set X) : Monotone (stage h ops hσ A) := by
  have : Nonempty μ.ord.ToType := Cardinal.nonempty_ord_toType
    (c := μ) (Cardinal.IsRegular.ne_zero Fact.out)
  let : OrderBot μ.ord.ToType := WellFoundedLT.toOrderBot _
  exact supTransfiniteIterate_monotone _ (subset_enlargement h ops hσ)

private theorem stage_succ (A : Set X) (j : μ.ord.ToType) :
    stage h ops hσ A (Order.succ j) = enlargement h ops hσ (stage h ops hσ A j) := by
  have : NoMaxOrder μ.ord.ToType := Cardinal.noMaxOrder
    (Cardinal.IsRegular.aleph0_le (Fact.out : μ.IsRegular))
  exact supTransfiniteIterate_succ _ _ j

include h hσ in
/-- Produce bounded filtered indices satisfying every specified finite constraint. -/
theorem exists_closed_bounded_filtered_set (A : Set X) (hA : HasCardinalLT A κ) :
    ∃ (B : Set X), A ⊆ B ∧ IsCardinalFiltered B μ ∧ HasCardinalLT B κ ∧
      ∀ (s : σ) (xs : List B), ops s (xs.map Subtype.val) ∈ B := by
  classical
  have : Nonempty μ.ord.ToType := Cardinal.nonempty_ord_toType
    (c := μ) (Cardinal.IsRegular.ne_zero Fact.out)
  let : OrderBot μ.ord.ToType := WellFoundedLT.toOrderBot _
  let B : Set X := ⋃ (j : μ.ord.ToType), stage h ops hσ A j
  have ha (x : B) : ∃ (j : μ.ord.ToType), x.val ∈ stage h ops hσ A j := by
    simpa only [B, Set.mem_iUnion] using x.property
  choose a ha using ha
  have hμ : Cardinal.aleph0 ≤ μ := Cardinal.IsRegular.aleph0_le Fact.out
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply Set.mem_iUnion.mpr
    exact ⟨⊥, by simpa [stage] using hx⟩
  · apply isCardinalFiltered_preorder
    intro T f hT
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hT
    let j := IsCardinalFiltered.max (fun t => a (f t)) hT
    have hf (t : T) : (f t).val ∈ stage h ops hσ A j :=
      stage_monotone h ops hσ A
        (leOfHom (IsCardinalFiltered.toMax (fun t => a (f t)) hT t)) (ha (f t))
    have he := enlargement_spec h ops hσ _ (stage_small h ops hσ A hA j)
    have : IsCardinalFiltered (enlargement h ops hσ (stage h ops hσ A j)) μ := he.2.1
    let f' (t : T) : enlargement h ops hσ (stage h ops hσ A j) :=
      ⟨(f t).val, subset_enlargement h ops hσ _ (hf t)⟩
    let z := IsCardinalFiltered.max f' hT
    refine ⟨⟨z.val, Set.mem_iUnion.mpr ⟨Order.succ j, ?_⟩⟩, fun t => ?_⟩
    · rw [stage_succ]
      exact z.property
    · exact leOfHom (IsCardinalFiltered.toMax f' hT t)
  · exact hasCardinalLT_iUnion _
      (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using h.lt)
      (stage_small h ops hσ A hA)
  · intro s xs
    let j := IsCardinalFiltered.max (fun i : Fin xs.length => a (xs.get i))
      (hasCardinalLT_of_finite _ μ hμ)
    have hx (x : B) (hx : x ∈ xs) : x.val ∈ stage h ops hσ A j := by
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
      exact stage_monotone h ops hσ A
        (leOfHom (IsCardinalFiltered.toMax (fun i : Fin xs.length => a (xs.get i))
          (hasCardinalLT_of_finite _ μ hμ) i)) (ha (xs.get i))
    let ys : List (stage h ops hσ A j) :=
      xs.attach.map (fun x => ⟨x.val.val, hx x.val x.property⟩)
    have hys : ys.map Subtype.val = xs.map Subtype.val := by
      dsimp only [ys]
      rw [List.map_map]
      change xs.attach.map (Subtype.val ∘ Subtype.val) = xs.map Subtype.val
      rw [← List.map_map, List.attach_map_subtype_val]
    apply Set.mem_iUnion.mpr
    refine ⟨Order.succ j, ?_⟩
    rw [stage_succ, ← hys]
    exact (enlargement_spec h ops hσ _ (stage_small h ops hσ A hA j)).1
      (mem_constraintStep ops _ s ys)

end Construction

end CategoryTheory.Presentable.BoundedDiagramClosure
