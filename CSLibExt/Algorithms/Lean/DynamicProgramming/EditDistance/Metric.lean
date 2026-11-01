/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm

/-!
# Unit-cost edit distance is a metric

Levenshtein distance with unit-cost insertions, deletions and substitutions is a metric on
lists (Navarro 2001, §2): every operation has an inverse of the same cost, which gives symmetry,
and scripts compose, which gives the triangle inequality. Together with `editDistance_self` and
`editDistance_eq_zero_iff` from `EditDistance.Algorithm` these are the metric axioms for
`d x y = (editDistance x y).ret.distance`.

## Main results

* `EditScript.exists_inverse`: every script has an inverse script of the same cost.
* `EditScript.exists_compose`: two scripts compose into one costing at most their sum.
* `editDistance_comm`: symmetry.
* `editDistance_triangle`: the triangle inequality.
* `editDistance_pos_iff`: positivity off the diagonal.

Not covered: the conditional lower bound of Backurs and Indyk (2015) that edit distance has no
strongly subquadratic algorithm unless the Strong Exponential Time Hypothesis fails; the
repository has no fine-grained complexity framework in which to state it.

## References

* V. I. Levenshtein, *Binary codes capable of correcting deletions, insertions, and reversals*,
  Soviet Physics Doklady 10 (1966), 707–710.
* R. A. Wagner and M. J. Fischer, *The string-to-string correction problem*, J. ACM 21 (1974).
* G. Navarro, *A guided tour to approximate string matching*, ACM Comput. Surv. 33 (2001),
  31–88.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

private inductive Execution {α : Type u} : EditScript α → List α → List α → Prop where
  | nil : Execution [] [] []
  | keep (a : α) {s : EditScript α} {x y : List α} :
      Execution s x y → Execution (.keep a :: s) (a :: x) (a :: y)
  | delete (a : α) {s : EditScript α} {x y : List α} :
      Execution s x y → Execution (.delete a :: s) (a :: x) y
  | insert (a : α) {s : EditScript α} {x y : List α} :
      Execution s x y → Execution (.insert a :: s) x (a :: y)
  | substitute (a b : α) {s : EditScript α} {x y : List α} :
      Execution s x y → Execution (.substitute a b :: s) (a :: x) (b :: y)

private theorem Execution.transforms {α : Type u} [BEq α] [LawfulBEq α]
    {s : EditScript α} {x y : List α} (h : Execution s x y) : s.Transforms x y := by
  induction h <;> simp_all [EditScript.Transforms, EditScript.apply?]

private theorem Execution.of_transforms {α : Type u} [BEq α] [LawfulBEq α]
    {s : EditScript α} {x y : List α} (h : s.Transforms x y) : Execution s x y := by
  unfold EditScript.Transforms at h
  induction s generalizing x y with
  | nil =>
      cases x with
      | nil =>
          simp only [EditScript.apply?, Option.some.injEq] at h
          subst y
          exact .nil
      | cons a x => simp [EditScript.apply?] at h
  | cons step s ih =>
      cases step with
      | keep a =>
          cases x with
          | nil => simp [EditScript.apply?] at h
          | cons b x =>
              simp only [EditScript.apply?, beq_iff_eq] at h
              split at h
              next hab =>
                have hab' : a = b := beq_iff_eq.mp hab
                subst b
                cases he : EditScript.apply? s x with
                | none => simp [he] at h
                | some z =>
                    simp only [he, Option.map_some, Option.some.injEq] at h
                    subst y
                    exact .keep a (ih he)
              next => simp at h
      | delete a =>
          cases x with
          | nil => simp [EditScript.apply?] at h
          | cons b x =>
              simp only [EditScript.apply?, beq_iff_eq] at h
              split at h
              next hab =>
                have hab' : a = b := beq_iff_eq.mp hab
                subst b
                exact .delete a (ih h)
              next => simp at h
      | insert a =>
          simp only [EditScript.apply?] at h
          cases he : EditScript.apply? s x with
          | none => simp [he] at h
          | some z =>
              simp only [he, Option.map_some, Option.some.injEq] at h
              subst y
              exact .insert a (ih he)
      | substitute a b =>
          cases x with
          | nil => simp [EditScript.apply?] at h
          | cons c x =>
              simp only [EditScript.apply?, beq_iff_eq] at h
              split at h
              next hac =>
                have hac' : a = c := beq_iff_eq.mp hac
                subst c
                cases he : EditScript.apply? s x with
                | none => simp [he] at h
                | some z =>
                    simp only [he, Option.map_some, Option.some.injEq] at h
                    subst y
                    exact .substitute a b (ih he)
              next => simp at h

/-- Every script has an inverse of the same cost (swap insertions and deletions, reverse
substitutions). -/
theorem EditScript.exists_inverse [BEq α] [LawfulBEq α] {script : EditScript α}
    {source target : List α} (h : script.Transforms source target) :
    ∃ inverse : EditScript α, inverse.Transforms target source ∧
      inverse.cost = script.cost := by
  have he := Execution.of_transforms h
  clear h
  induction he with
  | nil => exact ⟨[], Execution.nil.transforms, rfl⟩
  | keep a he ih =>
      obtain ⟨s, hs, hc⟩ := ih
      exact ⟨.keep a :: s, (Execution.keep a (Execution.of_transforms hs)).transforms,
        by simpa [EditScript.cost, EditStep.cost] using hc⟩
  | delete a he ih =>
      obtain ⟨s, hs, hc⟩ := ih
      exact ⟨.insert a :: s, (Execution.insert a (Execution.of_transforms hs)).transforms,
        by simp [EditScript.cost, EditStep.cost, hc]⟩
  | insert a he ih =>
      obtain ⟨s, hs, hc⟩ := ih
      exact ⟨.delete a :: s, (Execution.delete a (Execution.of_transforms hs)).transforms,
        by simp [EditScript.cost, EditStep.cost, hc]⟩
  | substitute a b he ih =>
      obtain ⟨s, hs, hc⟩ := ih
      exact ⟨.substitute b a :: s,
        (Execution.substitute b a (Execution.of_transforms hs)).transforms,
        by simp [EditScript.cost, EditStep.cost, hc]⟩

private theorem Execution.compose {α : Type u} {first second : EditScript α}
    {source middle target : List α} (h₁ : Execution first source middle)
    (h₂ : Execution second middle target) :
    ∃ composed : EditScript α, Execution composed source target ∧
      composed.cost ≤ first.cost + second.cost := by
  cases h₁ with
  | nil => exact ⟨second, h₂, by simp [EditScript.cost]⟩
  | delete a h₁ =>
      obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
      exact ⟨.delete a :: s, .delete a hs,
        by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
  | keep a h₁ =>
      cases h₂ with
      | keep _ h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨.keep a :: s, .keep a hs,
            by simpa [EditScript.cost, EditStep.cost] using hc⟩
      | delete _ h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨.delete a :: s, .delete a hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
      | insert b h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose (.keep a h₁) h₂
          exact ⟨.insert b :: s, .insert b hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
      | substitute _ b h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨.substitute a b :: s, .substitute a b hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
  | insert a h₁ =>
      cases h₂ with
      | keep _ h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨.insert a :: s, .insert a hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
      | delete _ h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨s, hs, by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
      | insert b h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose (.insert a h₁) h₂
          exact ⟨.insert b :: s, .insert b hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
      | substitute _ b h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨.insert b :: s, .insert b hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
  | substitute a b h₁ =>
      cases h₂ with
      | keep _ h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨.substitute a b :: s, .substitute a b hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
      | delete _ h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨.delete a :: s, .delete a hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
      | insert c h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose (.substitute a b h₁) h₂
          exact ⟨.insert c :: s, .insert c hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
      | substitute _ c h₂ =>
          obtain ⟨s, hs, hc⟩ := Execution.compose h₁ h₂
          exact ⟨.substitute a c :: s, .substitute a c hs,
            by simp only [EditScript.cost, EditStep.cost] at *; omega⟩
termination_by first.length + second.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- Two scripts compose into one whose cost is at most the sum of their costs. -/
theorem EditScript.exists_compose [BEq α] [LawfulBEq α] {first second : EditScript α}
    {source middle target : List α} (h₁ : first.Transforms source middle)
    (h₂ : second.Transforms middle target) :
    ∃ composed : EditScript α, composed.Transforms source target ∧
      composed.cost ≤ first.cost + second.cost := by
  obtain ⟨composed, h, hc⟩ :=
    Execution.compose (Execution.of_transforms h₁) (Execution.of_transforms h₂)
  exact ⟨composed, h.transforms, hc⟩


private theorem editDistance_le_comm [BEq α] [LawfulBEq α] (x y : List α) :
    (editDistance y x).ret.distance ≤ (editDistance x y).ret.distance := by
  obtain ⟨inverse, hinv, hcost⟩ :=
    EditScript.exists_inverse (editDistance_script_applies x y)
  calc (editDistance y x).ret.distance ≤ inverse.cost := editDistance_minimal y x inverse hinv
    _ = (editDistance x y).ret.distance := by rw [hcost, editDistance_script_cost]

/-- **Symmetry** of unit-cost edit distance. -/
theorem editDistance_comm [BEq α] [LawfulBEq α] (x y : List α) :
    (editDistance x y).ret.distance = (editDistance y x).ret.distance :=
  Nat.le_antisymm (editDistance_le_comm y x) (editDistance_le_comm x y)

/-- **The triangle inequality** for unit-cost edit distance. -/
theorem editDistance_triangle [BEq α] [LawfulBEq α] (x y z : List α) :
    (editDistance x z).ret.distance ≤
      (editDistance x y).ret.distance + (editDistance y z).ret.distance := by
  obtain ⟨composed, hcomp, hcost⟩ := EditScript.exists_compose
    (editDistance_script_applies x y) (editDistance_script_applies y z)
  calc (editDistance x z).ret.distance ≤ composed.cost :=
        editDistance_minimal x z composed hcomp
    _ ≤ _ := by rwa [editDistance_script_cost, editDistance_script_cost] at hcost

/-- Distinct lists are at positive distance. -/
theorem editDistance_pos_iff [BEq α] [LawfulBEq α] (x y : List α) :
    0 < (editDistance x y).ret.distance ↔ x ≠ y := by
  rw [Nat.pos_iff_ne_zero, ne_eq, editDistance_eq_zero_iff]

end Cslib.Algorithms.Lean
