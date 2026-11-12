/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm
public import CSLibExt.Algorithms.Lean.DynamicProgramming.LongestCommonSubsequence
public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment

/-!
# Edit distance and longest common subsequence as Needleman–Wunsch instances

`editDistance` and `longestCommonSubsequence` are tabulated prefix dynamic programs; for a lawful
`BEq`, each is proved optimal against its own witnesses (edit scripts and common sublists).
`nwScore` is the Needleman–Wunsch specification of the optimal global alignment score, proved
optimal against alignments. This module relates both tabulated optima to `nwScore` at two
scorings, for every element type with a lawful `BEq` and all lists, empty ones included:

* `editDistance_distance_eq_neg_nwScore`: the unit-cost edit distance is minus `nwScore` with
  substitution score `if a == b then 0 else -1` and gap score `-1`.
* `longestCommonSubsequence_length_eq_nwScore`: the longest common subsequence length is
  `nwScore` with substitution score `if a == b then 1 else 0` and gap score `0`.

The edit-distance proof translates witnesses both ways. An edit script that transforms one list
into another becomes an alignment of the two lists, one column per step, scoring at least minus
the script's cost (substituting a letter by an equal one costs `1` but scores `0`). An alignment
becomes an edit script that transforms its first row into its second and costs exactly minus the
alignment's score. The LCS proof compares common sublists with the recurrence `nwScore_eq`
directly.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

section EditDistance

/-- The alignment column recording one edit step. -/
private def editStepColumn : EditStep α → Option α × Option α
  | .keep value => (some value, some value)
  | .delete value => (some value, none)
  | .insert value => (none, some value)
  | .substitute source target => (some source, some target)

/-- The unit-cost edit steps of one alignment column: a column pairing two letters keeps or
substitutes, a gap column deletes or inserts, and an empty column emits nothing. -/
private def columnEditSteps [BEq α] : Option α × Option α → EditScript α
  | (some a, some b) => [if a == b then .keep a else .substitute a b]
  | (some a, none) => [.delete a]
  | (none, some b) => [.insert b]
  | (none, none) => []

/-- Prepending a non-empty column to a valid alignment gives a valid alignment. -/
private theorem isAlignment_cons {A : Alignment α} {xs ys : List α}
    (c : Option α × Option α) (hc : c ≠ (none, none)) (h : IsAlignment A xs ys) :
    IsAlignment (c :: A) (c.1.toList ++ xs) (c.2.toList ++ ys) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    exacts [hc, h.1 d hd]
  · rcases c with ⟨_ | a, _ | b⟩ <;> simp [h.2.1]
  · rcases c with ⟨_ | a, _ | b⟩ <;> simp [h.2.2]

/-- For a lawful `BEq`, an edit script that transforms `source` into `target` records, one column
per step, a valid alignment of `source` and `target`. -/
private theorem isAlignment_map_editStepColumn [BEq α] [LawfulBEq α] :
    ∀ (script : EditScript α) (source target : List α), script.Transforms source target →
      IsAlignment (script.map editStepColumn) source target
  | [], [], target, h => by
      have ht : target = [] := by
        simpa [EditScript.Transforms, EditScript.apply?] using h.symm
      subst ht
      exact ⟨by simp, rfl, rfl⟩
  | [], _ :: _, _, h => by simp [EditScript.Transforms, EditScript.apply?] at h
  | .keep _ :: _, [], _, h => by simp [EditScript.Transforms, EditScript.apply?] at h
  | .keep value :: script, source :: rest, target, h => by
      simp only [EditScript.Transforms, EditScript.apply?] at h
      split_ifs at h with hv
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain rfl : value = source := by simpa using hv
      simpa [editStepColumn] using isAlignment_cons (some value, some value) (by simp)
        (isAlignment_map_editStepColumn script rest t ht)
  | .delete _ :: _, [], _, h => by simp [EditScript.Transforms, EditScript.apply?] at h
  | .delete value :: script, source :: rest, target, h => by
      simp only [EditScript.Transforms, EditScript.apply?] at h
      split_ifs at h with hv
      obtain rfl : value = source := by simpa using hv
      simpa [editStepColumn] using isAlignment_cons (some value, none) (by simp)
        (isAlignment_map_editStepColumn script rest target h)
  | .insert value :: script, source, target, h => by
      simp only [EditScript.Transforms, EditScript.apply?] at h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa [editStepColumn] using isAlignment_cons (none, some value) (by simp)
        (isAlignment_map_editStepColumn script source t ht)
  | .substitute _ _ :: _, [], _, h => by simp [EditScript.Transforms, EditScript.apply?] at h
  | .substitute value replacement :: script, source :: rest, target, h => by
      simp only [EditScript.Transforms, EditScript.apply?] at h
      split_ifs at h with hv
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain rfl : value = source := by simpa using hv
      simpa [editStepColumn] using isAlignment_cons (some value, some replacement) (by simp)
        (isAlignment_map_editStepColumn script rest t ht)

/-- For a lawful `BEq`, the alignment recorded by an edit script scores at least minus the
script's unit cost. -/
private theorem neg_cost_le_alignmentScore_map_editStepColumn [BEq α] [LawfulBEq α]
    (script : EditScript α) :
    -(script.cost : ℤ) ≤
      alignmentScore (fun a b => if a == b then 0 else -1) (-1) (script.map editStepColumn) := by
  induction script with
  | nil => simp [EditScript.cost, alignmentScore]
  | cons step script ih =>
      simp only [alignmentScore, List.map_cons, List.sum_cons] at ih ⊢
      cases step with
      | keep value =>
          simp only [editStepColumn, columnScore, EditScript.cost, EditStep.cost, beq_self_eq_true,
            reduceIte]
          push_cast
          linarith
      | delete value =>
          simp only [editStepColumn, columnScore, EditScript.cost, EditStep.cost]
          push_cast
          linarith
      | insert value =>
          simp only [editStepColumn, columnScore, EditScript.cost, EditStep.cost]
          push_cast
          linarith
      | substitute source target =>
          simp only [editStepColumn, columnScore, EditScript.cost, EditStep.cost]
          push_cast
          split_ifs <;> linarith

/-- For a lawful `BEq`, the edit script read off an alignment transforms its first row into its
second row. -/
private theorem apply?_flatMap_columnEditSteps [BEq α] [LawfulBEq α] :
    ∀ A : Alignment α,
      EditScript.apply? (A.flatMap columnEditSteps) (A.filterMap Prod.fst) =
        some (A.filterMap Prod.snd)
  | [] => rfl
  | (some a, some b) :: A => by
      have ih := apply?_flatMap_columnEditSteps A
      by_cases hab : a = b
      · subst hab
        simp [columnEditSteps, EditScript.apply?, ih]
      · simp [columnEditSteps, EditScript.apply?, ih, hab]
  | (some a, none) :: A => by
      simp [columnEditSteps, EditScript.apply?, apply?_flatMap_columnEditSteps A]
  | (none, some b) :: A => by
      simp [columnEditSteps, EditScript.apply?, apply?_flatMap_columnEditSteps A]
  | (none, none) :: A => by
      simpa [columnEditSteps] using apply?_flatMap_columnEditSteps A

/-- The edit script read off an alignment costs exactly minus the alignment's score. -/
private theorem cost_flatMap_columnEditSteps [BEq α] (A : Alignment α) :
    (EditScript.cost (A.flatMap columnEditSteps) : ℤ) =
      -alignmentScore (fun a b => if a == b then 0 else -1) (-1) A := by
  induction A with
  | nil => rfl
  | cons c A ih =>
      simp only [alignmentScore, List.map_cons, List.sum_cons] at ih ⊢
      rcases c with ⟨_ | a, _ | b⟩
      · simpa [columnEditSteps, columnScore] using ih
      · simp only [columnEditSteps, columnScore, List.flatMap_cons, List.singleton_append,
          EditScript.cost, EditStep.cost]
        push_cast
        linarith
      · simp only [columnEditSteps, columnScore, List.flatMap_cons, List.singleton_append,
          EditScript.cost, EditStep.cost]
        push_cast
        linarith
      · simp only [columnEditSteps, columnScore, List.flatMap_cons, List.singleton_append,
          EditScript.cost]
        split_ifs <;> simp only [EditStep.cost] <;> push_cast <;> linarith

/-- **Unit-cost edit distance is a Needleman–Wunsch instance.** For a lawful `BEq`, the distance
computed by the tabulated `editDistance` is minus the optimal global alignment score with
substitution score `if a == b then 0 else -1` and gap score `-1`. -/
theorem editDistance_distance_eq_neg_nwScore [BEq α] [LawfulBEq α] (source target : List α) :
    ((editDistance source target).ret.distance : ℤ) =
      -nwScore (fun a b => if a == b then 0 else -1) (-1) source target := by
  apply le_antisymm
  · obtain ⟨A, hA, hscore⟩ :=
      exists_alignmentScore_eq_nwScore (fun a b => if a == b then 0 else -1) (-1) source target
    have happly : EditScript.Transforms (A.flatMap columnEditSteps) source target := by
      have h := apply?_flatMap_columnEditSteps A
      rwa [hA.2.1, hA.2.2] at h
    have hmin := editDistance_minimal source target _ happly
    rw [← hscore, ← cost_flatMap_columnEditSteps A]
    exact_mod_cast hmin
  · have hA := isAlignment_map_editStepColumn _ source target
      (editDistance_script_applies source target)
    have hle := alignmentScore_le_nwScore (fun a b => if a == b then 0 else -1) (-1) source
      target _ hA
    have hcost := neg_cost_le_alignmentScore_map_editStepColumn
      (editDistance source target).ret.script
    rw [editDistance_script_cost] at hcost
    linarith

end EditDistance

section LongestCommonSubsequence

/-- For a lawful `BEq`, every common sublist is at most as long as the Needleman–Wunsch score
with substitution score `if a == b then 1 else 0` and gap score `0`. -/
private theorem length_le_nwScore_of_sublist [BEq α] [LawfulBEq α] :
    ∀ (xs ys zs : List α), zs.Sublist xs → zs.Sublist ys →
      (zs.length : ℤ) ≤ nwScore (fun a b => if a == b then 1 else 0) 0 xs ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys zs hx _
      rw [List.sublist_nil.mp hx, nwScore_nil_left]
      simp
  | cons a xs ihx =>
      intro ys
      induction ys with
      | nil =>
          intro zs _ hy
          rw [List.sublist_nil.mp hy, nwScore_nil_right]
          simp
      | cons b ys ihy =>
          intro zs hx hy
          rw [nwScore_eq]
          cases hx with
          | cons _ hx =>
              have h := ihx (b :: ys) zs hx hy
              exact le_max_of_le_left (le_max_of_le_right (by simpa using h))
          | cons_cons _ hx =>
              cases hy with
              | cons _ hy =>
                  have h := ihy _ (hx.cons_cons a) hy
                  exact le_max_of_le_right (by simpa using h)
              | cons_cons _ hy =>
                  have h := ihx ys _ hx hy
                  refine le_max_of_le_left (le_max_of_le_left ?_)
                  simp only [beq_self_eq_true, reduceIte, List.length_cons]
                  push_cast
                  linarith

/-- For a lawful `BEq`, some common sublist is at least as long as the Needleman–Wunsch score
with substitution score `if a == b then 1 else 0` and gap score `0`. -/
private theorem exists_sublist_nwScore_le [BEq α] [LawfulBEq α] :
    ∀ (xs ys : List α), ∃ zs : List α, zs.Sublist xs ∧ zs.Sublist ys ∧
      nwScore (fun a b => if a == b then 1 else 0) 0 xs ys ≤ zs.length := by
  intro xs
  induction xs with
  | nil => exact fun ys => ⟨[], by simp, by simp, by simp [nwScore_nil_left]⟩
  | cons a xs ihx =>
      intro ys
      induction ys with
      | nil => exact ⟨[], by simp, by simp, by simp [nwScore_nil_right]⟩
      | cons b ys ihy =>
          obtain ⟨z₁, h₁x, h₁y, h₁⟩ := ihx ys
          obtain ⟨z₂, h₂x, h₂y, h₂⟩ := ihx (b :: ys)
          obtain ⟨z₃, h₃x, h₃y, h₃⟩ := ihy
          have hdiag : ∃ zs : List α, zs.Sublist (a :: xs) ∧ zs.Sublist (b :: ys) ∧
              nwScore (fun a b => if a == b then 1 else 0) 0 xs ys +
                (if a == b then 1 else 0) ≤ zs.length := by
            by_cases hab : a = b
            · subst hab
              refine ⟨a :: z₁, h₁x.cons_cons a, h₁y.cons_cons a, ?_⟩
              simp only [beq_self_eq_true, reduceIte, List.length_cons]
              push_cast
              linarith
            · refine ⟨z₁, h₁x.cons a, h₁y.cons b, ?_⟩
              simpa [hab] using h₁
          obtain ⟨z₀, h₀x, h₀y, h₀⟩ := hdiag
          have hle : nwScore (fun a b => if a == b then 1 else 0) 0 (a :: xs) (b :: ys) ≤
              max (max (z₀.length : ℤ) z₂.length) z₃.length := by
            rw [nwScore_eq]
            exact max_le_max (max_le_max h₀ (by simpa using h₂)) (by simpa using h₃)
          rcases max_choice (max (z₀.length : ℤ) z₂.length) z₃.length with h | h <;>
            rw [h] at hle
          · rcases max_choice (z₀.length : ℤ) z₂.length with h' | h' <;> rw [h'] at hle
            · exact ⟨z₀, h₀x, h₀y, hle⟩
            · exact ⟨z₂, h₂x.cons a, h₂y, hle⟩
          · exact ⟨z₃, h₃x, h₃y.cons b, hle⟩

/-- **Longest common subsequence length is a Needleman–Wunsch instance.** For a lawful `BEq`,
the length computed by the tabulated `longestCommonSubsequence` is the optimal global alignment
score with substitution score `if a == b then 1 else 0` and gap score `0`. -/
theorem longestCommonSubsequence_length_eq_nwScore [BEq α] [LawfulBEq α] (xs ys : List α) :
    ((longestCommonSubsequence xs ys).ret.1 : ℤ) =
      nwScore (fun a b => if a == b then 1 else 0) 0 xs ys := by
  obtain ⟨hlen, hx, hy, hopt⟩ := longestCommonSubsequence_correct xs ys
  obtain ⟨zs, hzx, hzy, hz⟩ := exists_sublist_nwScore_le xs ys
  have h₁ := length_le_nwScore_of_sublist xs ys _ hx hy
  have h₂ := hopt zs hzx hzy
  rw [hlen] at h₁ h₂
  apply le_antisymm h₁
  calc nwScore (fun a b => if a == b then 1 else 0) 0 xs ys ≤ zs.length := hz
    _ ≤ (longestCommonSubsequence xs ys).ret.1 := by exact_mod_cast h₂

end LongestCommonSubsequence

end Cslib.Algorithms.Lean
