/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat

/-! Exact sparse coordinate lookup with proved two-sided source bindings. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
open scoped BigOperators

/-- A finite sparse source tree stores only exact coordinate keys and original source indices. -/
inductive GeneratedAxisGlobalSparseLookupTree (ι : Type*) where
  | empty : GeneratedAxisGlobalSparseLookupTree ι
  | branch : ℕ → ι → GeneratedAxisGlobalSparseLookupTree ι →
      GeneratedAxisGlobalSparseLookupTree ι → GeneratedAxisGlobalSparseLookupTree ι

/-- A sparse lookup returns a source index only after matching its exact coordinate key. -/
def generatedAxisGlobalSparseLookup {ι : Type*} :
    GeneratedAxisGlobalSparseLookupTree ι → ℕ → Option ι
  | .empty, _ => none
  | .branch k i l r, n =>
      if n = k then some i else
        if n < k then generatedAxisGlobalSparseLookup l n else
          generatedAxisGlobalSparseLookup r n

/-- Each stored source index has precisely the displayed original coordinate key. -/
def GeneratedAxisGlobalSparseLookupValid {ι : Type*}
    (f : ι → ℕ) : GeneratedAxisGlobalSparseLookupTree ι → Prop
  | .empty => True
  | .branch k i l r =>
      f i = k ∧ GeneratedAxisGlobalSparseLookupValid f l ∧
        GeneratedAxisGlobalSparseLookupValid f r

/-- Exact finite source-key validity is decidable by inspecting the original tree recursively. -/
def generatedAxisGlobalSparseLookupValidDecidable {ι : Type*} (f : ι → ℕ) :
    (t : GeneratedAxisGlobalSparseLookupTree ι) →
      Decidable (GeneratedAxisGlobalSparseLookupValid f t)
  | .empty => isTrue True.intro
  | .branch k i l r =>
      letI := generatedAxisGlobalSparseLookupValidDecidable f l
      letI := generatedAxisGlobalSparseLookupValidDecidable f r
      inferInstanceAs (Decidable (f i = k ∧ GeneratedAxisGlobalSparseLookupValid f l ∧
        GeneratedAxisGlobalSparseLookupValid f r))

/-- The ordinary recursive finite decision procedure for original source-key certificates. -/
instance {ι : Type*} (f : ι → ℕ) (t : GeneratedAxisGlobalSparseLookupTree ι) :
    Decidable (GeneratedAxisGlobalSparseLookupValid f t) :=
  generatedAxisGlobalSparseLookupValidDecidable f t

/-- Every successful sparse lookup is justified by an actual original source coordinate. -/
theorem generatedAxisGlobalSparseLookup_sound {ι : Type*}
    (f : ι → ℕ) (t : GeneratedAxisGlobalSparseLookupTree ι)
    (ht : GeneratedAxisGlobalSparseLookupValid f t) (n : ℕ) (i : ι)
    (h : generatedAxisGlobalSparseLookup t n = some i) : f i = n := by
  induction t with
  | empty => simp [generatedAxisGlobalSparseLookup] at h
  | branch k j l r hl hr =>
    rcases ht with ⟨hj, hL, hR⟩
    simp only [generatedAxisGlobalSparseLookup] at h
    split_ifs at h with hn hlt
    · cases Option.some.inj h
      exact hj.trans hn.symm
    · exact hl hL h
    · exact hr hR h

/-- A two-sided sparse coordinate lookup evaluates the entire original finite coefficient sum. -/
theorem generatedAxisGlobalSparseLookup_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (f : ι → κ) (g : κ → Option ι)
    (hleft : ∀ i, g (f i) = some i)
    (hright : ∀ r i, g r = some i → f i = r)
    (c : ι → ℚ) (r : κ) :
    (∑ i, c i * (if f i = r then 1 else 0)) =
      match g r with | none => 0 | some i => c i := by
  cases hg : g r with
  | none =>
    apply Finset.sum_eq_zero
    intro i _
    have hi : f i ≠ r := by
      intro hi
      have h := hleft i
      rw [hi, hg] at h
      contradiction
    simp [hi]
  | some j =>
    have hj : f j = r := hright r j hg
    have he (i : ι) : f i = r ↔ i = j := by
      constructor
      · intro hi
        have h := hleft i
        rw [hi, hg] at h
        exact Option.some.inj h.symm
      · rintro rfl
        exact hj
    simp_rw [he]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
