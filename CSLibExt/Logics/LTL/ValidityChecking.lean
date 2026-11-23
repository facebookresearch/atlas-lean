/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.DecidableModelChecking

/-!
# Executable LTL validity and satisfiability

Validity and satisfiability over a finite alphabet are decided by the
existing executable model checker on the universal Boolean valuation
system, transported to set-valued words. The definitions follow Atlas
`Cslib.LTL.Formula` (upstream cslib has no LTL at this pin; a future
pin bump may need reconciliation).
-/

@[expose] public section

namespace Cslib.LTL.ModelChecking

variable {Atom : Type*} [Fintype Atom] [DecidableEq Atom]

/-- Universal valuation system with total unit transitions. -/
def allValuations : LTS (Atom → Bool) Unit where
  Tr := fun _ _ _ => True

/-- Total valuation transitions are trivially decidable. -/
instance allValuationsTrDecidable :
    ∀ (s : Atom → Bool) (action : Unit) (t : Atom → Bool),
      Decidable (allValuations.Tr s action t) :=
  fun _ _ _ => isTrue True.intro

/-- The universal initial set has decidable membership. -/
instance allValuationsMemDecidable :
  DecidablePred (· ∈ (Set.univ : Set (Atom → Bool))) :=
  fun _ => isTrue (Set.mem_univ _)

/-- The Boolean valuation test is decidable by equality. -/
instance allValuationsValDecidable :
  ∀ (v : Atom → Bool) (a : Atom), Decidable ((fun v a => v a = true) v a) :=
  fun v a => decEq (v a) true

omit [Fintype Atom] [DecidableEq Atom] in
/-- Every Boolean word runs in the universal valuation system. -/
theorem isRun_allValuations (w : ωSequence (Atom → Bool)) :
    IsRun allValuations Set.univ w := by
  rw [isRun_iff]
  exact ⟨Set.mem_univ _, fun _ => ⟨(), True.intro⟩⟩

/-- Validity checker over all Boolean valuations. -/
def validityB (φ : Formula Atom) : Bool :=
  checkB allValuations Set.univ (fun v a => v a = true) φ

/-- Satisfiability checker via negated validity. -/
def satisfiableB (φ : Formula Atom) : Bool :=
  !(checkB allValuations Set.univ (fun v a => v a = true) (.not φ))

/-- Set view of a Boolean valuation. -/
def toSet (v : Atom → Bool) : Set Atom :=
  {a | v a = true}

omit [Fintype Atom] [DecidableEq Atom] in
/-- Satisfaction agrees across the set and Boolean views. -/
theorem satisfies_toSet_iff (φ : Formula Atom)
    (w : ωSequence (Atom → Bool)) :
    Word.Satisfies (fun s a => a ∈ s) (w.map toSet) φ ↔
      Word.Satisfies (fun v a => v a = true) w φ := by
  have h :=
    Word.satisfies_map (valuation := fun s a => a ∈ s)
      (f := toSet) φ w
  simpa only [toSet, Set.mem_ofPred_eq] using h

omit [Fintype Atom] [DecidableEq Atom] in
/-- Every set word lifts to a Boolean word. -/
theorem exists_map_toSet_eq (W : ωSequence (Set Atom)) :
    ∃ w : ωSequence (Atom → Bool), w.map toSet = W := by
  classical
  refine ⟨fun n a => decide (a ∈ W n), ?_⟩
  ext n a
  change decide (a ∈ W n) = true ↔ a ∈ W n
  exact Iff.of_eq decide_eq_true_eq

/-- Validity endpoint over set-valued words. -/
theorem validityB_iff (φ : Formula Atom) :
    validityB φ = true ↔
      ∀ W : ωSequence (Set Atom),
        Word.Satisfies (fun s a => a ∈ s) W φ := by
  unfold validityB
  rw [checkB_iff]
  constructor
  · intro hModels W
    obtain ⟨w, rfl⟩ := exists_map_toSet_eq W
    exact (satisfies_toSet_iff φ w).mpr
      (hModels w (isRun_allValuations w))
  · intro hAll w _
    exact (satisfies_toSet_iff φ w).mp (hAll (w.map toSet))

/-- Satisfiability endpoint over set-valued words. -/
theorem satisfiableB_iff (φ : Formula Atom) :
    satisfiableB φ = true ↔
      ∃ W : ωSequence (Set Atom),
        Word.Satisfies (fun s a => a ∈ s) W φ := by
  classical
  have hval : checkB allValuations Set.univ (fun v a => v a = true) (.not φ) = true ↔
      ∀ W : ωSequence (Set Atom), Word.Satisfies (fun s a => a ∈ s) W (.not φ) :=
    validityB_iff (.not φ)
  have hbool : ∀ b : Bool, ((!b) = true ↔ ¬ (b = true)) := by
    intro b
    cases b <;> simp
  unfold satisfiableB
  rw [hbool, hval]
  simp only [Word.Satisfies.not_iff]
  constructor
  · intro hne
    by_contra hex
    exact hne (fun W hW => hex ⟨W, hW⟩)
  · rintro ⟨W, hW⟩ hall
    exact hall W hW

end Cslib.LTL.ModelChecking
