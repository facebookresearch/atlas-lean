/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.Matching.CollegeAdmissions
import MathlibExt.GameTheory.Matching.StableMechanism
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma

/-! # Tests for college admissions by quota slots

College A has two incumbents and prefers student 1 to 0. B has two seats, but wants only 2.
Everyone prefers unemployment to C, and would prefer D to their assignment, but D has no seats.
Student 3 is unmatched. Permuting the seats inside A and B preserves the college assignment
but creates two different blocking pairs in the copies market.
-/

namespace MathlibExtTest.GameTheory.Matching.CollegeAdmissions

open MathlibExt.GameTheory.Matching.RuralHospitals
open MathlibExt.GameTheory.Matching.CollegeAdmissions
open MathlibExt.GameTheory.Matching.StableMechanism (rankOrder)

private abbrev quota : Fin 4 → ℕ := ![2, 2, 1, 0]
private abbrev A₀ : Slot quota := ⟨0, ⟨0, by decide⟩⟩
private abbrev A₁ : Slot quota := ⟨0, ⟨1, by decide⟩⟩
private abbrev B₀ : Slot quota := ⟨1, ⟨0, by decide⟩⟩
private abbrev B₁ : Slot quota := ⟨1, ⟨1, by decide⟩⟩
private abbrev C₀ : Slot quota := ⟨2, ⟨0, by decide⟩⟩

private abbrev sp : MPrefsSingle (Fin 4) (Fin 4) := fun s =>
  rankOrder (fun x => x.elim 3 (if s < 2 then ![1, 2, 4, 0] else ![2, 1, 4, 0]))
    (by revert s; decide)

private instance (s : Fin 4) : DecidableRel (studentPrefs quota sp s).lt := fun x y => by
  unfold studentPrefs
  dsimp only
  infer_instance

private abbrev cp : WPrefsSingle (Fin 4) (Fin 4) := fun c =>
  rankOrder (fun x => if c = 0 then x.elim 3 ![1, 0, 2, 4] else if c = 1 then
    x.elim 1 ![2, 3, 0, 4] else x.elim 4 ![1, 2, 3, 0]) (by revert c; decide)

private abbrev good : Fin 4 ≃. Slot quota :=
  ⟨![some A₁, some A₀, some B₀, none], fun k =>
    if k = A₀ then some 1 else if k = A₁ then some 0 else if k = B₀ then some 2 else none,
    by decide⟩

private abbrev bad : Fin 4 ≃. Slot quota :=
  ⟨![some A₀, some A₁, some B₁, none], fun k =>
    if k = A₀ then some 0 else if k = A₁ then some 1 else if k = B₁ then some 2 else none,
    by decide⟩

private theorem good_stable : IsStableSingle (studentPrefs quota sp) (slotPrefs quota cp) good := by
  unfold IsStableSingle; decide

private theorem same_colleges : collapse bad = collapse good := by
  apply Assignment.ext
  funext s
  change (bad s).map Sigma.fst = (good s).map Sigma.fst
  revert s; decide

-- There is no index at D. Both copies of A lie above B for 0, but below B for 2;
-- C's one copy stays below the outside option. A vacancy at B does not make 3 acceptable.
example : IsEmpty (Fin (quota 3)) := inferInstanceAs (IsEmpty (Fin 0))
example : (studentPrefs quota sp 0).lt (some A₁) (some B₀) ∧
    (studentPrefs quota sp 2).lt (some B₁) (some A₀) ∧
    (studentPrefs quota sp 3).lt none (some C₀) ∧ (slotPrefs quota cp B₁).lt none (some 3) := by
  decide

-- A is full; B has one vacancy; 3 would like both B and D. Neither college blocks.
example : (roster (collapse good).assign 0).card = 2 ∧
    (roster (collapse good).assign 1).card = 1 := by
  have hA : roster (collapse good).assign 0 = {0, 1} := by
    ext s; rw [mem_roster]; revert s; decide
  have hB : roster (collapse good).assign 1 = {2} := by
    ext s; rw [mem_roster]; revert s; decide
  rw [hA, hB]; decide

example : (sp 3).lt (some 1) ((collapse good).assign 3) ∧
    ¬ Blocks sp cp (collapse good) 3 1 := ⟨by decide, (stable_collapse good_stable).2.2 3 1⟩
example : (sp 3).lt (some 3) ((collapse good).assign 3) ∧
    ¬ Blocks sp cp (collapse good) 3 3 := ⟨by decide, not_blocks_of_quota_zero sp cp _ rfl 3⟩

-- Inversion at A: its top student 1 prefers the earlier copy and outranks its incumbent 0.
private theorem inversion : (studentPrefs quota sp 1).lt (some A₀) (bad 1) ∧
    (slotPrefs quota cp A₀).lt (some 1) (bad.symm A₀) := by decide

-- Gap at B: student 2 prefers the vacant first copy and it prefers 2 to being empty.
example : bad.symm B₀ = none ∧ (studentPrefs quota sp 2).lt (some B₀) (bad 2) ∧
    (slotPrefs quota cp B₀).lt (some 2) (bad.symm B₀) := by decide

example : ¬ IsStableSingle (studentPrefs quota sp) (slotPrefs quota cp) bad :=
  fun h => h.2.2 1 A₀ inversion
example : IsStable sp cp (collapse bad) := by
  rw [same_colleges]; exact stable_collapse good_stable

-- The same pairwise college predicate detects a real replacement block at a *full* college:
-- here 2 holds 1's seat at A. There is also an acceptable vacancy for 2 at B.
private abbrev displaced : Fin 4 ≃. Slot quota :=
  ⟨![some A₀, none, some A₁, none], fun k =>
    if k = A₀ then some 0 else if k = A₁ then some 2 else none, by decide⟩

example : (roster (collapse displaced).assign 0).card = quota 0 ∧
    Blocks sp cp (collapse displaced) 1 0 := by
  have h : roster (collapse displaced).assign 0 = {0, 2} := by
    ext s; rw [mem_roster]; revert s; decide
  exact ⟨by rw [h]; decide, by exact ⟨by decide, Or.inr ⟨2, by decide, by decide⟩⟩⟩

example : Blocks sp cp (collapse displaced) 2 1 := by
  have h : roster (collapse displaced).assign 1 = ∅ := by
    ext s; rw [mem_roster]; revert s; decide
  exact ⟨by decide, Or.inl ⟨by rw [h]; decide, by decide⟩⟩

-- Fill B's spare seat with the unacceptable student 3. No pair would block, but the
-- college would rather leave that seat empty. Pairwise nonblocking alone is not stability.
private abbrev overaccept : Fin 4 ≃. Slot quota :=
  ⟨![some A₁, some A₀, some B₀, some B₁], fun k => if k = B₁ then some 3 else good.symm k,
    by decide⟩

example : (∀ s k, ¬ ((studentPrefs quota sp s).lt (some k) (overaccept s) ∧
    (slotPrefs quota cp k).lt (some s) (overaccept.symm k))) ∧
    ¬ IsStable sp cp (collapse overaccept) :=
  ⟨by decide, fun h => h.2.1 3 1 (by decide) (by decide)⟩

-- The equivalence really recovers the particular ordered matching, not the bad permutation.
example : lift cp (collapse bad) = good := by
  rw [same_colleges]; exact lift_collapse_of_ordered (ordered_of_stable good_stable)
example : (stableEquiv quota sp cp).symm ⟨good, good_stable⟩ =
    ⟨collapse good, stable_collapse good_stable⟩ := rfl
example : stableEquiv quota sp cp ⟨collapse good, stable_collapse good_stable⟩ =
    ⟨good, good_stable⟩ := (stableEquiv quota sp cp).apply_symm_apply ⟨good, good_stable⟩

end MathlibExtTest.GameTheory.Matching.CollegeAdmissions
