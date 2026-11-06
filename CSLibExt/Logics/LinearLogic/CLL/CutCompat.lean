/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-
Compatibility source port from leanprover/cslib PR944, commit
a69a43dca61ead87b6a631854de017ddaa310e08.
Original authorship and algorithm: Fabrizio Montesi, Apache 2.0.
Only imports, explicit binders, module splitting and pinned-API bridges
are adapted here. The locked CLL Proposition and Proof are reused.
-/

module

public import Cslib.Logics.LinearLogic.CLL.CutElimination

/-! # Prerequisite APIs for the frozen cut-elimination source port -/

@[expose] public section

namespace Cslib.Logic.CLL

open Cslib.Logic.InferenceSystem

universe u

variable {Atom : Type u} {a b : Proposition Atom} {Γ Δ Θ : Sequent Atom}

namespace Sequent

/-- **Check that every proposition in a list is a why-not proposition.**
Checks that all propositions in a list are question marks (`ʔ`). -/
def _root_.List.allQuest (as : List (Proposition Atom)) :=
  as.map (· matches ʔ_) |> List.foldr .and true

/-- **Why-not check agrees on a list and its multiset.**
Checking a list context agrees with checking its multiset coercion. -/
@[simp, scoped grind =]
theorem allQuest_coe (Γ : List (Proposition Atom)) : allQuest (Γ : Sequent Atom) = Γ.allQuest :=
  Multiset.coe_fold_r Bool.and true _

/-- **Empty sequent consists of question-mark propositions.**
The empty sequent consists of `ʔ`-propositions. -/
@[simp, scoped grind =]
theorem allQuest_zero : (0 : Sequent Atom).allQuest := by simp [allQuest]

/-- **A cons sequent is all question marks iff its head and tail are.**
A cons sequent consists of `ʔ`-propositions exactly when its head and tail do. -/
theorem allQuest_cons_iff {Γ : Sequent Atom} : allQuest (a ::ₘ Γ) ↔ (∃ b, a = ʔb) ∧ Γ.allQuest := by
  cases a <;> simp [allQuest]

/-- **A question-mark head does not change the all-question-mark property.**
Adding a `ʔ`-proposition preserves and reflects `allQuest`. -/
@[simp]
theorem allQuest_quest_cons {Γ : Sequent Atom} : allQuest (ʔa ::ₘ Γ) ↔ Γ.allQuest := by
  simp [allQuest]

/-- **A sequent headed by a bang proposition is not all question marks.**
A sequent containing a `!`-proposition cannot satisfy `allQuest`. -/
@[simp]
theorem not_allQuest_bang_cons {Γ : Sequent Atom} : ¬allQuest ((!a) ::ₘ Γ) := by simp [allQuest]

/-- **A sum of sequents is all question marks iff both summands are.**
A sum consists of `ʔ`-propositions exactly when both summands do. -/
@[simp, scoped grind .]
theorem allQuest_add {Γ Δ : Sequent Atom} : (Γ + Δ).allQuest ↔ Γ.allQuest ∧ Δ.allQuest := by
  refine Multiset.induction_on Γ ?_ ?_
  · simp
  · intro a
    cases a <;> simp [allQuest]

theorem allQuest_of_le {Γ Δ : Sequent Atom} (h : Γ ≤ Δ) (hΔ : Δ.allQuest) : Γ.allQuest := by
  obtain ⟨Θ, rfl⟩ := Multiset.le_iff_exists_add.mp h
  exact (allQuest_add.mp hΔ).1

theorem exists_quest_of_mem_allQuest {Γ : Sequent Atom} (hΓ : Γ.allQuest) (ha : a ∈ Γ) :
    ∃ b, a = ʔb := by
  have ha_le : ({a} : Sequent Atom) ≤ Γ := by
    simpa using ha
  have hqa : Sequent.allQuest (a ::ₘ (0 : Sequent Atom)) := by
    simpa using allQuest_of_le ha_le hΓ
  exact (allQuest_cons_iff.mp hqa).1

end Sequent

/-- **Height of a classical linear logic proof.** Height of a proof. -/
def Proof.height {Γ : Sequent Atom} : ⇓Γ → ℕ
  | .ax | .one | .top => 1
  | .bot p | .parr p | .oplus₁ p | .oplus₂ p
    | .quest p | .weaken p | .contract p | .bang _ p => p.height + 1
  | .cut p q | .tensor p q | .with p q => max p.height q.height + 1

/-- **Conclusion transport preserves proof height.**
Transporting a conclusion preserves proof height. -/
@[simp, scoped grind =]
theorem Proof.rwConclusion_height {Γ Δ : Sequent Atom} (h : Γ = Δ) (p : ⇓Γ) :
    (p.rwConclusion h).height = p.height := by grind

/-- **Conclusion transport preserves the Boolean cut-free check.**
Conclusion transport preserves the pinned Boolean cut-free check. -/
@[simp]
theorem Proof.cutFree_rwConclusion {Γ Δ : Sequent Atom}
    (h : Γ = Δ) (p : Proof Γ) :
    (p.rwConclusion h).cutFree = p.cutFree := by
  cases h
  rfl

end Cslib.Logic.CLL
