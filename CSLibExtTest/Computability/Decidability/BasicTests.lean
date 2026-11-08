/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Basic

@[expose] public section

/-!
# Tests for decidable, recognizable and co-recognizable predicates

Concrete members of each class, and Post's theorem used in both directions.
-/

set_option autoImplicit false

open Computability Turing Cslib.Decidability

namespace CSLibExtTest.Computability.Decidability

/-- Evenness is computable, so it is decidable by a multi-stack machine. -/
theorem even_computablePred : ComputablePred fun n : ℕ ↦ Even n := by
  refine ComputablePred.computable_iff.mpr ⟨fun n ↦ n % 2 == 0, ?_, ?_⟩
  · exact (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).to_comp
  · funext n
    simp [Nat.even_iff]

example : TM2Decidable fun n : ℕ ↦ Even n :=
  tm2Decidable_iff_computablePred.mpr even_computablePred

/-- Hence evenness is recognizable and co-recognizable, and oddness is decidable. -/
example : TM2Recognizable (fun n : ℕ ↦ Even n) ∧ TM2CoRecognizable fun n : ℕ ↦ Even n := by
  have h := tm2Decidable_iff_computablePred.mpr even_computablePred
  exact ⟨h.tm2Recognizable, h.tm2CoRecognizable⟩

example : TM2Decidable fun n : ℕ ↦ ¬Even n :=
  (tm2Decidable_iff_computablePred.mpr even_computablePred).not

/-- Post's theorem, backward: recognizable plus co-recognizable gives decidable, here on lists. -/
example (p : List ℕ → Prop) (h₁ : TM2Recognizable p) (h₂ : TM2CoRecognizable p) :
    TM2Decidable p :=
  tm2Decidable_iff_tm2Recognizable_and_tm2CoRecognizable.mpr ⟨h₁, h₂⟩

/-- The always-true predicate is recognized by a machine that halts at once. -/
example : TM2Recognizable fun _ : ℕ ↦ True :=
  tm2Recognizable_iff_rePred.mpr (ComputablePred.computable_iff.mpr
    ⟨fun _ ↦ true, Computable.const true, by funext; simp⟩).to_re

end CSLibExtTest.Computability.Decidability
