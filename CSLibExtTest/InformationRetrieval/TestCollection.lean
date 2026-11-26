/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.InformationRetrieval.PrecisionAt
import CSLibExt.InformationRetrieval.TestCollection
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Tests for test collections

Fixture: three documents, one topic; doc 0 judged relevant, doc 1 judged
nonrelevant, doc 2 unjudged.
-/

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- Fixture: doc 0 relevant, doc 1 nonrelevant, doc 2 unjudged. -/
def fixture : TestCollection 3 Unit :=
  ⟨fun _ d => match d.val with | 0 => some true | 1 => some false | _ => none⟩

/-- Ranking mixing relevant and unjudged documents. -/
def r1 : Fin 2 → Fin 3 := ![0, 2]

/-- Ranking with no relevant documents. -/
def r2 : Fin 2 → Fin 3 := ![2, 1]

/-- T1: `relevant` holds for doc 0. -/
theorem fixture_relevant_doc0 :
    fixture.relevant () ⟨0, by decide⟩ := by
  decide

/-- T1: `relevant` fails for doc 1. -/
theorem fixture_not_relevant_doc1 :
    ¬ fixture.relevant () ⟨1, by decide⟩ := by
  decide

/-- T1: `relevant` fails for doc 2. -/
theorem fixture_not_relevant_doc2 :
    ¬ fixture.relevant () ⟨2, by decide⟩ := by
  decide

/-- T2: doc 2 is not relevant by unjudged. -/
theorem fixture_not_relevant_doc2_by_unjudged :
    ¬ fixture.relevant () ⟨2, by decide⟩ :=
  TestCollection.not_relevant_of_unjudged fixture () ⟨2, by decide⟩ rfl

/-- T2: doc 1 is not relevant by judged nonrelevant. -/
theorem fixture_not_relevant_doc1_by_judged :
    ¬ fixture.relevant () ⟨1, by decide⟩ :=
  TestCollection.not_relevant_of_judged_nonrelevant fixture ()
    ⟨1, by decide⟩ rfl

/-- T3: ranking `![0, 2]` has precision `1 / 2`. -/
theorem fixture_precisionAt_r1 :
    precisionAt (fixture.relevant ()) r1 = 1 / 2 := by
  have hcard :
      (Finset.univ.filter fun i =>
        fixture.relevant () (r1 i)).card = 1 := by
    decide +kernel
  unfold precisionAt
  rw [hcard]
  simp

/-- T3: ranking `![2, 1]` has precision `0`. -/
theorem fixture_precisionAt_r2 :
    precisionAt (fixture.relevant ()) r2 = 0 := by
  have hcard :
      (Finset.univ.filter fun i =>
        fixture.relevant () (r2 i)).card = 0 := by
    decide +kernel
  unfold precisionAt
  rw [hcard]
  simp

/-- T4: precision over `relevant` lies in `[0, 1]`. -/
theorem fixture_precisionAt_mem_Icc :
    precisionAt (fixture.relevant ()) r1 ∈
      Set.Icc (0 : ℝ) 1 :=
  precisionAt_mem_Icc (fixture.relevant ()) r1

end Cslib.InformationRetrieval
