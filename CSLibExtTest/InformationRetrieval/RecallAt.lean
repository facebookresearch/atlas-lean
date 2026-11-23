/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.RecallAt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for recall at a cutoff
-/

set_option autoImplicit false

open Cslib.InformationRetrieval

namespace CSLibExtTest.InformationRetrieval.RecallAt

/-- With no relevant candidates, recall is zero by convention. -/
example {N k : ℕ} (r : Fin k → Fin N) :
    recallAt (fun _ => False) r = 0 :=
  recallAt_eq_zero_of_no_relevant _ r (by simp)

/-- The interval bound for an injective ranked prefix, as an example. -/
example {N k : ℕ} (rel : Fin N → Prop) [DecidablePred rel]
    {r : Fin k → Fin N} (hr : Function.Injective r) :
    recallAt rel r ∈ Set.Icc (0 : ℝ) 1 :=
  recallAt_mem_Icc rel hr

/-- Retrieving every candidate when all are relevant has recall `1`. -/
example : recallAt (fun _ => True) (fun i : Fin 3 => i) = 1 := by
  norm_num [recallAt, Finset.card_univ, Fintype.card_fin]

/-- Retrieving two of three relevant candidates has recall `2 / 3`, unlike
precision at cutoff `2`, which would be `1` for this all-relevant prefix. -/
example : recallAt (fun _ => True) (![0, 1] : Fin 2 → Fin 3) = 2 / 3 := by
  norm_num [recallAt, Finset.card_univ, Fintype.card_fin]

end CSLibExtTest.InformationRetrieval.RecallAt
