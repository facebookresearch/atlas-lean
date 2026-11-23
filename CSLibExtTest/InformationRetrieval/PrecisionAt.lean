/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.PrecisionAt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for precision at a cutoff
-/

set_option autoImplicit false

open Cslib.InformationRetrieval

namespace CSLibExtTest.InformationRetrieval.PrecisionAt

/-- The empty-cutoff convention, as an example. -/
example {N : ℕ} (rel : Fin N → Prop) [DecidablePred rel]
    (r : Fin 0 → Fin N) : precisionAt rel r = 0 :=
  precisionAt_zero_cutoff rel r

/-- The interval bound, as an example. -/
example {N k : ℕ} (rel : Fin N → Prop) [DecidablePred rel]
    (r : Fin k → Fin N) : precisionAt rel r ∈ Set.Icc (0 : ℝ) 1 :=
  precisionAt_mem_Icc rel r

/-- If every candidate is relevant, a two-position prefix has precision `1`. -/
example (r : Fin 2 → Fin 3) : precisionAt (fun _ => True) r = 1 := by
  norm_num [precisionAt, Finset.card_univ, Fintype.card_fin]

/-- If no candidate is relevant, a two-position prefix has precision `0`. -/
example (r : Fin 2 → Fin 3) : precisionAt (fun _ => False) r = 0 := by
  simp [precisionAt]

end CSLibExtTest.InformationRetrieval.PrecisionAt
