/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.PCPApplications

@[expose] public section

/-!
# Tests for the undecidable problems about context-free grammars
-/

set_option autoImplicit false

open Cslib.Language Cslib.Decidability

namespace CSLibExtTest.Computability.Decidability.PCPApplications

example : ∃ (T : Type) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Decidable fun g : EncodedCFG T × EncodedCFG T ↦ ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language :=
  exists_not_tm2Decidable_overlap

example : ∃ (T : Type) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Decidable fun g : EncodedCFG T × EncodedCFG T ↦
      ∀ w, ¬(w ∈ g.1.language ∧ w ∈ g.2.language) :=
  exists_not_tm2Decidable_disjoint

example : ∃ (T : Type) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Decidable fun g : EncodedCFG T ↦ IsAmbiguous g.toCFG :=
  exists_not_tm2Decidable_isAmbiguous

example : ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Decidable fun g : EncodedCFG T ↦ ∀ w, w ∈ g.language :=
  exists_not_tm2Decidable_univ

example : ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Decidable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language = g.2.language :=
  exists_not_tm2Decidable_language_eq

example : ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Decidable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language ≤ g.2.language :=
  exists_not_tm2Decidable_language_le

/-- The all-words grammar over `Bool` generates `[true, false]`. -/
example : [true, false] ∈ (allWordsCFG (T := Bool)).language := mem_language_allWordsCFG _

end CSLibExtTest.Computability.Decidability.PCPApplications
