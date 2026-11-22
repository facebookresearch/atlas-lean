/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.CFGRecognizability

@[expose] public section

/-!
# Tests for the recognizability of PCP and of problems about context-free grammars
-/

set_option autoImplicit false

open Cslib.Language Cslib.Decidability Cslib.Decidability.Post

namespace CSLibExtTest.Computability.Decidability.CFGRecognizability

/-- The complement of PCP is not recognizable. -/
example : ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α),
    ¬TM2Recognizable fun P : List (Domino α) ↦ ¬PCP P :=
  exists_not_tm2Recognizable_not_pcp

/-- `OVERLAP_CFG` over `Bool` is recognizable, and `ALL_CFG` over `Bool` is co-recognizable. -/
example : TM2Recognizable fun g : EncodedCFG Bool × EncodedCFG Bool ↦
    ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language :=
  tm2Recognizable_overlap

example : TM2CoRecognizable fun g : EncodedCFG Bool ↦ ∀ w, w ∈ g.language :=
  tm2CoRecognizable_univ

example : TM2CoRecognizable fun g : EncodedCFG Bool × EncodedCFG Bool ↦
    g.1.language = g.2.language :=
  tm2CoRecognizable_language_eq

example : TM2CoRecognizable fun g : EncodedCFG Bool × EncodedCFG Bool ↦
    g.1.language ≤ g.2.language :=
  tm2CoRecognizable_language_le

/-- `ALL_CFG` is co-recognizable but not decidable, so it is not recognizable. -/
example : ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Recognizable fun g : EncodedCFG T ↦ ∀ w, w ∈ g.language :=
  exists_not_tm2Recognizable_univ

example : ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Recognizable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language = g.2.language :=
  exists_not_tm2Recognizable_language_eq

example : ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Recognizable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language ≤ g.2.language :=
  exists_not_tm2Recognizable_language_le

example : ∃ (T : Type) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Recognizable fun g : EncodedCFG T × EncodedCFG T ↦
      ∀ w, ¬(w ∈ g.1.language ∧ w ∈ g.2.language) :=
  exists_not_tm2Recognizable_disjoint

/-- Post's theorem, contrapositive, on the halting problem. -/
example : ¬TM2Recognizable fun c : Nat.Partrec.Code ↦ ¬(c.eval 0).Dom :=
  not_tm2Recognizable_not_of (tm2Recognizable_halting 0) (not_tm2Decidable_halting 0)

end CSLibExtTest.Computability.Decidability.CFGRecognizability
