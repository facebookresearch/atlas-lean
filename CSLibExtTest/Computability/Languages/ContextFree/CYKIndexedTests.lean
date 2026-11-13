/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Languages.ContextFree.CYKIndexed.Encoded

/-!
# Indexed CYK consumers and boundary tests

These kernel-reduced examples exercise actual indexed execution, not a
callback with assumed answers. Language claims use the canonical bridge.
-/

@[expose] public section

namespace Cslib.Language.CYKIndexedTests

open CYKIndexed

/-- A recursive CNF grammar for nonempty strings of `true`. -/
def positive : EncodedCFG Bool :=
  ⟨0, [(0, [.inl 0, .inl 0]), (0, [.inr true])]⟩

/-- The recursive test grammar satisfies the actual CNF interface. -/
theorem positive_cnf : IsChomskyNormalForm positive.toCFG := by
  simp [IsChomskyNormalForm, positive, EncodedCFG.toCFG,
    EncodedCFG.decodeRule, EncodedCFG.decodeSymbol]

/-- A populated recognizer result with multiple equal proper substrings. -/
theorem repeated_accepts :
    (recognizesEncoded 1 1 positive [true, true, true, true]).ret = true := by
  decide

/-- Actual execution implies a canonical language statement. -/
theorem repeated_in_language :
    [true, true, true, true] ∈ positive.language :=
  (recognizesEncoded_iff 1 1 positive positive_cnf _).1 repeated_accepts

/-- Lengths zero, one and two distinguish epsilon, terminals and binaries. -/
theorem short_words :
    (recognizesEncoded 1 1 positive []).ret = false ∧
    (recognizesEncoded 1 1 positive [true]).ret = true ∧
    (recognizesEncoded 1 1 positive [false]).ret = false ∧
    (recognizesEncoded 1 1 positive [true, true]).ret = true ∧
    (recognizesEncoded 1 1 positive [true, false]).ret = false := by decide

/-- Failure propagates through either side of a binary split. -/
theorem mixed_words :
    (recognizesEncoded 1 1 positive [false, true, true]).ret = false ∧
    (recognizesEncoded 1 1 positive [true, false, true]).ret = false ∧
    (recognizesEncoded 1 1 positive [true, true, false]).ret = false := by
  decide

/-- CNF grammar with start epsilon and an ordered two-letter production. -/
def nullable : EncodedCFG Bool :=
  ⟨0, [(0, []), (0, [.inl 1, .inl 2]),
    (1, [.inr true]), (2, [.inr false])]⟩

/-- The start does not occur in outputs when an epsilon rule is present. -/
theorem nullable_cnf : IsChomskyNormalForm nullable.toCFG := by
  simp [IsChomskyNormalForm, nullable, EncodedCFG.toCFG,
    EncodedCFG.decodeRule, EncodedCFG.decodeSymbol]

/-- Epsilon, singletons, order and overlong words are distinguished. -/
theorem nullable_words :
    (recognizesEncoded 1 1 nullable []).ret = true ∧
    (recognizesEncoded 1 1 nullable [true]).ret = false ∧
    (recognizesEncoded 1 1 nullable [true, false]).ret = true ∧
    (recognizesEncoded 1 1 nullable [false, true]).ret = false ∧
    (recognizesEncoded 1 1 nullable [true, false, false]).ret = false := by
  decide

/-- Epsilon acceptance reaches the existing language definition. -/
theorem nil_in_language : [] ∈ nullable.language :=
  (recognizesEncoded_iff 1 1 nullable nullable_cnf []).1 (by decide)

/-- Empty rule sets and non-start epsilon rules do not accept by accident. -/
theorem empty_and_unreachable :
    (recognizesEncoded 1 1 (⟨7, []⟩ : EncodedCFG Bool) []).ret = false ∧
    (recognizesEncoded 1 1 (⟨7, []⟩ : EncodedCFG Bool) [true]).ret = false ∧
    (recognizesEncoded 1 1 (⟨7, [(6, [])]⟩ : EncodedCFG Bool) []).ret =
      false := by decide

/-- Nonterminals need not be dense; duplicate rules preserve acceptance. -/
theorem sparse_and_duplicate :
    (recognizesEncoded 2 3 (⟨1000, [(1000, [.inr true]),
      (1000, [.inr true])]⟩ : EncodedCFG Bool) [true]).ret = true ∧
    (recognizesEncoded 2 3 (⟨999, [(1000, [.inr true])]⟩ : EncodedCFG Bool)
      [true]).ret = false := by decide

/-- Membership covers empty, first, last, duplicate and absent elements. -/
theorem member_boundaries :
    (member 3 0 ([] : List ℕ)).ret = false ∧
    (member 3 0 [0, 1, 2]).ret = true ∧
    (member 3 2 [0, 1, 2]).ret = true ∧
    (member 3 1 [1, 1]).ret = true ∧
    (member 3 3 [0, 1, 2]).ret = false ∧
    (member 3 3 [0, 1, 2]).time = 19 := by decide

/-- Terminal symbols and nonterminal symbols are never conflated. -/
theorem output_boundaries :
    (fits 1 1 #[true] (#[] : Array (Array (List ℕ))) 0 1
      [.terminal true]).ret = true ∧
    (fits 1 1 #[true] (#[] : Array (Array (List ℕ))) 0 1
      [.nonterminal 0]).ret = false ∧
    (fits 1 1 #[true] (#[] : Array (Array (List ℕ))) 0 1
      [.terminal true, .terminal true]).ret = false ∧
    (fits 1 1 #[true] (#[] : Array (Array (List ℕ))) 1 1
      [.terminal true]).ret = false := by decide

/-- Distinct positions for repeated factors survive later row updates. -/
theorem indexed_positions :
    let rs := (decodeRules positive.rules).ret
    let tbl := (table 1 1 #[true, true] rs 2).ret
    lookup tbl 0 1 = [0] ∧ lookup tbl 1 1 = [0] ∧
    lookup tbl 0 2 = [0] ∧ lookup tbl 1 2 = [] ∧
    lookup tbl 2 1 = [] ∧ lookup tbl 0 0 = [] ∧
    lookup tbl 0 3 = [] := by decide

/-- Neither endpoint is a proper binary split, even with nonempty row zero. -/
theorem proper_split_only :
    let tbl : Array (Array (List ℕ)) :=
      #[#[[7, 8], [7, 8], [7, 8]], #[[], [], []], #[[7, 8], [], []]]
    (fits 1 1 #[true, true] tbl 0 2
      [.nonterminal 7, .nonterminal 8]).ret = false ∧
    (fits 1 1 #[true, true] tbl 0 1
      [.nonterminal 7, .nonterminal 8]).ret = false := by decide

/-- One symbolic consumer specializes the whole charged bound, not just
loop arithmetic, to an actual recursive grammar. -/
theorem positive_time (w : List Bool) :
    (recognizesEncoded 1 1 positive w).time ≤ 180 * (w.length + 1) ^ 3 := by
  simpa [positive] using recognizesEncoded_time_le 1 1 positive w

/-- Canonical CYK and indexed CYK agree on every word, not just the probes. -/
theorem canonical_agreement (w : List Bool) :
    (recognizesEncoded 1 1 positive w).ret = cykAccepts positive.toCFG w := by
  exact recognizes_eq_cykAccepts positive_cnf 1 1 _
    (fun r => by simp [decodeRules_ret, EncodedCFG.toCFG]) w

end Cslib.Language.CYKIndexedTests
