/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SMALLEST GRAMMAR: definitions

Source:
M. Charikar, E. Lehman, D. Liu, R. Panigrahy, M. Prabhakaran, A. Sahai, and A. Shelat, "The
smallest grammar problem", IEEE Transactions on Information Theory 51 (2005), 2554-2576,
doi:10.1109/TIT.2005.850116, Sections I, IV-A and V-A;
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Computability.ContextFreeGrammar

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SmallestGrammar

/-- An instance: the string `w` and the bound `K`. -/
abbrev SmallestGrammarInstance := List ℕ × ℕ

/-- The size of a grammar: the total number of symbols on the right sides of all its rules. -/
def grammarSize (g : ContextFreeGrammar ℕ) : ℕ :=
  ∑ r ∈ g.rules, r.output.length

/-- Some context-free grammar of size at most `K` generates exactly the string `w`. -/
def SmallestGrammarFeasible (i : SmallestGrammarInstance) : Prop :=
  ∃ g : ContextFreeGrammar ℕ, g.language = {i.1} ∧ grammarSize g ≤ i.2

open Classical in
/-- SMALLEST GRAMMAR as a decision problem over bitstrings. -/
noncomputable def smallestGrammarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SmallestGrammarInstance) x with
  | some i => decide (SmallestGrammarFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SmallestGrammar
