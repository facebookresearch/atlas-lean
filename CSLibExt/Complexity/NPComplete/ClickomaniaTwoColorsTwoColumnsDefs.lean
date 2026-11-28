/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLICKOMANIA with two colors and two columns: definitions

Source:
A. Adler, E. D. Demaine, A. Hesterberg, Q. Liu and M. Rudoy, "Clickomania is hard, even with
two colors and columns", in J. Beineke and J. Rosenhouse (eds.), *The Mathematics of Various
Entertaining Subjects, Vol. 2*, Princeton University Press (2017),
doi:10.23943/princeton/9780691171920.003.0018, Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ClickomaniaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClickomaniaTwoColorsTwoColumns

open MetaMathlibExt.Complexity.NPComplete.Clickomania

/-- Well-formedness of an instance: a well-formed CLICKOMANIA board (a full rectangle with at
least one block) with at most two columns and at most two colors. -/
def WellFormed (B : Board) : Prop :=
  Clickomania.WellFormed B ∧ B.length ≤ 2 ∧ ∃ a b : ℕ, ∀ col ∈ B, ∀ x ∈ col, x = a ∨ x = b

open Classical in
/-- CLICKOMANIA with two colors and two columns as a decision problem over bitstrings. -/
noncomputable def clickomaniaTwoColorsTwoColumnsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := Board) x with
  | some i => decide (WellFormed i ∧ ClickomaniaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ClickomaniaTwoColorsTwoColumns
