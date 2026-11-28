/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KD45 SATISFIABILITY (single-agent belief): definitions

Source:
J. Y. Halpern and Y. Moses, "A guide to completeness and complexity for modal logics of
knowledge and belief", Artificial Intelligence 54 (1992), 319-379,
doi:10.1016/0004-3702(92)90049-4 (preliminary version: Proc. IJCAI-85, 480-490, Theorems 14
and 15);
J. Y. Halpern and L. C. Rêgo, "Characterizing the NP-PSPACE gap in the satisfiability problem
for modal logic", Journal of Logic and Computation 17 (2007), 795-806,
doi:10.1093/logcom/exm029.
-/
module

public import Cslib.Foundations.Relation.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ModalLogicS5SatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KD45Satisfiability

open Cslib.Modal
open MetaMathlibExt.Complexity.NPComplete.ModalLogicS5Satisfiability
  (ModalLogicS5SatisfiabilityInstance parse)

/-- The formula is true at some world of a Kripke model whose accessibility relation is
serial, transitive and Euclidean. -/
def KD45SatisfiabilityFeasible (i : ModalLogicS5SatisfiabilityInstance) : Prop :=
  ∃ φ, parse i.2 [] = some φ ∧
    ∃ (W : Type) (M : KripkeModel W ℕ) (w : W),
      Relation.Serial M.rel ∧ IsTrans W M.rel ∧ Relation.RightEuclidean M.rel ∧ M.Satisfies w φ

open Classical in
/-- KD45 SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def kd45SatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ModalLogicS5SatisfiabilityInstance) x with
  | some i => decide (ModalLogicS5Satisfiability.WellFormed i ∧ KD45SatisfiabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KD45Satisfiability
