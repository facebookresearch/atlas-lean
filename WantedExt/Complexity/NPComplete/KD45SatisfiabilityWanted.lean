/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KD45 SATISFIABILITY (single-agent belief) is NP-complete

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

public import Batteries.Util.ProofWanted
public import Cslib.Foundations.Relation.Defs
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ModalLogicS5SatisfiabilityWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KD45Satisfiability

open Cslib.Modal
open MetaMathlibExt.Complexity.NPComplete.ModalLogicS5Satisfiability
  (ModalLogicS5SatisfiabilityInstance parse)

/-!
# KD45 SATISFIABILITY (single-agent belief) is NP-complete

INSTANCE: a formula `φ` of propositional modal logic with one modal operator.
QUESTION: is `φ` satisfiable in a KD45 structure, that is, true at some world of a Kripke
structure whose accessibility relation is serial, transitive and Euclidean?

The instance format is that of `ModalLogicS5SatisfiabilityWanted` and is reused unchanged: the
number `n` of primitive propositions `u₀, …, u_{n-1}` and the formula as a postfix token list
(`0` is `∧`, `1` is `¬`, `2` is the modal operator `□`, `k + 3` is `uₖ`), read by its `parse`
into `Cslib.Modal.Formula ℕ`, with its `WellFormed` (the tokens form a formula over the `n`
propositions). Satisfaction is `Cslib.Modal.KripkeModel.Satisfies`. The frame conditions are
those of CSLib's modal logic `D45` (`Cslib.Logic.Modal.Unimodal.D45`): `Relation.Serial` (every
world has a successor), `IsTrans` and `Relation.RightEuclidean` (`r a b` and `r a c` give
`r b c`).

Halpern and Moses prove that KD45 is sound and complete for Euclidean, transitive and serial
structures and that deciding satisfiability of KD45 formulas is NP-complete with one agent and
PSPACE-complete with two or more; Halpern and Rêgo prove NP-completeness of the satisfiability
problem for every modal logic containing K5, KD45 among them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **KD45 SATISFIABILITY (single-agent belief) is NP-complete.** Source: Halpern and Moses
(1992); Halpern and Rêgo (2007). -/
public theorem_wanted kd45Satisfiability_npComplete :
    kd45SatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kd45SatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.KD45Satisfiability
