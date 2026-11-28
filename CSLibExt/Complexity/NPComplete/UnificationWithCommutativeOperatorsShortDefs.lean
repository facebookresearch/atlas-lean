/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsDefs

/-!
# UNIFICATION WITH COMMUTATIVE OPERATORS with short expressions: definitions

INSTANCE: a set `V` of variables, a set `C` of constants, and ordered pairs `(eᵢ, fᵢ)`,
`1 ≤ i ≤ n`, of expressions, where an expression is either a variable from `V`, a constant
from `C`, or `(e + f)` where `e` and `f` are expressions, and no `eᵢ` or `fᵢ` contains more
than 7 occurrences of constants and variables (the comment's restriction). QUESTION: is there
an assignment to each `v ∈ V` of a variable-free expression `I(v)` such that `I(eᵢ) ≡ I(fᵢ)`
for `1 ≤ i ≤ n`, where `e ≡ f` if and only if `e = f`, or `e = (a + b)`, `f = (c + d)` and
either `a ≡ c` and `b ≡ d`, or `a ≡ d` and `b ≡ c`?

The instance, its token encoding and the question are those of
`UnificationWithCommutativeOperatorsDefs`
(`UnificationWithCommutativeOperators.UnificationWithCommutativeOperatorsInstance`,
`UnificationWithCommutativeOperators.WellFormed` and
`UnificationWithCommutativeOperators.UnificationWithCommutativeOperatorsFeasible`). In the
prefix token list of an expression, the occurrences of variables and constants are exactly
the tokens `(0, v)` and `(1, c)` (every other token is `(2, 0)`, the operator `+`), so
`WellFormed` adds that each of the two token lists of each pair has at most 7 tokens whose
first component is not `2` (`leafCount`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN16] UNIFICATION
WITH COMMUTATIVE OPERATORS, p. 252, comment: "Remains NP-complete even if no `eᵢ` or `fᵢ`
contains more than 7 occurrences of constants and variables" (the entry credits the problem
to R. Sethi, private communication, 1977; the original was not available).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShort

open MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperators

/-- The number of occurrences of variables and constants in an expression given by its prefix
token list: the tokens `(0, v)` and `(1, c)`, i.e., those that are not the operator `(2, 0)`. -/
def leafCount (ts : List (ℕ × ℕ)) : ℕ :=
  ts.countP fun t => t.1 ≠ 2

/-- Well-formedness of an instance: it is a well-formed instance of UNIFICATION WITH
COMMUTATIVE OPERATORS, and no `eᵢ` or `fᵢ` contains more than 7 occurrences of constants and
variables. -/
def WellFormed (i : UnificationWithCommutativeOperatorsInstance) : Prop :=
  UnificationWithCommutativeOperators.WellFormed i ∧
    ∀ p ∈ i.2.2, leafCount p.1 ≤ 7 ∧ leafCount p.2 ≤ 7

open Classical in
/-- UNIFICATION WITH COMMUTATIVE OPERATORS with short expressions as a decision problem over
bitstrings. -/
noncomputable def unificationWithCommutativeOperatorsShortDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnificationWithCommutativeOperatorsInstance) x with
  | some i => decide (WellFormed i ∧ UnificationWithCommutativeOperatorsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShort
