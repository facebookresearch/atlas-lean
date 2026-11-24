/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBSET PRODUCT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SUBSET PRODUCT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubsetProduct

/-!
# SUBSET PRODUCT is NP-complete

A list of positive natural numbers and a target `T`. The question is whether some sublist has
product exactly `T`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SUBSET PRODUCT instances.** An instance of SUBSET PRODUCT is a pair $(a, T)$ of a finite
list $a$ of natural numbers and a target natural number $T$. -/
abbrev SubsetProductInstance := List ℕ × ℕ

/-- **Well-formed SUBSET PRODUCT instances.** An instance $(a, T)$ of SUBSET PRODUCT, with $a$ a
finite list of natural numbers and $T$ a natural number, is well formed when every entry of $a$
is positive. -/
def WellFormed (i : SubsetProductInstance) : Prop :=
  ∀ a ∈ i.1, 0 < a

/-- **Feasible SUBSET PRODUCT instances.** An instance $(a, T)$ of SUBSET PRODUCT, with $a$ a
finite list of natural numbers and $T$ a natural number, is feasible when some sublist of $a$ (a
list obtained from $a$ by deleting entries and keeping the order of the rest) has product exactly
$T$. -/
def SubsetProductFeasible
    (i : SubsetProductInstance) : Prop :=
  ∃ s : List ℕ, s.Sublist i.1 ∧ s.prod = i.2

open Classical in
/-- **SUBSET PRODUCT as a decision problem.** The decision problem SUBSET PRODUCT accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a finite
list of natural numbers and a natural number, to an instance $(a, T)$ that is well formed (every
entry of $a$ is positive) and feasible (some sublist of $a$ has product exactly $T$). It rejects
every bitstring that does not decode to an instance. -/
noncomputable def subsetProductDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubsetProductInstance) x with
  | some i => decide (WellFormed i ∧ SubsetProductFeasible i)
  | none => false

/-- **SUBSET PRODUCT is NP-complete.** The decision problem SUBSET PRODUCT lies in NP, and every
decision problem in NP has a polynomial-time many-one reduction to SUBSET PRODUCT.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SUBSET PRODUCT. -/
public theorem_wanted subsetProduct_npComplete :
    subsetProductDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L subsetProductDec

end MetaMathlibExt.Complexity.NPComplete.SubsetProduct
