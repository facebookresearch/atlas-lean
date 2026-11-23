/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC CONGRUENCES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN1] QUADRATIC
CONGRUENCES;
K. L. Manders and L. M. Adleman, "NP-complete decision problems for binary
quadratics", Journal of Computer and System Sciences 16 (1978), 168-184,
doi:10.1016/0022-0000(78)90044-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.ModEq

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticCongruences

/-!
# QUADRATIC CONGRUENCES is NP-complete

INSTANCE: positive integers `a`, `b` and `c`. QUESTION: is there a positive integer `x < c`
such that `x² ≡ a (mod b)`?

The numbers use the canonical binary encoding; the problem is NP-complete in the weak sense
(trying every `x < c` takes time pseudo-polynomial in `c`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the numbers `(a, b, c)`. -/
abbrev QuadraticCongruencesInstance := ℕ × ℕ × ℕ

/-- Well-formedness of an instance: `a`, `b` and `c` are positive. -/
def WellFormed (i : QuadraticCongruencesInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some positive `x < c` satisfies `x ^ 2 ≡ a [MOD b]`. -/
def QuadraticCongruencesFeasible (i : QuadraticCongruencesInstance) : Prop :=
  ∃ x : ℕ, 0 < x ∧ x < i.2.2 ∧ x ^ 2 ≡ i.1 [MOD i.2.1]

open Classical in
/-- QUADRATIC CONGRUENCES as a decision problem over bitstrings. -/
noncomputable def quadraticCongruencesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuadraticCongruencesInstance) x with
  | some i => decide (WellFormed i ∧ QuadraticCongruencesFeasible i)
  | none => false

/-- **QUADRATIC CONGRUENCES is NP-complete.** Source: Garey and Johnson (1979), [AN1];
Manders and Adleman (1978). -/
public theorem_wanted quadraticCongruences_npComplete :
    quadraticCongruencesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticCongruencesDec

end MetaMathlibExt.Complexity.NPComplete.QuadraticCongruences
