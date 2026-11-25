/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSED HEMISPHERE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP6] OPEN HEMISPHERE, p. 246
(comment: "The same results hold for the related CLOSED HEMISPHERE problem in which we ask that
y satisfy x·y ≥ 0 for at least K m-tuples x ∈ X [Johnson and Preparata, 1978].");
D. S. Johnson and F. P. Preparata, "The densest hemisphere problem", Theoretical
Computer Science 6 (1978), 93-107, doi:10.1016/0304-3975(78)90006-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OpenHemisphereWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosedHemisphere

open MetaMathlibExt.Complexity.NPComplete.OpenHemisphere (OpenHemisphereInstance intOf WellFormed)

/-!
# CLOSED HEMISPHERE is NP-complete

INSTANCE: a finite set `X` of `m`-tuples of integers, and a positive integer `K ≤ |X|`.
QUESTION: is there a nonzero `m`-tuple `y` of rational numbers such that `x · y ≥ 0` for at least
`K` `m`-tuples `x ∈ X`?

This is the closed variant of OPEN HEMISPHERE ([MP6], `OpenHemisphereWanted`), whose instance
encoding and well-formedness (`X` a set of `m`-tuples, `0 < K ≤ |X|`) are reused unchanged. The
tuple `y` must be nonzero: it is the normal vector of the hemisphere `{x | x · y ≥ 0}` of Johnson
and Preparata's densest hemisphere problem. Garey and Johnson's one-line statement of the closed
variant omits `y ≠ 0`; without it `y = 0` satisfies `x · y ≥ 0` for every `x ∈ X`, so every
instance would be a yes-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A nonzero rational `m`-tuple `y` with `x · y ≥ 0` for at least `K` elements `x` of `X`. -/
def ClosedHemisphereFeasible (i : OpenHemisphereInstance) : Prop :=
  ∃ y : Fin i.1 → ℚ, y ≠ 0 ∧ i.2.2 ≤
    (i.2.1.filter fun x => 0 ≤ ∑ j : Fin i.1, (intOf (x.getD j (0, 0)) : ℚ) * y j).length

open Classical in
/-- CLOSED HEMISPHERE as a decision problem over bitstrings. -/
noncomputable def closedHemisphereDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenHemisphereInstance) x with
  | some i => decide (WellFormed i ∧ ClosedHemisphereFeasible i)
  | none => false

/-- **CLOSED HEMISPHERE is NP-complete.** Source: Garey and Johnson (1979), [MP6], comment;
Johnson and Preparata (1978). -/
public theorem_wanted closedHemisphere_npComplete :
    closedHemisphereDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L closedHemisphereDec

end MetaMathlibExt.Complexity.NPComplete.ClosedHemisphere
