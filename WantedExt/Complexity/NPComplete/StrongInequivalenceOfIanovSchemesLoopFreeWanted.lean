/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG INEQUIVALENCE OF IANOV SCHEMES (loop-free, trivial `P₂`) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO16] STRONG INEQUIVALENCE OF
IANOV SCHEMES, p. 276 (comment: remains NP-complete even if neither program contains any
loops and `P₂` is the trivial program that leaves the value of `x` unchanged; references
[Constable, Hunt, and Sahni, 1974] and [Rutledge, 1964]);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031
(journal version of the 1974 Cornell report GJ cites: strong equivalence of single variable
program schemes is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesLoopFree

/-!
# STRONG INEQUIVALENCE OF IANOV SCHEMES (loop-free, trivial `P₂`) is NP-complete

INSTANCE: finite sets `F` and `P` of function and predicate symbols, a single variable `x`,
and two Ianov schemes over `F`, `P` and `x`, each a sequence `I₁, I₂, …, Iₘ` of instructions
of the form `x ← f(x)`, `if p(x) then goto Iⱼ else goto Iₖ`, and `halt`, where `f ∈ F` and
`p ∈ P`; neither program contains any loops, and `P₂` is the trivial program that leaves the
value of `x` unchanged.
QUESTION: are the two given Ianov schemes not strongly equivalent, i.e., is there a domain
set `D`, an interpretation of each `f ∈ F` as a function `f : D → D`, an interpretation of
each `p ∈ P` as a function `p : D → {T, F}`, and an initial value `x₀ ∈ D` for `x`, such that
either both schemes halt with different final values for `x` or one halts and the other
doesn't?

This is the restriction of `WantedExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesWanted`
named in the source's comment. The instance type, the scheme encoding and semantics, the
parent well-formedness condition and the question are that module's
(`StrongInequivalenceOfIanovSchemes.StrongInequivalenceOfIanovSchemesInstance`,
`StrongInequivalenceOfIanovSchemes.WellFormed`,
`StrongInequivalenceOfIanovSchemes.StrongInequivalenceOfIanovSchemesFeasible`); the
restriction is added to `WellFormed`:

* a scheme contains no loop when its control-flow relation `Next` (from an assignment `Iᶜ`
  to `I_{c+1}`, from a test to both of its jump targets) has no cycle;
* the trivial program that leaves `x` unchanged is the one-instruction scheme `halt`,
  `[(2, 0, 0, 0)]`, which has no loop either.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The control-flow relation of a scheme on `0`-based instruction indices: an assignment
`x ← f_r(x)` at index `c` passes control to `c + 1`, and a test
`if p_r(x) then goto Iⱼ else goto Iₖ` at index `c` passes control to `j - 1` or `k - 1`. -/
def Next (S : StrongInequivalenceOfIanovSchemes.IanovScheme) (c d : ℕ) : Prop :=
  (∃ r, S[c]? = some (0, r, 0, 0) ∧ d = c + 1) ∨
    ∃ r j k, S[c]? = some (1, r, j, k) ∧ (d = j - 1 ∨ d = k - 1)

/-- A scheme contains no loop: no instruction can reach itself along `Next`. -/
def LoopFree (S : StrongInequivalenceOfIanovSchemes.IanovScheme) : Prop :=
  ∀ c, ¬ Relation.TransGen (Next S) c c

/-- Well-formedness of an instance: it is a well-formed STRONG INEQUIVALENCE OF IANOV SCHEMES
instance (both lists are schemes over `F` and `P`), neither scheme contains a loop, and the
second scheme is the trivial scheme `halt`. -/
def WellFormed
    (i : StrongInequivalenceOfIanovSchemes.StrongInequivalenceOfIanovSchemesInstance) : Prop :=
  StrongInequivalenceOfIanovSchemes.WellFormed i ∧ LoopFree i.2.2.1 ∧ LoopFree i.2.2.2 ∧
    i.2.2.2 = [(2, 0, 0, 0)]

open Classical in
/-- STRONG INEQUIVALENCE OF IANOV SCHEMES for a loop-free scheme and the trivial scheme as a
decision problem over bitstrings. -/
noncomputable def strongInequivalenceOfIanovSchemesLoopFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StrongInequivalenceOfIanovSchemes.StrongInequivalenceOfIanovSchemesInstance) x with
  | some i =>
      decide (WellFormed i ∧
        StrongInequivalenceOfIanovSchemes.StrongInequivalenceOfIanovSchemesFeasible i)
  | none => false

/-- **STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete for a loop-free scheme and the
trivial scheme.** Source: Garey and Johnson (1979), [PO16]; Constable, Hunt and Sahni
(1980). -/
public theorem_wanted strongInequivalenceOfIanovSchemesLoopFree_npComplete :
    strongInequivalenceOfIanovSchemesLoopFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongInequivalenceOfIanovSchemesLoopFreeDec

end MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesLoopFree
