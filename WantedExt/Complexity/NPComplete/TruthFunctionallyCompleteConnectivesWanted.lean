/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO10] TRUTH-FUNCTIONALLY COMPLETE
CONNECTIVES, p. 261 (reference: R. Statman (1976), private communication; transformation from
3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectivesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives

open Cslib.Logic.LegacyPL

/-!
# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of well-formed Boolean expressions over
`U`. QUESTION: is `C` truth-functionally complete, i.e., is there a truth-functionally complete
set of logical connectives (unary and binary operators) `D = {θ₁, …, θₖ}` such that for each
`θᵢ ∈ D` there is an expression `E ∈ C` and a substitution `s : U → {a, b}` for which
`s(E) ≡ a θᵢ b` or `s(E) ≡ θᵢ a` (depending on whether `θᵢ` is binary or unary)?

Expressions are those of `NonTautologyWanted` (connectives `¬`, `∧`, `∨`, `→`, written in
postfix over `U = {u₀, …, u_{n-1}}`), and `C` is a list of their token lists. A substitution is
`s : ℕ → Bool`, sending `uₓ` to `a` when `s x = true` and to `b` when `s x = false`;
`substOp E s` is the binary truth function `(a, b) ↦ s(E)`, so `s(E) ≡ a θ b` says
`substOp E s = θ`. A unary connective `θ` is represented by the binary truth function
`fun a _ => θ a`, which composes exactly as `θ` does; then `s(E) ≡ θ a` again says
`substOp E s = fun a _ => θ a`. A set `D` of connectives is truth-functionally complete when
every truth function of every arity `m ≥ 1` is a composition of members of `D` applied to the
`m` arguments. Compositions are CSLib circuits (`Cslib.Circuits.Circuit`, a straight-line program
whose gates read the inputs and earlier gates) over the signature with one binary operation
symbol per member of `D` (operation symbols `Fin D.length`, each of arity `2`), interpreted by
that member; `f` is a composition when a one-output circuit computes it
(`Circuit.Computes`, `Cslib.Circuits.single f`). Arity `0` is excluded because a composition of
unary and binary connectives always mentions an argument; this is the logician's convention
under which `{NAND}` is complete, and it is why the statement does not use CSLib's
`Interpretation.IsComplete`, which also asks for circuits with no inputs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES is NP-complete.** Source: Garey and Johnson
(1979), [LO10] (Statman, 1976). -/
public theorem_wanted truthFunctionallyCompleteConnectives_npComplete :
    truthFunctionallyCompleteConnectivesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L truthFunctionallyCompleteConnectivesDec

end MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives
