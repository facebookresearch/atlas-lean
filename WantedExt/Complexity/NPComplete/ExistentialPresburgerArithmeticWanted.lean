/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXISTENTIAL PRESBURGER ARITHMETIC is NP-complete

Source:
B. Scarpellini, "Complexity of subcases of Presburger arithmetic", Transactions of the American
Mathematical Society 284 (1984), 203-218, doi:10.1090/S0002-9947-1984-0742421-9 (Section 7,
Corollary 1, and Fact 1 of Section 5).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ExistentialPresburgerArithmeticDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExistentialPresburgerArithmetic

open Cslib.Logic.LegacyPL
open NonTautology (parse valuation)

/-!
# EXISTENTIAL PRESBURGER ARITHMETIC is NP-complete

INSTANCE: a closed existential formula `∃ y₀ ⋯ ∃ y_{k-1} L` of Presburger arithmetic, where
`L` is quantifier-free: a Boolean combination, with `¬`, `∧`, `∨` and `→`, of atomic formulas
`t ≤ q` between terms built from the variables, `0`, `1`, `+` and doubling. QUESTION: is the
formula true in the standard model `ℕ`?

This is Scarpellini's set `E` of closed true existential formulas, in his version of Presburger
arithmetic with the doubling function `φ₂(x) = 2x`, so that a term spells a coefficient `c` in
`O(log c)` symbols. A term denotes a linear form `a₀ y₀ + ⋯ + a_{k-1} y_{k-1} + b` with natural
coefficients, so an atomic formula is a linear inequality
`a₀ y₀ + ⋯ + a_{k-1} y_{k-1} + b ≤ c₀ y₀ + ⋯ + c_{k-1} y_{k-1} + e`; here it is given by the
coefficient lists `[a₀, ..., a_{k-1}]`, `[c₀, ..., c_{k-1}]` and the constants `b`, `e`, all in
binary. The quantifier-free part is a proposition of CSLib v4.35, restored as
`Cslib.Logic.LegacyPL.Proposition`, over the atomic formulas, written as a postfix token list and
read by `NonTautology.parse`: the token `(0, x)`
is the `x`-th atomic formula of the list, `(1, _)` is `¬`, and `(2, _)`, `(3, _)`, `(4, _)` are
`∧`, `∨`, `→`. Truth values are CSLibExt's `Proposition.evalBool` under
`NonTautology.valuation`, which makes `⊥` false. An assignment of the variables is the list
`[y₀, ..., y_{k-1}]` of their values.

Scarpellini proves that `E` is NP-hard (Section 7, from Theorem 5) and in NP (Corollary 1 of
Section 7, by his small-solution bound Theorem 6(A) from Sieveking and von zur Gathen); Fact 1
of Section 5 records that `E` is NP-complete.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EXISTENTIAL PRESBURGER ARITHMETIC is NP-complete.** Source: Scarpellini (1984). -/
public theorem_wanted existentialPresburgerArithmetic_npComplete :
    existentialPresburgerArithmeticDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L existentialPresburgerArithmeticDec

end MetaMathlibExt.Complexity.NPComplete.ExistentialPresburgerArithmetic
