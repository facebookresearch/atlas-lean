/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGISTER SUFFICIENCY FOR LOOPS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO3] REGISTER
SUFFICIENCY FOR LOOPS;
M. R. Garey, D. S. Johnson, G. L. Miller, and C. H. Papadimitriou, "The
complexity of coloring circular arcs and chords", SIAM Journal on Algebraic and
Discrete Methods 1 (1980), 216-227, doi:10.1137/0601025.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RegisterSufficiencyForLoopsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegisterSufficiencyForLoops

/-!
# REGISTER SUFFICIENCY FOR LOOPS is NP-complete

INSTANCE: a set `V` of loop variables, a loop length `N ∈ ℤ⁺`, for each variable `v ∈ V` a start
time `s(v) ∈ ℤ₀⁺` and a duration `l(v) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: can the loop
variables be safely stored in `K` registers, i.e., is there an assignment `f : V → {1, …, K}`
such that if `f(v) = f(u)` for some `u ≠ v ∈ V`, then `s(u) ≤ s(v)` implies `s(u) + l(u) ≤ s(v)`
and `s(v) + l(v) (mod N) ≤ s(u)`?

Variable `v` occupies its register during the time slots `s(v), s(v) + 1, …, s(v) + l(v) - 1`
of the loop, read modulo `N` because the loop repeats; two variables may share a register
exactly when these residue sets are disjoint. This is the source condition with its
"`(mod N)`" read as wrap-around: for `s(u) ≤ s(v) < N` and durations at most `N`, the slot sets
of `u` and `v` are disjoint iff `s(u) + l(u) ≤ s(v)` (`u` ends before `v` starts) and
`s(v) + l(v) ≤ s(u) + N` (`v`, wrapping past the end of the loop, ends before `u` starts in the
next iteration). Equivalently, `f` is a proper `K`-coloring of the circular-arc graph of the
arcs `[s(v), s(v) + l(v))` on a circle of length `N`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REGISTER SUFFICIENCY FOR LOOPS is NP-complete.** Source: Garey and Johnson (1979), [PO3];
Garey, Johnson, Miller, and Papadimitriou (1980). -/
public theorem_wanted registerSufficiencyForLoops_npComplete :
    registerSufficiencyForLoopsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L registerSufficiencyForLoopsDec

end MetaMathlibExt.Complexity.NPComplete.RegisterSufficiencyForLoops
