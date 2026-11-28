/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXTERNAL MACRO DATA COMPRESSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA
COMPRESSION, p. 231 (references [Storer, 1977], [Storer and Szymanski, 1978]; transformation
from VERTEX COVER);
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ExternalMacroDataCompressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompression

/-!
# EXTERNAL MACRO DATA COMPRESSION is NP-complete

INSTANCE: an alphabet `Σ`, a string `s ∈ Σ*`, a pointer cost `h ∈ Z⁺`, and a bound `B ∈ Z⁺`.
QUESTION: are there strings `D` (dictionary string) and `C` (compressed string) in
`(Σ ∪ {pᵢ : 1 ≤ i ≤ |s|})*`, where the symbols `pᵢ` are "pointers", such that
`|D| + |C| + (h - 1) · (number of occurrences of pointers in D and C) ≤ B` and such that there
is a way of identifying pointers with substrings of `D` so that `s` can be obtained from `C` by
repeatedly replacing pointers in `C` by their corresponding substrings in `D`?

The alphabet is `Σ = {0, …, k - 1}`. A symbol of `Σ ∪ {pᵢ}` is `Sum.inl a` (the letter `a`) or
`Sum.inr j` (the pointer `p_{j+1}`, indexed from `0`); `IsOver k m u` says that `u` uses only
letters below `k` and pointers `p₁, …, p_m`. The identification of pointers with substrings of
`D` is a map `σ` with `σ j` a contiguous substring (`List.IsInfix`) of `D` for every pointer.
`ReplaceStep σ u v` replaces one occurrence of a pointer `p` in `u` by `σ p`, and `s` is obtained
from `C` when the reflexive-transitive closure of these steps leads from `C` to `s`. Substrings
of `D` may themselves contain pointers, which later steps replace in turn ("repeatedly").
`Compresses k s c B` states the question for a pointer cost `c`, so that variants with another
pointer cost (the [SR22] comment) can reuse it. `C = s` with `D` empty shows that every
`B ≥ |s|` is a yes-instance, so the binary encoding of `B` does not affect membership in `NP`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EXTERNAL MACRO DATA COMPRESSION is NP-complete.** Source: Garey and Johnson (1979),
[SR22]; Storer and Szymanski (1982). -/
public theorem_wanted externalMacroDataCompression_npComplete :
    externalMacroDataCompressionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L externalMacroDataCompressionDec

end MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompression
