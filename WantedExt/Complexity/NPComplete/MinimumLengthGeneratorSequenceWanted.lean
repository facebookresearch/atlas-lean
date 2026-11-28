/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM LENGTH GENERATOR SEQUENCE is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 288-300,
doi:10.1016/0196-6774(82)90026-8, problem [5] MINIMUM LENGTH GENERATOR SEQUENCE;
S. Even and O. Goldreich, "The minimum-length generator sequence problem is NP-hard",
J. Algorithms 2 (1981), 311-313, doi:10.1016/0196-6774(81)90029-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumLengthGeneratorSequenceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumLengthGeneratorSequence

/-!
# MINIMUM LENGTH GENERATOR SEQUENCE is NP-complete

INSTANCE: a set `{gᵢ : 1 ≤ i ≤ k}` of generators of a permutation group `G`, a target
permutation `P ∈ G`, and a positive integer `K`.
QUESTION: is there a sequence `g_{i₁}, g_{i₂}, …, g_{i_j}`, `j ≤ K`, such that
`P = g_{i₁} g_{i₂} ⋯ g_{i_j}`? (Johnson's column, problem [5]; Even and Goldreich 1981,
transformation from X3C.)

Permutations act on `{0, …, n - 1}`; a permutation is the list of its values `[π 0, …, π (n-1)]`,
required to be a rearrangement of `0, …, n - 1`. A sequence of generators is the list of their
indices `[i₁, …, i_j]`, and its product maps `x` to `g_{i₁} (g_{i₂} (⋯ (g_{i_j} x)))`; reading
the product in the other order replaces each sequence by its reverse, which does not change the
answer. The empty sequence (`j = 0`) is the identity. `P ∈ G` says that some sequence of the
generators, of any length, has product `P` (in a finite group, products of generators already
give every element of the generated group).

`K` is written in unary, as the list of `K` copies of `true`, so that a sequence of at most `K`
generators is a certificate of polynomial size (with `K` in binary, the shortest sequence for
`P` can be much longer than the input: for a single generator `g`, the shortest sequence for
`g^K` has `K` letters whenever `K` is less than the order of `g`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM LENGTH GENERATOR SEQUENCE is NP-complete.** Source: Johnson (1982), problem [5];
Even and Goldreich (1981). -/
public theorem_wanted minimumLengthGeneratorSequence_npComplete :
    minimumLengthGeneratorSequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumLengthGeneratorSequenceDec

end MetaMathlibExt.Complexity.NPComplete.MinimumLengthGeneratorSequence
