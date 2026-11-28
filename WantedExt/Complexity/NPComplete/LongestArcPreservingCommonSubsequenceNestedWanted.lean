/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST ARC-PRESERVING COMMON SUBSEQUENCE (nested, nested) is NP-complete

Source:
G.-H. Lin, Z.-Z. Chen, T. Jiang and J. Wen, "The longest common subsequence problem for
sequences with nested arc annotations", Journal of Computer and System Sciences 65 (2002),
465-480, doi:10.1016/S0022-0000(02)00004-1;
problem definitions as in V. Yu. Popov, "Arc-preserving subsequences of arc-annotated
sequences", Acta Universitatis Sapientiae, Informatica 3 (2011), 35-47, arXiv:1104.4433.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNestedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNested

/-!
# LONGEST ARC-PRESERVING COMMON SUBSEQUENCE (nested, nested) is NP-complete

An arc-annotated sequence is a pair `(S, P)` of a sequence `S` over an alphabet and a set `P`
of pairs `(i₁, i₂)` of positions of `S` with `i₁ < i₂` (arcs). A common subsequence `T` of
`S₁` and `S₂` induces a bijective, order-preserving mapping from a set of positions of `S₁`
onto a set of positions of `S₂` with equal letters at matched positions; `T` is
arc-preserving if for any `(i₁, j₁)` and `(i₂, j₂)` in the mapping,
`(i₁, i₂) ∈ P₁ ⇔ (j₁, j₂) ∈ P₂`. An arc set is nested if

1. no two arcs share an endpoint: for all `(i₁, i₂), (i₃, i₄) ∈ P`, `i₁ ≠ i₄`, `i₂ ≠ i₃`, and
   `i₁ = i₃ ⇔ i₂ = i₄`;
2. no two arcs cross: for all `(i₁, i₂), (i₃, i₄) ∈ P`, `i₁ ∈ [i₃, i₄] ⇔ i₂ ∈ [i₃, i₄]`.

LAPCS(NESTED, NESTED): given two arc-annotated sequences `(S₁, P₁)` and `(S₂, P₂)` with nested
arc sets and a positive integer `k`, is there a common subsequence `T` of `S₁` and `S₂` that
is arc-preserving with `|T| ≥ k`? Lin, Chen, Jiang and Wen (2002) proved it NP-hard; it is
in NP.

Letters are natural numbers and positions are `0`-based (the sources number them from `1`).
A common subsequence of length `ℓ` is given by its two position mappings
`f : Fin ℓ ↪o Fin |S₁|` and `g : Fin ℓ ↪o Fin |S₂|`, order embeddings with
`S₁[f t] = S₂[g t]`; this is Mathlib's characterization of `List.Sublist`
(`List.sublist_iff_exists_fin_orderEmbedding_get_eq`) applied to both sequences, with the
matched positions kept because arc preservation is a condition on them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST ARC-PRESERVING COMMON SUBSEQUENCE (nested, nested) is NP-complete.** Source:
Lin, Chen, Jiang and Wen (2002). -/
public theorem_wanted longestArcPreservingCommonSubsequenceNested_npComplete :
    longestArcPreservingCommonSubsequenceNestedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestArcPreservingCommonSubsequenceNestedDec

end MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNested
