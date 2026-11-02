/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIN PACKING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BIN PACKING; D. S.
Johnson, "Fast algorithms for bin packing" (1974).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinPacking

/-!
# BIN PACKING is NP-complete

A list of item sizes, a bin capacity, and a number `K` of bins. The question is whether all
items fit into at most `K` bins of the given capacity, witnessed by a partition of the items
into exactly `K` bins (empty bins allowed).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Bin packing instances.** An instance of BIN PACKING is a triple $(s, B, K)$ of a finite
list $s$ of natural numbers (the item sizes), a natural number $B$ (the bin capacity) and a
natural number $K$ (the number of bins). -/
abbrev BinPackingInstance := List ℕ × ℕ × ℕ

/-- **Feasible bin packing instances.** An instance $(s, B, K)$ of BIN PACKING is feasible when
there is a list of exactly $K$ bins, each a finite list of natural numbers with sum at most $B$,
such that the concatenation of the bins is a permutation of $s$.

Since bins may be empty, this says that the items fit into at most $K$ bins of capacity $B$. -/
def BinPackingFeasible
    (i : BinPackingInstance) : Prop :=
  ∃ bins : List (List ℕ), bins.length = i.2.2 ∧ bins.flatten.Perm i.1 ∧
    ∀ bin ∈ bins, bin.sum ≤ i.2.1

open Classical in
/-- **The bin packing decision problem.** BIN PACKING is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of bin packing
instances, to a feasible instance; it rejects every bitstring that fails to decode. -/
noncomputable def binPackingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BinPackingInstance) x with
  | some i => decide (BinPackingFeasible i)
  | none => false

/-- **BIN PACKING is NP-complete.** The bin packing decision problem belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), BIN PACKING; D. S. Johnson, "Fast algorithms for bin packing"
(1974). -/
public theorem_wanted binPacking_npComplete :
    binPackingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L binPackingDec

end MetaMathlibExt.Complexity.NPComplete.BinPacking
