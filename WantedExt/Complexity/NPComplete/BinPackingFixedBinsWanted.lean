/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIN PACKING with a fixed number `K ≥ 2` of bins is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR1] BIN PACKING, p. 226, comment:
"NP-complete and solvable in pseudo-polynomial time for each fixed K ≥ 2";
R. M. Karp, "Reducibility among combinatorial problems", in Complexity of Computer
Computations (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (PARTITION);
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 3(a).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BinPackingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinPackingFixedBins

/-!
# BIN PACKING with a fixed number `K ≥ 2` of bins is NP-complete

For a fixed constant `K ≥ 2`: INSTANCE: a finite set `U` of items, a size `s(u) ∈ ℤ⁺` for each
`u ∈ U`, and a positive integer bin capacity `B`. QUESTION: is there a partition of `U` into
disjoint sets `U₁, U₂, …, U_K` such that the sum of the sizes of the items in each `Uᵢ` is `B`
or less?

This is the restriction of BIN PACKING (`MetaMathlibExt.Complexity.NPComplete.BinPacking`) in
which `K` is no longer part of the instance. The instance is the list of item sizes and `B`,
and `withBins i K` appends the fixed `K` to obtain an instance of BIN PACKING, whose question
(`BinPacking.BinPackingFeasible`: a split of the item list into exactly `K` bins, empty bins
allowed, each of total size at most `B`) is asked. Item sizes and `B` are positive, as in Garey
and Johnson's instance. Binary encoding of all numbers (for fixed `K` the problem is
pseudo-polynomial, so it is NP-complete only in the ordinary sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the item sizes and the bin capacity `B`. -/
abbrev BinPackingFixedBinsInstance := List ℕ × ℕ

/-- The BIN PACKING instance with the fixed number `K` of bins appended. -/
def withBins (i : BinPackingFixedBinsInstance) (K : ℕ) : BinPacking.BinPackingInstance :=
  (i.1, i.2, K)

/-- Well-formedness of an instance: every item size is positive, and `B` is positive. -/
def WellFormed (i : BinPackingFixedBinsInstance) : Prop :=
  (∀ s ∈ i.1, 0 < s) ∧ 0 < i.2

open Classical in
/-- BIN PACKING with the number of bins fixed to `K`, as a decision problem over bitstrings. -/
noncomputable def binPackingFixedBinsDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := BinPackingFixedBinsInstance) x with
  | some i => decide (WellFormed i ∧ BinPacking.BinPackingFeasible (withBins i K))
  | none => false

/-- **BIN PACKING is NP-complete for every fixed number `K ≥ 2` of bins.** Source: Garey and
Johnson (1979), [SR1], comment; Karp (1972), PARTITION. -/
public theorem_wanted binPackingFixedBins_npComplete (K : ℕ) (hK : 2 ≤ K) :
    binPackingFixedBinsDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (binPackingFixedBinsDec K)

end MetaMathlibExt.Complexity.NPComplete.BinPackingFixedBins
