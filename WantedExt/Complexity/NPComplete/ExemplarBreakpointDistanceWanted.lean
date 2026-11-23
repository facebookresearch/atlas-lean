/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXEMPLAR BREAKPOINT DISTANCE is NP-complete

Source:
D. Bryant, "The complexity of calculating exemplar distances", in D. Sankoff and J. H. Nadeau
(eds.), *Comparative Genomics*, Kluwer (2000), 207-211, doi:10.1007/978-94-011-4309-7_19,
Section 2 (definitions, after D. Sankoff, "Genome rearrangement with gene families",
Bioinformatics 15 (1999), 909-917, doi:10.1093/bioinformatics/15.11.909) and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExemplarBreakpointDistance

/-!
# EXEMPLAR BREAKPOINT DISTANCE is NP-complete

INSTANCE: two genomes `G` and `H`, strings of signed (`+` or `-`) symbols (genes) over an
alphabet `A`, in which every symbol of `A` occurs in both genomes, and a nonnegative integer
`K`. QUESTION: is the exemplar breakpoint distance between `G` and `H` at most `K`, i.e. are
there exemplar strings `g` of `G` and `h` of `H` whose breakpoint distance is at most `K`?

The definitions are Bryant's (Section 2, following Sankoff 1999). All occurrences of a symbol
`a` in both genomes form the gene family of `a`; Bryant assumes every family has a member in
each genome. An exemplar string is obtained from a genome by deleting all but one occurrence of
each gene family, so it keeps the relative order of the remaining genes. For exemplar strings
`g = g₁ ⋯ gₙ` and `h = h₁ ⋯ hₙ`, consecutive genes `a b` of `g` determine a breakpoint unless
`a` immediately precedes `b` in `h` or `-b` immediately precedes `-a` in `h`; additional
breakpoints are posited if `g₁ ≠ h₁` and if `gₙ ≠ hₙ` (signed genes compared). The breakpoint
distance is the number of breakpoints. (Bryant's worked example, exemplars `-b -a -c d` and
`c a b d` at breakpoint distance `2`, fixes the signed reading of the adjacency clause.)

Bryant proves that calculating the exemplar breakpoint distance is NP-hard (Theorem 1, even for
genomes in which every family has at most two members in each genome); the decision problem
is in NP because a pair of exemplar strings is a short certificate.

A gene is a pair `(a, s)` of a symbol `a : ℕ` and a sign `s : Bool` (`true` for `+`, `false`
for `-`); a genome is a list of genes. An exemplar string of `X` is a sublist (`List.Sublist`)
of `X` containing exactly one gene of every family of `X`. "`a` immediately precedes `b` in
`h`" means that `(a, b)` is one of the consecutive pairs `h.zip h.tail`. `K` uses the canonical
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the genomes `G` and `H`, lists of signed genes `(symbol, sign)` with `true`
for `+`, and the bound `K`. -/
abbrev ExemplarBreakpointDistanceInstance := List (ℕ × Bool) × List (ℕ × Bool) × ℕ

/-- The gene `-x`: the same symbol with the opposite sign. -/
def neg (x : ℕ × Bool) : ℕ × Bool := (x.1, !x.2)

/-- An exemplar string `x` of the genome `X`: a sublist of `X` that contains exactly one gene of
every gene family of `X`. -/
def IsExemplar (X x : List (ℕ × Bool)) : Prop :=
  x.Sublist X ∧ (x.map Prod.fst).Nodup ∧ ∀ a ∈ X.map Prod.fst, a ∈ x.map Prod.fst

/-- The pairs `(x_j, x_{j+1})` of consecutive genes of a string. -/
def adjacencies (x : List (ℕ × Bool)) : List ((ℕ × Bool) × (ℕ × Bool)) :=
  x.zip x.tail

/-- The breakpoint distance between exemplar strings `g` and `h`: the consecutive pairs `a b` of
`g` such that neither `a` precedes `b` nor `-b` precedes `-a` in `h`, plus one if `g₁ ≠ h₁` and
one if `gₙ ≠ hₙ`. -/
def breakpointDistance (g h : List (ℕ × Bool)) : ℕ :=
  ((adjacencies g).filter fun ab =>
      ab ∉ adjacencies h ∧ (neg ab.2, neg ab.1) ∉ adjacencies h).length +
    (if g.head? = h.head? then 0 else 1) + (if g.getLast? = h.getLast? then 0 else 1)

/-- Well-formedness of an instance: every symbol occurs in both genomes. -/
def WellFormed (i : ExemplarBreakpointDistanceInstance) : Prop :=
  (∀ a ∈ i.1.map Prod.fst, a ∈ i.2.1.map Prod.fst) ∧
    ∀ a ∈ i.2.1.map Prod.fst, a ∈ i.1.map Prod.fst

/-- Some exemplar strings `g` of `G` and `h` of `H` have breakpoint distance at most `K`. -/
def ExemplarBreakpointDistanceFeasible (i : ExemplarBreakpointDistanceInstance) : Prop :=
  ∃ g h : List (ℕ × Bool), IsExemplar i.1 g ∧ IsExemplar i.2.1 h ∧
    breakpointDistance g h ≤ i.2.2

open Classical in
/-- EXEMPLAR BREAKPOINT DISTANCE as a decision problem over bitstrings. -/
noncomputable def exemplarBreakpointDistanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExemplarBreakpointDistanceInstance) x with
  | some i => decide (WellFormed i ∧ ExemplarBreakpointDistanceFeasible i)
  | none => false

/-- **EXEMPLAR BREAKPOINT DISTANCE is NP-complete.** Source: Bryant (2000), Theorem 1. -/
public theorem_wanted exemplarBreakpointDistance_npComplete :
    exemplarBreakpointDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L exemplarBreakpointDistanceDec

end MetaMathlibExt.Complexity.NPComplete.ExemplarBreakpointDistance
