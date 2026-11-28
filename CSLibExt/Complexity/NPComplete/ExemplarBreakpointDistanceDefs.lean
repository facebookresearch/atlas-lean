/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXEMPLAR BREAKPOINT DISTANCE: definitions

Source:
D. Bryant, "The complexity of calculating exemplar distances", in D. Sankoff and J. H. Nadeau
(eds.), *Comparative Genomics*, Kluwer (2000), 207-211, doi:10.1007/978-94-011-4309-7_19,
Section 2 (definitions, after D. Sankoff, "Genome rearrangement with gene families",
Bioinformatics 15 (1999), 909-917, doi:10.1093/bioinformatics/15.11.909) and Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExemplarBreakpointDistance

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

end MetaMathlibExt.Complexity.NPComplete.ExemplarBreakpointDistance
