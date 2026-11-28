/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REVERSAL MEDIAN: definitions

Source:
A. Caprara, "The reversal median problem", INFORMS Journal on Computing 15 (2003), 93-113,
doi:10.1287/ijoc.15.1.93.15155;
the hardness for three genomes is recorded by M. Bader, "The transposition median problem is
NP-complete", Theoretical Computer Science 412 (2011), 1099-1110,
doi:10.1016/j.tcs.2010.12.009.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReversalMedian

/-- A signed permutation: the list of (gene, orientation) pairs, orientation `true` meaning `-`. -/
abbrev SignedPerm := List (ℕ × Bool)

/-- An instance: the number `n` of genes, the three genomes `π¹, π², π³`, and the bound `K`. -/
abbrev ReversalMedianInstance := ℕ × SignedPerm × SignedPerm × SignedPerm × ℕ

/-- `π` is a signed permutation of the genes `0, …, n - 1`: each gene occurs exactly once. -/
def IsSignedPerm (n : ℕ) (π : SignedPerm) : Prop :=
  (π.map Prod.fst).Perm (List.range n)

/-- The reversal `ρ(a, b)`: reverse the segment at positions `a, …, b` and flip the orientation of
each of its genes. -/
def reversal (π : SignedPerm) (a b : ℕ) : SignedPerm :=
  π.take a ++ ((π.drop a).take (b + 1 - a)).reverse.map (fun g => (g.1, !g.2)) ++ π.drop (b + 1)

/-- Apply a sequence of reversals, first to last. -/
def applyReversals (π : SignedPerm) (rs : List (ℕ × ℕ)) : SignedPerm :=
  rs.foldl (fun ρ r => reversal ρ r.1 r.2) π

/-- `rs` is a sequence of reversals of a genome with `n` genes: every reversal `(a, b)` has
`a ≤ b < n`. -/
def AreReversals (n : ℕ) (rs : List (ℕ × ℕ)) : Prop :=
  ∀ r ∈ rs, r.1 ≤ r.2 ∧ r.2 < n

/-- Well-formedness of an instance: the three genomes are signed permutations of the `n` genes. -/
def WellFormed (i : ReversalMedianInstance) : Prop :=
  IsSignedPerm i.1 i.2.1 ∧ IsSignedPerm i.1 i.2.2.1 ∧ IsSignedPerm i.1 i.2.2.2.1

/-- Some signed permutation `σ` of the `n` genes is transformed into `π¹`, `π²` and `π³` by three
sequences of reversals of total length at most `K`. -/
def ReversalMedianFeasible (i : ReversalMedianInstance) : Prop :=
  ∃ σ : SignedPerm, IsSignedPerm i.1 σ ∧
    ∃ r₁ r₂ r₃ : List (ℕ × ℕ), AreReversals i.1 r₁ ∧ AreReversals i.1 r₂ ∧
      AreReversals i.1 r₃ ∧ applyReversals σ r₁ = i.2.1 ∧ applyReversals σ r₂ = i.2.2.1 ∧
      applyReversals σ r₃ = i.2.2.2.1 ∧ r₁.length + r₂.length + r₃.length ≤ i.2.2.2.2

open Classical in
/-- REVERSAL MEDIAN as a decision problem over bitstrings. -/
noncomputable def reversalMedianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReversalMedianInstance) x with
  | some i => decide (WellFormed i ∧ ReversalMedianFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ReversalMedian
