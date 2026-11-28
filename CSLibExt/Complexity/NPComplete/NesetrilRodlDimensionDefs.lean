/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NESETRIL-RODL DIMENSION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT62] NESETRIL-RODL DIMENSION;
J. Nešetřil and A. Pultr, "A Dushnik-Miller type dimension of graphs and its complexity",
Fundamentals of Computation Theory (FCT 1977), Lecture Notes in Computer Science 56 (1977),
482-493, doi:10.1007/3-540-08442-8_119.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NesetrilRodlDimension

/-- An instance: the vertex count `n` in unary (a list of length `n`; vertices
`0, ..., n - 1`), the edge list, and the bound `K`. -/
abbrev NesetrilRodlDimensionInstance := List Bool × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`, `n` the length of the unary list. -/
def Graph (i : NesetrilRodlDimensionInstance) : SimpleGraph (Fin i.1.length) :=
  Cslib.Complexity.Karp.edgeGraph i.1.length i.2.1

/-- Well-formedness of an instance: `n` is written in unary as `[true, ..., true]`, the edge
list describes a simple graph on `0, ..., n - 1`, and `1 ≤ K ≤ |E|`. -/
def WellFormed (i : NesetrilRodlDimensionInstance) : Prop :=
  (∀ b ∈ i.1, b = true) ∧
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length ∧ e.1 ≠ e.2 ∧
      (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- Some one-to-one `f : V → (Fin K → Fin n)` has, for all `u, v`, `{u, v} ∈ E` iff `f(u)` and
`f(v)` disagree in every component. -/
def NesetrilRodlDimensionFeasible (i : NesetrilRodlDimensionInstance) : Prop :=
  ∃ f : Fin i.1.length → Fin i.2.2 → Fin i.1.length, Function.Injective f ∧
    ∀ u v, (Graph i).Adj u v ↔ ∀ k, f u k ≠ f v k

open Classical in
/-- NESETRIL-RODL DIMENSION as a decision problem over bitstrings. -/
noncomputable def nesetrilRodlDimensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NesetrilRodlDimensionInstance) x with
  | some i => decide (WellFormed i ∧ NesetrilRodlDimensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NesetrilRodlDimension
