/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Multiset.Basic

/-!
# SYNTENIC DISTANCE: definitions

INSTANCE: two genomes `G₁` and `G₂` over the same set of genes, and an integer `K`.
QUESTION: is the syntenic distance from `G₁` to `G₂` at most `K`, that is, can `G₁` be
transformed into `G₂` by at most `K` moves?

Following DasGupta, Jiang, Kannan, Li and Sweedyk (1998), Section 2 (after Ferretti, Nadeau and
Sankoff): a genome is a collection of subsets (synteny sets, or chromosomes) of a set of genes,
and the order of genes is ignored. Definition 2.1: let `S₁, S₂, T₁, T₂` be sets, at most one
of them empty, with `T₁ ∪ T₂ = S₁ ∪ S₂`; if all four are nonempty, replacing `S₁, S₂` by
`T₁, T₂` is a translocation; if `S₂` is empty, replacing `S₁` by `T₁, T₂` is a fission; if
`T₂` is empty, replacing `S₁, S₂` by `T₁` is a fusion. The syntenic distance `D(G₁, G₂)` is
the least number of moves transforming `G₁` into `G₂`; Theorem 3.1 proves that computing it is
NP-hard. Membership in NP: moves preserve the union of the chromosomes; when the unions agree
and both genomes are nonempty, fusing all chromosomes of `G₁` into one and splitting it into
those of `G₂` takes `|G₁| + |G₂| - 2` moves, so a shortest move sequence is a certificate of
polynomial size.

A genome is a nonempty multiset of nonempty finite sets of genes (`Multiset (Finset ℕ)`), so its
chromosomes are unordered and two equal chromosomes count twice (the source's compact
representation allows equal sets). The instance lists each chromosome as a list of genes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
B. DasGupta, T. Jiang, S. Kannan, M. Li and E. Sweedyk, "On the complexity and approximation
of syntenic distance", Discrete Applied Mathematics 88 (1998), 59-82,
doi:10.1016/S0166-218X(98)00066-3; Definition 2.1 and Theorem 3.1 are numbered as in the
conference version (RECOMB 1997).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SyntenicDistance

/-- An instance: the genomes `G₁` and `G₂` as lists of chromosomes (each a list of genes), and
the bound `K`. -/
abbrev SyntenicDistanceInstance := List (List ℕ) × List (List ℕ) × ℕ

/-- The genome denoted by a list of chromosomes. -/
def genome (G : List (List ℕ)) : Multiset (Finset ℕ) := (G.map List.toFinset : Multiset _)

/-- One move of Definition 2.1 (DasGupta et al. 1998) on genomes. -/
inductive Move : Multiset (Finset ℕ) → Multiset (Finset ℕ) → Prop
  /-- Translocation: `S₁, S₂` become `T₁, T₂`, all four nonempty, `T₁ ∪ T₂ = S₁ ∪ S₂`. -/
  | translocation (R : Multiset (Finset ℕ)) (S₁ S₂ T₁ T₂ : Finset ℕ) :
      S₁.Nonempty → S₂.Nonempty → T₁.Nonempty → T₂.Nonempty → T₁ ∪ T₂ = S₁ ∪ S₂ →
      Move (S₁ ::ₘ S₂ ::ₘ R) (T₁ ::ₘ T₂ ::ₘ R)
  /-- Fission: `S₁` becomes `T₁, T₂`, all three nonempty, `T₁ ∪ T₂ = S₁`. -/
  | fission (R : Multiset (Finset ℕ)) (S₁ T₁ T₂ : Finset ℕ) :
      S₁.Nonempty → T₁.Nonempty → T₂.Nonempty → T₁ ∪ T₂ = S₁ →
      Move (S₁ ::ₘ R) (T₁ ::ₘ T₂ ::ₘ R)
  /-- Fusion: `S₁, S₂` become `T₁ = S₁ ∪ S₂`, with `S₁, S₂` nonempty. -/
  | fusion (R : Multiset (Finset ℕ)) (S₁ S₂ T₁ : Finset ℕ) :
      S₁.Nonempty → S₂.Nonempty → T₁ = S₁ ∪ S₂ →
      Move (S₁ ::ₘ S₂ ::ₘ R) (T₁ ::ₘ R)

/-- Well-formedness of an instance: both genomes have at least one chromosome, every chromosome
is a nonempty list of distinct genes, and the two genomes are over the same set of genes. -/
def WellFormed (i : SyntenicDistanceInstance) : Prop :=
  i.1 ≠ [] ∧ i.2.1 ≠ [] ∧ (∀ c ∈ i.1 ++ i.2.1, c ≠ [] ∧ c.Nodup) ∧
    i.1.flatten.toFinset = i.2.1.flatten.toFinset

/-- The syntenic distance from `G₁` to `G₂` is at most `K`: a sequence of `m ≤ K` moves leads
from `G₁` to `G₂`. -/
def SyntenicDistanceFeasible (i : SyntenicDistanceInstance) : Prop :=
  ∃ m ≤ i.2.2, ∃ g : ℕ → Multiset (Finset ℕ),
    g 0 = genome i.1 ∧ g m = genome i.2.1 ∧ ∀ j < m, Move (g j) (g (j + 1))

open Classical in
/-- SYNTENIC DISTANCE as a decision problem over bitstrings. -/
noncomputable def syntenicDistanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := SyntenicDistanceInstance) x with
  | some i => decide (WellFormed i ∧ SyntenicDistanceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SyntenicDistance
