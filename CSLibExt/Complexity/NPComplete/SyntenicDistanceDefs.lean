/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SYNTENIC DISTANCE: definitions

Source:
B. DasGupta, T. Jiang, S. Kannan, M. Li and E. Sweedyk, "On the complexity and approximation
of syntenic distance", Discrete Applied Mathematics 88 (1998), 59-82,
doi:10.1016/S0166-218X(98)00066-3; Definition 2.1 and Theorem 3.1 are numbered as in the
conference version (RECOMB 1997).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Multiset.Basic

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
