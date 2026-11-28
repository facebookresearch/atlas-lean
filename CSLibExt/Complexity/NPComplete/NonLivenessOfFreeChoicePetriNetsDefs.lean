/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-LIVENESS OF FREE CHOICE PETRI NETS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS3] NON-LIVENESS OF FREE
CHOICE PETRI NETS;
N. D. Jones, L. H. Landweber, and Y. E. Lien, "Complexity of some problems in Petri
nets", Theoretical Computer Science 4 (1977), 277-299,
doi:10.1016/0304-3975(77)90014-7;
liveness as in T. Murata, "Petri nets: properties, analysis and applications",
Proceedings of the IEEE 77 (1989), 541-580, doi:10.1109/5.24143.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonLivenessOfFreeChoicePetriNets

/-- A transition `⟨a, b⟩`: the places it takes a token from and puts a token on. -/
abbrev Transition := List Bool × List Bool

/-- An instance: the number of places `n`, the initial marking `M₀`, and the transitions
`T`. -/
abbrev NonLivenessOfFreeChoicePetriNetsInstance := ℕ × List ℕ × List Transition

/-- Well-formedness of an instance: `0 < n`, `M₀` and every `a`, `b` have length `n`, `T` lists
distinct transitions, and `P` is free choice. -/
def WellFormed (i : NonLivenessOfFreeChoicePetriNetsInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 ∧ i.2.2.Nodup ∧
    (∀ t ∈ i.2.2, t.1.length = i.1 ∧ t.2.length = i.1) ∧
    ∀ t ∈ i.2.2, t.1.count true = 1 ∨
      ∀ t' ∈ i.2.2, t' ≠ t → ∀ j < i.1, t.1.getD j false = true → t'.1.getD j false = false

/-- Transition `t` may fire at marking `M`: `M - a ≥ 0`. -/
def Enabled (M : ℕ → ℕ) (t : Transition) : Prop :=
  ∀ j, t.1.getD j false = true → 1 ≤ M j

/-- The marking `M - a + b` after firing `t = ⟨a, b⟩` at `M`. -/
def fire (M : ℕ → ℕ) (t : Transition) : ℕ → ℕ := fun j =>
  M j - (if t.1.getD j false then 1 else 0) + (if t.2.getD j false then 1 else 0)

/-- The transitions of the sequence fire one after another starting from marking `M`. -/
def Firable : (ℕ → ℕ) → List Transition → Prop
  | _, [] => True
  | M, t :: σ => Enabled M t ∧ Firable (fire M t) σ

/-- `P` is not live: some `t ∈ T` and some firing sequence `σ` of transitions of `T` such that
no sequence `τ` of transitions of `T` makes `σ τ t` firable at `M₀`. -/
def NonLivenessOfFreeChoicePetriNetsFeasible
    (i : NonLivenessOfFreeChoicePetriNetsInstance) : Prop :=
  ∃ t ∈ i.2.2, ∃ σ : List Transition, (∀ x ∈ σ, x ∈ i.2.2) ∧
    Firable (fun j => i.2.1.getD j 0) σ ∧
    ∀ τ : List Transition, (∀ x ∈ τ, x ∈ i.2.2) →
      ¬ Firable (fun j => i.2.1.getD j 0) (σ ++ τ ++ [t])

open Classical in
/-- NON-LIVENESS OF FREE CHOICE PETRI NETS as a decision problem over bitstrings. -/
noncomputable def nonLivenessOfFreeChoicePetriNetsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonLivenessOfFreeChoicePetriNetsInstance) x with
  | some i => decide (WellFormed i ∧ NonLivenessOfFreeChoicePetriNetsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NonLivenessOfFreeChoicePetriNets
