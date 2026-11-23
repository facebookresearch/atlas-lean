/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-LIVENESS OF FREE CHOICE PETRI NETS is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonLivenessOfFreeChoicePetriNets

/-!
# NON-LIVENESS OF FREE CHOICE PETRI NETS is NP-complete

INSTANCE: a Petri net `P = (n, M₀, T)`, where `n ∈ ℤ⁺`, `M₀` is an `n`-tuple of non-negative
integers (the initial marking), and `T` is a set of transitions `⟨a, b⟩` in which `a` and `b`
are `n`-tuples of `0`'s and `1`'s; firing `⟨a, b⟩` at a marking `M` requires `M - a ≥ 0` and
gives `M - a + b`. `P` is free choice: for each `⟨a, b⟩ ∈ T`, either `a` contains exactly one
`1`, or every other `⟨c, d⟩ ∈ T` has `c` equal to `0` in every position where `a` has a `1`.
QUESTION: is `P` not live, that is, is there a transition `t ∈ T` and a firing sequence `σ`
such that, for every sequence `τ` of transitions, the sequence `σ τ t` is not firable at `M₀`?

`σ` is a firing sequence, so it is itself firable at `M₀`. This is the standard notion of
liveness (Murata 1989, Section IV): a net is live if, no matter what marking has been reached
from `M₀`, every transition can still be fired by some further firing sequence. So `P` is not
live exactly when some reachable marking (the one `σ` leads to) allows no continuation that
fires `t`. Without that condition any non-firable `σ` would make the answer yes. Places are
`0, ..., n - 1`; a marking is a function `ℕ → ℕ`, and only places below `n` are ever changed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **NON-LIVENESS OF FREE CHOICE PETRI NETS is NP-complete.** Source: Garey and Johnson
(1979), [MS3]; Jones, Landweber, and Lien (1977). -/
public theorem_wanted nonLivenessOfFreeChoicePetriNets_npComplete :
    nonLivenessOfFreeChoicePetriNetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonLivenessOfFreeChoicePetriNetsDec

end MetaMathlibExt.Complexity.NPComplete.NonLivenessOfFreeChoicePetriNets
