/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED FINITE STATE AUTOMATON for nearly complete samples is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 267, comment to problem [AL8]
MINIMUM INFERRED FINITE STATE AUTOMATON ("for any fixed ε > 0, the problem remains
NP-complete if restricted to instances for which (S ∪ T) ⊆ Σ^(n) and
|Σ^(n) - (S ∪ T)| ≤ |Σ^(n)|^ε", credited there to Angluin, 1977);
D. Angluin, "On the complexity of minimum inference of regular sets", Information
and Control 39 (1978), 337-350, doi:10.1016/S0019-9958(78)90683-6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonNearlyComplete

open MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomaton

/-!
# MINIMUM INFERRED FINITE STATE AUTOMATON for nearly complete samples is NP-complete

Fix `ε > 0`. INSTANCE: a finite alphabet `Σ`, two finite subsets `S, T ⊆ Σ*`, and a positive
integer `K`, restricted to instances for which `(S ∪ T) ⊆ Σ^(n)` and
`|Σ^(n) - (S ∪ T)| ≤ |Σ^(n)|^ε` for some `n`, where `Σ^(n)` is the set of all strings of length
`n` or less over `Σ`. QUESTION: is there a `K`-state deterministic finite automaton `A` that
recognizes a language `L ⊆ Σ*` such that `S ⊆ L` and `T ⊆ Σ* - L`?

The instance, its well-formedness and the question are those of
`MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomaton` ([AL8]); this module
adds the restriction. `|Σ^(n)| = ∑_{k ≤ n} m^k` for `Σ = Fin m`. Since `S ∪ T ⊆ Σ^(n)`,
`|Σ^(n) - (S ∪ T)| = |Σ^(n)| - |S ∪ T|`, where `|S ∪ T|` counts distinct strings.

The exponent is a fixed rational `ε = p / q` with `p, q > 0`, and the bound
`|Σ^(n) - (S ∪ T)| ≤ |Σ^(n)|^(p/q)` is written `|Σ^(n) - (S ∪ T)|^q ≤ |Σ^(n)|^p`. The statement
is a family: one decision problem for each such `ε`. (For an irrational `ε` the restriction is
not decidable unless `ε` is computable; every real `ε > 0` exceeds some rational `p / q > 0`,
whose instances are among those allowed for `ε`.)

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `|Σ^(n)|` for an alphabet of `m` letters: the number of strings of length at most `n`. -/
def stringsUpTo (m n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), m ^ k

/-- The sample is nearly complete for `ε = p / q`: for some `n`, every string of `S` and `T`
has length at most `n`, and `|Σ^(n) - (S ∪ T)|^q ≤ |Σ^(n)|^p`. -/
def NearlyComplete (p q : ℕ) (i : MinimumInferredFiniteStateAutomatonInstance) : Prop :=
  ∃ n, (∀ w ∈ i.2.1 ++ i.2.2.1, w.length ≤ n) ∧
    (stringsUpTo i.1 n - (i.2.1 ++ i.2.2.1).toFinset.card) ^ q ≤ stringsUpTo i.1 n ^ p

/-- Well-formedness of an instance: it is a well-formed MINIMUM INFERRED FINITE STATE
AUTOMATON instance (letters below `m`, `K` positive), and the sample is nearly complete for
`ε = p / q`. -/
def WellFormed (p q : ℕ) (i : MinimumInferredFiniteStateAutomatonInstance) : Prop :=
  MinimumInferredFiniteStateAutomaton.WellFormed i ∧ NearlyComplete p q i

open Classical in
/-- MINIMUM INFERRED FINITE STATE AUTOMATON restricted to nearly complete samples for
`ε = p / q`, as a decision problem over bitstrings. -/
noncomputable def minimumInferredFiniteStateAutomatonNearlyCompleteDec (p q : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumInferredFiniteStateAutomatonInstance) x with
  | some i => decide (WellFormed p q i ∧ MinimumInferredFiniteStateAutomatonFeasible i)
  | none => false

/-- **MINIMUM INFERRED FINITE STATE AUTOMATON for nearly complete samples is NP-complete**, for
every fixed rational `ε = p / q > 0`. Source: Garey and Johnson (1979), [AL8] comment;
Angluin (1978). -/
public theorem_wanted minimumInferredFiniteStateAutomatonNearlyComplete_npComplete
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    minimumInferredFiniteStateAutomatonNearlyCompleteDec p q ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            (minimumInferredFiniteStateAutomatonNearlyCompleteDec p q)

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonNearlyComplete
