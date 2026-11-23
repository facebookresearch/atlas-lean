/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH HOMOLOGOUS ARCS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND35] INTEGRAL FLOW WITH
HOMOLOGOUS ARCS;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021 (Problem N(iii), Theorem 2.2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowHomologousArcs

/-!
# INTEGRAL FLOW WITH HOMOLOGOUS ARCS is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, a capacity
`c(a) ∈ ℤ⁺` for each `a ∈ A`, a requirement `R ∈ ℤ⁺`, and a set `H ⊆ A × A` of "homologous"
pairs of arcs. QUESTION: is there a flow function `f : A → ℤ₀⁺` such that (1) `f(a) ≤ c(a)` for
all `a ∈ A`, (2) for each `v ∈ V - {s, t}`, flow is conserved at `v`, (3) for all pairs
`⟨a, a'⟩ ∈ H`, `f(a) = f(a')`, and (4) the net flow into `t` is at least `R`?

The vertices are `0, ..., n - 1`. Each arc is a record `(u, v, c)`: the arc from `u` to `v` with
capacity `c`; there are no self-loops and no repeated arcs. A homologous pair is a pair
`((u, v), (u', v'))` of arcs, each given by its endpoints. A flow is a function
`f : Fin n → Fin n → ℕ` (integral and nonnegative) on ordered pairs. Conditions (1) and (2) are
`IsFeasibleFlow` from `MathlibExt.Combinatorics.Graph.MaxFlowMinCut` for the arc capacities
`capacity` (`c(a)` on an arc `a`, `0` on every other ordered pair), so the flow also vanishes
off the arcs, i.e. it is a function on `A`. Conditions (3) and (4) are stated directly. As in
the source, `s` and `t` need not be distinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), arc records `(u, v, c)` (arc from
`u` to `v` with capacity `c`), `s`, `t`, the requirement `R`, and the homologous pairs
`((u, v), (u', v'))`. -/
abbrev IntegralFlowHomologousArcsInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ × List ((ℕ × ℕ) × (ℕ × ℕ))

/-- The arcs `(u, v)` of the arc records. -/
def arcs (i : IntegralFlowHomologousArcsInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun a => (a.1, a.2.1)

/-- The capacity `c(u, v)` of the arc from `u` to `v`, and `0` when there is no such arc. -/
def capacity (i : IntegralFlowHomologousArcsInstance) (u v : ℕ) : ℕ :=
  ((i.2.1.find? fun a => a.1 = u ∧ a.2.1 = v).map fun a => a.2.2).getD 0

/-- Well-formedness of an instance: the arc records describe a directed graph on
`0, ..., n - 1` (endpoints in range, no self-loops, no repeated arcs), every capacity is
positive, `s` and `t` are vertices, the requirement `R` is positive, and both arcs of every
homologous pair are arcs of the graph (`H ⊆ A × A`). -/
def WellFormed (i : IntegralFlowHomologousArcsInstance) : Prop :=
  ((arcs i).Nodup ∧ ∀ a ∈ arcs i, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    (∀ a ∈ i.2.1, 0 < a.2.2) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2.1 ∧
    ∀ h ∈ i.2.2.2.2.2, h.1 ∈ arcs i ∧ h.2 ∈ arcs i

/-- There is an integral flow `f` that is feasible for the arc capacities (it vanishes off the
arcs, is at most the capacity on each arc, and is conserved at every vertex other than `s` and
`t`), takes equal values on the two arcs of every homologous pair, and has net flow into `t`
at least `R`. -/
def IntegralFlowHomologousArcsFeasible (i : IntegralFlowHomologousArcsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1) (f : Fin i.1 → Fin i.1 → ℕ),
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity i u v : ℝ)) ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩
        (fun u v => (f u v : ℝ)) ∧
      (∀ h ∈ i.2.2.2.2.2, ∀ u v u' v' : Fin i.1,
        ((u : ℕ), (v : ℕ)) = h.1 → ((u' : ℕ), (v' : ℕ)) = h.2 → f u v = f u' v') ∧
      (i.2.2.2.2.1 : ℝ) ≤ (∑ u, (f u ⟨i.2.2.2.1, ht⟩ : ℝ)) - ∑ w, (f ⟨i.2.2.2.1, ht⟩ w : ℝ)

open Classical in
/-- INTEGRAL FLOW WITH HOMOLOGOUS ARCS as a decision problem over bitstrings. -/
noncomputable def integralFlowHomologousArcsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegralFlowHomologousArcsInstance) x with
  | some i => decide (WellFormed i ∧ IntegralFlowHomologousArcsFeasible i)
  | none => false

/-- **INTEGRAL FLOW WITH HOMOLOGOUS ARCS is NP-complete.** Source: Garey and Johnson (1979),
[ND35]; Sahni (1974). -/
public theorem_wanted integralFlowHomologousArcs_npComplete :
    integralFlowHomologousArcsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integralFlowHomologousArcsDec

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowHomologousArcs
