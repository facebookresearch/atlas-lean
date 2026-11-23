/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM QUADRATIC-COST FLOW is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND32] MINIMUM EDGE-COST FLOW (p. 214),
comment "However, becomes NP-complete once more if (4) is replaced by
∑_{a ∈ A} (p₁(a) f(a)² + p₂(a) f(a)) ≤ B" (credited there to P. P. Herrmann, 1973).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumQuadraticCostFlow

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted (IsFeasibleFlow)

/-!
# MINIMUM QUADRATIC-COST FLOW is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, a capacity
`c(a) ∈ ℤ⁺` and integer coefficients `p₁(a), p₂(a)` for each `a ∈ A`, a requirement `R ∈ ℤ⁺`, and a
bound `B ∈ ℤ⁺`.
QUESTION: is there a flow function `f : A → ℤ₀⁺` such that (1) `f(a) ≤ c(a)` for all `a ∈ A`,
(2) flow is conserved at each `v ∈ V - {s, t}`, (3) the net flow into `t` is at least `R`, and
(4') `∑_{a ∈ A} (p₁(a) f(a)² + p₂(a) f(a)) ≤ B`?

This is MINIMUM EDGE-COST FLOW ([ND32], `MinimumEdgeCostFlowWanted`) with condition (4), a bound
on the total price of the arcs carrying flow, replaced by the quadratic cost bound (4'), as in
Garey and Johnson's comment. With a linear cost `∑ p(a) f(a)` the problem is solvable in
polynomial time; the quadratic cost makes it NP-complete again. Garey and Johnson do not restrict
the signs of `p₁, p₂`, and the coefficients are arbitrary integers here: with `p₁ ≥ 0` the cost is
separable convex, and integral convex-cost flow is solvable in polynomial time, so the hardness
lies in the concave terms. (For instance, on an arc of capacity `2` the cost `-p f² + 3 p f` is
`0` at `f = 0` and `2p` at `f = 1, 2`, twice the fixed charge `p` of MINIMUM EDGE-COST FLOW, which
[ND32] records as NP-complete for capacities `2` and prices `p ∈ {0, 1}`.) Integers are encoded as
pairs `(positive part, negative part)` (`intOf`), as in `ZeroOneILPWanted`.

Vertices are `0, ..., n - 1`, and arcs are listed as `(tail, head, capacity, p₁, p₂)`. A flow is
a function `f : Fin n → Fin n → ℕ`; conditions (1) and (2) are MathlibExt's `IsFeasibleFlow` for
the capacity `(arcData i u v).1` (`0` off the arcs, so `f` vanishes there), as in
`DirectedTwoCommodityIntegralFlowWanted`. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), the arcs
`(tail, head, capacity, p₁, p₂)` with `p₁, p₂` encoded integers, `s`, `t`, the requirement `R`,
and the bound `B`. -/
abbrev MinimumQuadraticCostFlowInstance :=
  ℕ × List (ℕ × ℕ × ℕ × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ × ℕ × ℕ × ℕ

/-- The integer encoded by a pair `(positive part, negative part)`. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- The arcs `(u, v)` of the arc records. -/
def arcs (i : MinimumQuadraticCostFlowInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun a => (a.1, a.2.1)

/-- The data `(c, p₁, p₂)` of the arc from `u` to `v` (`p₁, p₂` encoded), and all zeros when
there is no such arc. -/
def arcData (i : MinimumQuadraticCostFlowInstance) (u v : ℕ) : ℕ × (ℕ × ℕ) × (ℕ × ℕ) :=
  ((i.2.1.find? fun a => a.1 = u ∧ a.2.1 = v).map fun a => a.2.2).getD (0, (0, 0), (0, 0))

/-- Well-formedness of an instance: the arc records describe a directed graph on
`0, ..., n - 1` (endpoints in range, no self-loops, no repeated arcs), every capacity is positive,
`s` and `t` are distinct vertices, and `R` and `B` are positive. -/
def WellFormed (i : MinimumQuadraticCostFlowInstance) : Prop :=
  ((arcs i).Nodup ∧ ∀ a ∈ arcs i, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    (∀ a ∈ i.2.1, 0 < a.2.2.1) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧ 0 < i.2.2.2.2.1 ∧ 0 < i.2.2.2.2.2

/-- An integral flow within the capacities, conserved at every vertex other than `s` and `t`,
with net flow into `t` at least `R`, whose quadratic cost `∑ (p₁ f² + p₂ f)` is at most `B`. -/
def MinimumQuadraticCostFlowFeasible (i : MinimumQuadraticCostFlowInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1), ∃ f : Fin i.1 → Fin i.1 → ℕ,
    IsFeasibleFlow (fun u v : Fin i.1 => ((arcData i u v).1 : ℝ)) ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩
        (fun u v => (f u v : ℝ)) ∧
      (i.2.2.2.2.1 : ℝ) ≤ (∑ u, (f u ⟨i.2.2.2.1, ht⟩ : ℝ)) - ∑ w, (f ⟨i.2.2.2.1, ht⟩ w : ℝ) ∧
      (∑ u : Fin i.1, ∑ v : Fin i.1,
        (intOf (arcData i u v).2.1 * (f u v : ℤ) ^ 2 + intOf (arcData i u v).2.2 * f u v)) ≤
        (i.2.2.2.2.2 : ℤ)

open Classical in
/-- MINIMUM QUADRATIC-COST FLOW as a decision problem over bitstrings. -/
noncomputable def minimumQuadraticCostFlowDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumQuadraticCostFlowInstance) x with
  | some i => decide (WellFormed i ∧ MinimumQuadraticCostFlowFeasible i)
  | none => false

/-- **MINIMUM QUADRATIC-COST FLOW is NP-complete.** Source: Garey and Johnson (1979), [ND32],
comment (Herrmann, 1973). -/
public theorem_wanted minimumQuadraticCostFlow_npComplete :
    minimumQuadraticCostFlowDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumQuadraticCostFlowDec

end MetaMathlibExt.Complexity.NPComplete.MinimumQuadraticCostFlow
