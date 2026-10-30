/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Max flow is in P (Edmonds-Karp)

Source:
J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow
problems", Journal of the ACM 19 (1972), 248-264; L. R. Ford Jr. and D. R. Fulkerson, Flows in
Networks, Princeton University Press, 1962.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MaxFlowInP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Max flow is in P (Edmonds-Karp)

The max-flow decision problem is in `P`, by augmenting-path algorithms (Edmonds-Karp). The
instance is a vertex count, a list of edges `(u, v, capacity)`, source `s`, sink `t`, and a
target `K`; the question is whether some feasible flow (capacities respected, conservation at
every vertex except `s, t`) has net outflow from `s` at least `K`. Well-formedness requires
every edge's endpoints below `n` and distinct, `s` and `t` below `n`, and `s ≠ t`.
-/

open Classical in
/-- Max-flow decision problem over bitstrings. -/
noncomputable def maxFlowDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ) x with
  | some i => decide (
      (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1) ∧
      i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧
      ∃ flow : List ℕ, flow.length = i.2.1.length ∧
        (∀ j < i.2.1.length, flow.getD j 0 ≤ (i.2.1.getD j (0, 0, 0)).2.2) ∧
        (∀ v < i.1, v ≠ i.2.2.1 → v ≠ i.2.2.2.1 →
          (Finset.range i.2.1.length).sum (fun j =>
            if (i.2.1.getD j (0, 0, 0)).2.1 = v then flow.getD j 0 else 0) =
          (Finset.range i.2.1.length).sum (fun j =>
            if (i.2.1.getD j (0, 0, 0)).1 = v then flow.getD j 0 else 0)) ∧
        (Finset.range i.2.1.length).sum (fun j =>
          if (i.2.1.getD j (0, 0, 0)).1 = i.2.2.1 then flow.getD j 0 else 0) -
        (Finset.range i.2.1.length).sum (fun j =>
          if (i.2.1.getD j (0, 0, 0)).2.1 = i.2.2.1 then flow.getD j 0 else 0) ≥
            i.2.2.2.2)
  | none => false

/-- **Max flow is in P (Edmonds-Karp).** Source: J. Edmonds and R. M. Karp, "Theoretical
improvements in algorithmic efficiency for network flow problems", Journal of the ACM 19
(1972), 248-264; L. R. Ford Jr. and D. R. Fulkerson, Flows in Networks, Princeton
University Press, 1962. -/
public theorem_wanted max_flow_in_p :
    maxFlowDec ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.MaxFlowInP
