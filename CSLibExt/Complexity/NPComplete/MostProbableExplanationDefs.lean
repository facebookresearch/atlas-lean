/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MOST PROBABLE EXPLANATION in Bayesian networks: definitions

Source:
S. E. Shimony, "Finding MAPs for belief networks is NP-hard", Artificial Intelligence 68
(1994), 399-410, doi:10.1016/0004-3702(94)90072-8;
J. D. Park and A. Darwiche, "Complexity results and approximation strategies for MAP
explanations", Journal of Artificial Intelligence Research 21 (2004), 101-133,
doi:10.1613/jair.1236, arXiv:1107.0024 (§2.2: the decision problem D-MPE, and "D-MPE is
NP-complete (Shimony, 1994)").
-/
module

public import CSLibExt.MachineLearning.GraphicalModels.BayesianNetwork
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MostProbableExplanation

open Cslib.MachineLearning.GraphicalModels

/-- A node: its parent list and its conditional probability table, as rows `(u, θ)` (see the
module docstring). -/
abbrev Node := List ℕ × List (List ℕ × List (ℕ × ℕ))

/-- An instance: the domain size `d`, the nodes in topological order, the evidence, and the
threshold `((p⁺, p⁻), q)`. -/
abbrev MostProbableExplanationInstance :=
  ℕ × List Node × List (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)

/-- `θ` is a probability distribution on `{0, …, d - 1}` given by `d` fractions in `[0, 1]`
with positive denominators that sum to `1`. -/
def IsDistribution (d : ℕ) (θ : List (ℕ × ℕ)) : Prop :=
  θ.length = d ∧ (∀ q ∈ θ, 0 < q.2 ∧ q.1 ≤ q.2) ∧ (θ.map fun q => (q.1 : ℚ) / q.2).sum = 1

/-- Node `k` of a network over the domain `{0, …, d - 1}`: its parents are distinct nodes
`j < k`, and its table has exactly one row for each instantiation of the parents (rows with
distinct parent values, each of the right length and with values below `d`, and `d ^ |U|` of
them), each row giving a distribution on `{0, …, d - 1}`. -/
def IsNode (d k : ℕ) (v : Node) : Prop :=
  v.1.Nodup ∧ (∀ j ∈ v.1, j < k) ∧ (v.2.map Prod.fst).Nodup ∧ v.2.length = d ^ v.1.length ∧
    ∀ row ∈ v.2, row.1.length = v.1.length ∧ (∀ a ∈ row.1, a < d) ∧ IsDistribution d row.2

/-- Well-formedness of an instance: the domain is nonempty, every node is well formed, the
evidence assigns values below `d` to distinct variables of the network, and `q > 0`. -/
def WellFormed (i : MostProbableExplanationInstance) : Prop :=
  0 < i.1 ∧ (∀ k (hk : k < i.2.1.length), IsNode i.1 k i.2.1[k]) ∧
    (i.2.2.1.map Prod.fst).Nodup ∧ (∀ e ∈ i.2.2.1, e.1 < i.2.1.length ∧ e.2 < i.1) ∧
    0 < i.2.2.2.2

/-- The network `b` agrees with the parents and tables listed in the instance: for every
`j < k`, `j` is a parent of node `k` exactly when it is listed, and for every listed row
`(u, θ)` and every instantiation `y` of the parents that agrees with `u`, the distribution of
node `k` given `y` is `θ`. Listed indices `≥ k` and unlisted rows impose nothing, so the
network is determined only for well-formed input. -/
def Encodes (i : MostProbableExplanationInstance) (b : BayesNet (Fin i.1) i.2.1.length) :
    Prop :=
  ∀ k : Fin i.2.1.length,
    (∀ j : Fin k, j ∈ b.pa k ↔ (j : ℕ) ∈ (i.2.1[k]).1) ∧
      ∀ row ∈ (i.2.1[k]).2, ∀ y : b.pa k → Fin i.1,
        (∀ j : b.pa k, ∃ m : ℕ, (i.2.1[k]).1[m]? = some (j.1 : ℕ) ∧ row.1[m]? = some (y j : ℕ)) →
          ∀ v : Fin i.1,
            (b.cpt k y).weights v = ((row.2.getD v (0, 1)).1 : ℝ) / (row.2.getD v (0, 1)).2

/-- The threshold `p = (p⁺ - p⁻) / q`. -/
noncomputable def threshold (i : MostProbableExplanationInstance) : ℝ :=
  ((i.2.2.2.1.1 : ℝ) - i.2.2.2.1.2) / i.2.2.2.2

/-- D-MPE: the domain is nonempty and some network `b` that `Encodes` the instance has an
instantiation `x` of all the variables with `Pr(x, e) > p`, where `Pr(x, e)` is `Pr(x)` if `x`
agrees with the evidence and `0` otherwise. For well-formed input, `b` is the network of the
instance. -/
def MostProbableExplanationFeasible (i : MostProbableExplanationInstance) : Prop :=
  ∃ _ : Nonempty (Fin i.1), ∃ b : BayesNet (Fin i.1) i.2.1.length, Encodes i b ∧
    ∃ x : Fin i.2.1.length → Fin i.1,
      threshold i <
        if ∀ e ∈ i.2.2.1, ∃ h : e.1 < i.2.1.length, (x ⟨e.1, h⟩ : ℕ) = e.2 then b.joint x
        else 0

open Classical in
/-- MOST PROBABLE EXPLANATION as a decision problem over bitstrings. -/
noncomputable def mostProbableExplanationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MostProbableExplanationInstance) x with
  | some i => decide (WellFormed i ∧ MostProbableExplanationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MostProbableExplanation
