/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MOST PROBABLE EXPLANATION in Bayesian networks is NP-complete

Source:
S. E. Shimony, "Finding MAPs for belief networks is NP-hard", Artificial Intelligence 68
(1994), 399-410, doi:10.1016/0004-3702(94)90072-8;
J. D. Park and A. Darwiche, "Complexity results and approximation strategies for MAP
explanations", Journal of Artificial Intelligence Research 21 (2004), 101-133,
doi:10.1613/jair.1236, arXiv:1107.0024 (§2.2: the decision problem D-MPE, and "D-MPE is
NP-complete (Shimony, 1994)").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.MachineLearning.GraphicalModels.BayesianNetwork
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MostProbableExplanation

open Cslib.MachineLearning.GraphicalModels

/-!
# MOST PROBABLE EXPLANATION in Bayesian networks is NP-complete

INSTANCE: a Bayesian network `(G, Θ)` with rational parameters: a directed acyclic graph `G`
over discrete variables `X`, and for each variable `X` with parents `U` a conditional
probability table assigning a number `θ_{x|u} ∈ [0, 1]` to each value `x` of `X` and each
instantiation `u` of `U`, with `∑ₓ θ_{x|u} = 1`; evidence `e` (an instantiation of a set `E` of
variables); and a rational number `p`.
QUESTION (D-MPE): is there an instantiation `x` of all the network variables such that
`Pr(x, e) > p`? Here `Pr(x) = ∏ θ_{x|u}` over the families of the network, and `Pr(x, e)` is
`Pr(x)` when `x` agrees with `e` and `0` otherwise.

The network is CSLib's `BayesNet (Fin d) n`: the variables `0, …, n - 1` are listed in a
topological order of `G` (every parent of node `k` is a node `j < k`; every DAG has such an
order), and all take values in `{0, …, d - 1}` (a variable with fewer values is padded with
values of probability `0`, which changes no answer). Its joint distribution
`BayesNet.joint` is `Pr`, the product of the table entries (`BayesNet.joint_eq_prod`).

The instance lists, for each node `k`, its parents and its table, row by row: a row `(u, θ)`
gives the parents' values `u` (in the order of the parent list) and the distribution
`θ = (θ_{0|u}, …, θ_{d-1|u})` as fractions `(num, den)`; the table has one row per
instantiation of the parents (`IsNode`). `Encodes i b` says that the network `b` has these
parents and tables. The threshold is `p = (p⁺ - p⁻) / q`, given as `((p⁺, p⁻), q)` with
`q > 0`; the evidence is a list of pairs `(variable, value)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding` (numbers in binary). Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- The network `b` has the parents and tables listed in the instance: node `k`'s parents are
the listed ones, and for every listed row `(u, θ)` and every instantiation `y` of the parents
that agrees with `u`, the distribution of node `k` given `y` is `θ`. -/
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

/-- D-MPE: for the network `b` of the instance, some instantiation `x` of all the variables
has `Pr(x, e) > p`, where `Pr(x, e)` is `Pr(x)` if `x` agrees with the evidence and `0`
otherwise. -/
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

/-- **MOST PROBABLE EXPLANATION (D-MPE) in Bayesian networks is NP-complete.** Source:
Shimony (1994); Park and Darwiche (2004). -/
public theorem_wanted mostProbableExplanation_npComplete :
    mostProbableExplanationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mostProbableExplanationDec

end MetaMathlibExt.Complexity.NPComplete.MostProbableExplanation
