/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MODULARITY MAXIMIZATION is NP-complete

Source:
U. Brandes, D. Delling, M. Gaertler, R. Görke, M. Hoefer, Z. Nikoloski and D. Wagner, "On
modularity clustering", IEEE Transactions on Knowledge and Data Engineering 20(2) (2008),
172-188, doi:10.1109/TKDE.2007.190689 (arXiv:physics/0608255: Problem 1 (Modularity) and
Theorem 3, "Modularity is strongly NP-complete", by a transformation from 3-PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ModularityMaximization

/-!
# MODULARITY MAXIMIZATION is NP-complete

INSTANCE: a graph `G = (V, E)` with at least one edge and a rational number `K`.
QUESTION: is there a clustering `𝒞` of `G` (a partition of `V` into clusters) whose modularity
`Q(𝒞) = ∑_{C ∈ 𝒞} ( |E(C)| / m - (∑_{v ∈ C} deg(v) / (2m))² )` is at least `K`?

This is Brandes et al.'s decision problem "Problem 1 (Modularity) Given a graph G and a number
K, is there a clustering C of G, for which Q(C) ≥ K?", with modularity in their form (2): `m`
is the number of edges, `E(C)` the set of edges with both endpoints in the cluster `C`, and
`deg(v)` "the number of edges incident to v". They note that `4m² · Q(𝒞)` is an integer, so a
rational `K` loses nothing, and prove the problem NP-complete in the strong sense.

The vertices are `0, …, n - 1` and the edges a simple edge list (no loops, no repeated edge in
either orientation, endpoints below `n`); `m ≥ 1` is required, since `Q` divides by `m`. `K` is
any rational, given as `(p - r) / q` with natural numbers `p`, `r` (positive and negative part)
and `q > 0`. A clustering is given by a labelling `c : ℕ → ℕ`: its clusters are the nonempty classes
`{v < n | c v = j}`, indexed by the labels `j` in the image of `{0, …, n - 1}`; every partition of
`V` arises this way.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, edge list, and the bound `K = (p - r) / q` as
`((p, r), q)`. -/
abbrev ModularityMaximizationInstance := ℕ × List (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)

/-- Well-formedness of an instance: the edge list is a simple graph on `0, …, n - 1` with at
least one edge, and the denominator of `K` is positive. -/
def WellFormed (i : ModularityMaximizationInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.1 ≠ [] ∧ 0 < i.2.2.2

/-- The degree of `v`: the number of edges incident to `v`. -/
def degree (i : ModularityMaximizationInstance) (v : ℕ) : ℕ :=
  i.2.1.countP fun e => e.1 = v ∨ e.2 = v

/-- The modularity of the clustering whose clusters are the classes `{v < n | c v = j}`:
the sum over clusters `C` of `|E(C)| / m - (∑_{v ∈ C} deg(v) / (2m))²`. -/
def modularity (i : ModularityMaximizationInstance) (c : ℕ → ℕ) : ℚ :=
  ∑ j ∈ (Finset.range i.1).image c,
    (((i.2.1.countP fun e => c e.1 = j ∧ c e.2 = j : ℕ) : ℚ) / i.2.1.length -
      (((∑ v ∈ (Finset.range i.1).filter (fun v => c v = j), degree i v : ℕ) : ℚ) /
        (2 * i.2.1.length)) ^ 2)

/-- Some clustering has modularity at least `K = (p - r) / q`. -/
def ModularityMaximizationFeasible (i : ModularityMaximizationInstance) : Prop :=
  ∃ c : ℕ → ℕ, ((i.2.2.1.1 : ℚ) - i.2.2.1.2) / i.2.2.2 ≤ modularity i c

open Classical in
/-- MODULARITY MAXIMIZATION as a decision problem over bitstrings. -/
noncomputable def modularityMaximizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ModularityMaximizationInstance) x with
  | some i => decide (WellFormed i ∧ ModularityMaximizationFeasible i)
  | none => false

/-- **MODULARITY MAXIMIZATION is NP-complete.** Source: Brandes, Delling, Gaertler, Görke, Hoefer,
Nikoloski and Wagner (2008), Theorem 3. -/
public theorem_wanted modularityMaximization_npComplete :
    modularityMaximizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L modularityMaximizationDec

end MetaMathlibExt.Complexity.NPComplete.ModularityMaximization
