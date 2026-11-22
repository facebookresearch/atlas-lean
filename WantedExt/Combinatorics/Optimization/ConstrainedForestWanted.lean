/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic

/-!
# The primal–dual method for constrained forest problems (wanted)

M. X. Goemans and D. P. Williamson, "A general approximation technique for constrained forest
problems", *SIAM J. Comput.* 24(2) (1995), 296–317.

A *requirement function* `f : 2^V → {0, 1}` asks for at least one edge across every cut `δ(S)`
with `f(S) = 1`. Goemans and Williamson call `f` *proper* when it is symmetric
(`f(S) = f(V \ S)`) and disjoint sets with `f = 0` have a union with `f = 0` (p. 296); they also
assume `f(V) = 0` (p. 297). Spanning trees, `s`-`t` paths, Steiner trees and `T`-joins
(Table 1, p. 297), and generalized Steiner trees (Steiner forests; text of p. 297) are proper
constrained forest problems.

Their Theorem 2.4 shows that the primal–dual algorithm returns a feasible forest of cost at most
`(2 - 2/|A|)` times the value of a feasible dual solution, `A = {v : f({v}) = 1}`; hence the
ratio between the optimal values of the integer program (IP) and its linear relaxation (LP) is
at most `2 - 2/|A|` (p. 297). The wanted theorem records this integrality-gap consequence,
which is weaker than Theorem 2.4 (it says nothing about the algorithm or its running time).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Optimization.ConstrainedForest

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- **Edges of a cut.** `δ(S)`: the edges of `G` with exactly one endpoint in `S` (Goemans and
Williamson, *SIAM J. Comput.* 24(2) (1995), §1). -/
noncomputable def cutEdges (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∃ u ∈ S, ∃ v ∉ S, e = s(u, v)

/-- **Proper requirement function.** `f : 2^V → {0, 1}` is proper when `f(S) = f(V \ S)` for all
`S`, and `f(A) = f(B) = 0` for disjoint `A`, `B` implies `f(A ∪ B) = 0` (Goemans and Williamson,
*SIAM J. Comput.* 24(2) (1995), §1, properties (i) and (ii), p. 296). -/
def IsProper (f : Finset V → Bool) : Prop :=
  (∀ S, f Sᶜ = f S) ∧
    ∀ A B, Disjoint A B → f A = false → f B = false → f (A ∪ B) = false

/-- **Steiner forest requirement.** For demand pairs `(s_i, t_i)`, `f(S) = 1` exactly when `S`
separates some pair; its minimal feasible forests are the Steiner forests (generalized Steiner
trees) of Goemans and Williamson, *SIAM J. Comput.* 24(2) (1995), §1, p. 297. -/
def steinerForestRequirement (demands : List (V × V)) (S : Finset V) : Bool :=
  demands.any fun d => decide (d.1 ∈ S) != decide (d.2 ∈ S)

open Classical in
/-- **Goemans–Williamson integrality gap for proper constrained forest problems.** Let `G` be a
finite simple graph with nonnegative edge costs `c`, and `f` a proper requirement function with
`f(V) = 0`; put `A = {v : f({v}) = 1}`. For every feasible solution `x ≥ 0` of the linear
relaxation (`x(δ(S)) ≥ 1` whenever `f(S) = 1`) there is a set of edges `F` meeting every cut
`δ(S)` with `f(S) = 1` whose cost is at most `(2 - 2/|A|) ∑_e c_e x_e` (Goemans and Williamson,
*SIAM J. Comput.* 24(2) (1995), Theorem 2.4 and the remark on p. 297 that the ratio between the
optimal values of (IP) and (LP) is at most `2 - 2/|A|`). When `|A| = 0`, Lean's `2 / 0 = 0`
makes the factor `2`; then `f ≡ 0` and `F = ∅` works. -/
theorem_wanted exists_forest_cost_le_of_lp_feasible (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e, 0 ≤ c e) (f : Finset V → Bool) (hf : IsProper f) (hV : f univ = false)
    (x : Sym2 V → ℝ) (hx0 : ∀ e, 0 ≤ x e)
    (hx : ∀ S, f S = true → 1 ≤ ∑ e ∈ cutEdges G S, x e) :
    ∃ F ⊆ G.edgeFinset, (∀ S, f S = true → (F ∩ cutEdges G S).Nonempty) ∧
      ∑ e ∈ F, c e ≤
        (2 - 2 / ((univ.filter fun v => f {v} = true).card : ℝ)) *
          ∑ e ∈ G.edgeFinset, c e * x e

end MathlibExt.Combinatorics.Optimization.ConstrainedForest
