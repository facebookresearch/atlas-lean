/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complex balancing and detailed balancing under formal balancing

A reversible mass-action system is a finite digraph on vertices `V` without loops, whose vertex
`i` is labelled by a complex `y_i ∈ ℕ^S` (distinct vertices may carry the same complex), with a
rate constant `κ_{ij} > 0` on each edge `i → j`, and such that `j → i` is an edge whenever
`i → j` is. Rate constants are encoded as a matrix `κ` with `κ_{ii} = 0`, `κ_{ij} ≥ 0`, and
`κ_{ij} > 0` exactly on the edges. The system `dc/dt = Ψ(c) A_κ Y`, with
`Ψ(c) = (c^{y_1}, …, c^{y_n})`, is

* **complex balanced** if `Ψ(c) A_κ = 0` for some positive `c`, that is, at every vertex `i` the
  inflow `∑_j κ_{ji} c^{y_j}` equals the outflow `∑_j κ_{ij} c^{y_i}`;
* **detailed balanced** if for some positive `c`, `κ_{ij} c^{y_i} = κ_{ji} c^{y_j}` for every
  edge `i → j`;
* **formally balanced** if for every cycle of the underlying undirected simple graph, the product
  of the rate constants along one orientation equals the product along the other.

**Theorem 1.1** (Dickenstein–Pérez Millán 2011). For a reversible mass-action system, the rate
constants are formally balanced and the system is complex balanced if and only if the system is
detailed balanced.

Complex balance is stated per vertex, as in the source, so vertices with equal complexes are not
aggregated. A cycle of the undirected graph is a sequence of `m ≥ 3` distinct vertices with
consecutive vertices (cyclically) adjacent. The source proves the implication from detailed
balance to formal balance by citing Feinberg (1989). Complex balance of mass-action networks with
natural-number complexes is developed in `Domains.Biology.Dynamics.ComplexBalanced`, and
Kolmogorov's cycle criterion for Markov chains in
`MathlibExt.Probability.KolmogorovCycleSufficiency` and
`MathlibExt.Probability.KolmogorovCycleNecessity`; neither states this theorem.

Sources: A. Dickenstein, M. Pérez Millán, "How far is complex balancing from detailed
balancing?", Bull. Math. Biol. 73 (2011) 811–828, Section 1, Theorem 1.1 (arXiv:1001.0947);
M. Feinberg, "Necessary and sufficient conditions for detailed balancing in mass action
systems of arbitrary complexity", Chem. Eng. Sci. 44 (1989) 1819–1827.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace WantedExt.Biology.Biophysics.ComplexDetailedBalanceWanted

variable {V S : Type*} [Fintype V] [Fintype S]

/-- The monomial `c^y = ∏_s c_s ^ y_s`. -/
noncomputable def monomial (c : S → ℝ) (y : S → ℕ) : ℝ :=
  ∏ s, c s ^ y s

/-- `κ` is the rate matrix of a reversible mass-action system on the vertices `V`: no loops,
nonnegative entries, and `κ i j > 0` exactly when `κ j i > 0` (every edge has its reverse). -/
def IsReversibleRates (κ : V → V → ℝ) : Prop :=
  (∀ i, κ i i = 0) ∧ (∀ i j, 0 ≤ κ i j) ∧ ∀ i j, 0 < κ i j → 0 < κ j i

/-- The system is complex balanced: some positive `c` has `Ψ(c) A_κ = 0`, that is, at every
vertex `i`, `∑_j κ_{ji} c^{y_j} = (∑_j κ_{ij}) c^{y_i}`. -/
def IsComplexBalanced (y : V → S → ℕ) (κ : V → V → ℝ) : Prop :=
  ∃ c : S → ℝ, (∀ s, 0 < c s) ∧
    ∀ i, ∑ j, κ j i * monomial c (y j) = (∑ j, κ i j) * monomial c (y i)

/-- The system is detailed balanced: some positive `c` has `κ_{ij} c^{y_i} = κ_{ji} c^{y_j}` for
all vertices `i`, `j` (for reversible rates, `IsReversibleRates`, both sides vanish on
non-edges). -/
def IsDetailedBalanced (y : V → S → ℕ) (κ : V → V → ℝ) : Prop :=
  ∃ c : S → ℝ, (∀ s, 0 < c s) ∧ ∀ i j, κ i j * monomial c (y i) = κ j i * monomial c (y j)

/-- The rate constants are formally balanced: for every cycle `v_0, …, v_{m+2}` of `m + 3 ≥ 3`
distinct vertices with `κ (v i) (v (i + 1)) > 0` for every `i` (indices mod `m + 3`), the product
of the rate constants along the cycle equals the product along the reversed cycle. -/
def IsFormallyBalanced (κ : V → V → ℝ) : Prop :=
  ∀ (m : ℕ) (v : Fin (m + 3) → V), Function.Injective v →
    (∀ i, 0 < κ (v i) (v (i + 1))) →
      ∏ i, κ (v i) (v (i + 1)) = ∏ i, κ (v (i + 1)) (v i)

/-- **Complex balance under formal balance is detailed balance** (Dickenstein–Pérez Millán 2011,
Theorem 1.1). Let `V` and `S` be finite, let `y : V → S → ℕ` label the vertices by complexes
(not necessarily distinct), and let `κ` be the rate matrix of a reversible mass-action system:
`κ i i = 0`, `κ i j ≥ 0`, and `κ i j > 0` implies `κ j i > 0`. Then the rate constants are
formally balanced and the system is complex balanced (some positive `c` has `Ψ(c) A_κ = 0`) if
and only if the system is detailed balanced (some positive `c` has
`κ_{ij} c^{y_i} = κ_{ji} c^{y_j}` for all `i`, `j`).

Source: A. Dickenstein, M. Pérez Millán, Bull. Math. Biol. 73 (2011) 811–828, Theorem 1.1. -/
theorem_wanted isFormallyBalanced_and_isComplexBalanced_iff_isDetailedBalanced
    (y : V → S → ℕ) {κ : V → V → ℝ} (hκ : IsReversibleRates κ) :
    IsFormallyBalanced κ ∧ IsComplexBalanced y κ ↔ IsDetailedBalanced y κ

end WantedExt.Biology.Biophysics.ComplexDetailedBalanceWanted
