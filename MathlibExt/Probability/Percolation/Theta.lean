/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Configuration.ProductMeasure
public import MathlibExt.Probability.ProductBondPercolation

/-!
# Percolation probability and the critical point of bond percolation on `ℤ^d`

Bernoulli bond percolation on the hypercubic lattice `ℤ^d`: each nearest-neighbour edge is open
independently with probability `p` (`bernoulliProductMeasure`). This file defines the percolation
probability `θ(p)`, the probability that the open cluster of the origin is infinite, and the
critical probability `p_c(d) = sup {p : θ(p) = 0}`.

## Main definitions

* `StatMech.Percolation.origin`: the origin of `ℤ^d`.
* `StatMech.Percolation.percolationEvent`: the event that the open cluster of the origin is
  infinite.
* `StatMech.Percolation.theta`: the percolation probability `θ_d(p)`.
* `StatMech.Percolation.subcriticalSet`: the set of `p ∈ [0, 1]` with `θ_d(p) = 0`.
* `StatMech.Percolation.pc`: the critical probability `p_c(d)`.
* `StatMech.Percolation.boxFinset`: the box `Λ_n = [-n, n]^d` as a finset.

## Main results

* `StatMech.Percolation.theta_nonneg`, `StatMech.Percolation.theta_le_one`.
* `StatMech.Percolation.cluster_eq_gcluster`: the lattice cluster agrees with the cluster
  `MathlibExt.Probability.ProductBondPercolation.gcluster` of bond percolation on the graph
  `hypercubicLattice d`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, Chapter 1.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace StatMech

namespace Percolation

open StatMech.Lattice

/-- The origin `0 ∈ ℤ^d`. -/
def origin (d : ℕ) : Site d := fun _ => 0

/-- The percolation event `{0 ↔ ∞}`: the open cluster of the origin is infinite. -/
def percolationEvent (d : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (StatMech.Lattice.cluster d ω (origin d)).Infinite}

/-- The percolation probability `θ_d(p) = ℙ_p(0 ↔ ∞)` of Bernoulli bond percolation on `ℤ^d`
with edge density `p`. -/
noncomputable def theta (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : ℝ :=
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (percolationEvent d)

/-- The set of densities `p ∈ [0, 1]` at which `θ_d(p) = 0`. -/
def subcriticalSet (d : ℕ) : Set ℝ≥0 :=
  {p : ℝ≥0 | ∃ hp : p ≤ 1, theta d p hp = 0}

/-- The critical probability `p_c(d) = sup {p ∈ [0, 1] : θ_d(p) = 0}` of bond percolation on `ℤ^d`.

See also `MathlibExt.Probability.ProductBondPercolation.criticalProb`, which defines the critical
point of a general countable graph through the event that *some* infinite cluster exists; the two
agree for `ℤ^d` by translation invariance, but that identification is not proved here. -/
noncomputable def pc (d : ℕ) : ℝ≥0 :=
  sSup (subcriticalSet d)

@[simp]
theorem mem_percolationEvent {d : ℕ} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ percolationEvent d ↔ (StatMech.Lattice.cluster d ω (origin d)).Infinite :=
  Iff.rfl

@[simp]
theorem mem_subcriticalSet {d : ℕ} {p : ℝ≥0} :
    p ∈ subcriticalSet d ↔ ∃ hp : p ≤ 1, theta d p hp = 0 :=
  Iff.rfl

theorem theta_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : 0 ≤ theta d p hp :=
  ENNReal.toReal_nonneg

theorem theta_le_one (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : theta d p hp ≤ 1 := by
  unfold theta
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one

/-- The open cluster of `x` in the lattice model is the cluster
`MathlibExt.Probability.ProductBondPercolation.gcluster` of bond percolation on the graph
`hypercubicLattice d` with the same edge configuration. -/
theorem cluster_eq_gcluster {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    StatMech.Lattice.cluster d ω x =
      MathlibExt.Probability.ProductBondPercolation.gcluster (hypercubicLattice d) ω x := by
  have hG : openSubgraph d ω =
      MathlibExt.Probability.ProductBondPercolation.openSubgraph (hypercubicLattice d) ω := by
    ext a b
    simp only [openSubgraph_adj, MathlibExt.Probability.ProductBondPercolation.openSubgraph,
      SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨h.2, h.1.ne⟩, h.1⟩, fun h => ⟨h.2, h.1.1⟩⟩
  ext y
  simp only [mem_cluster, MathlibExt.Probability.ProductBondPercolation.gcluster, Set.mem_ofPred_eq,
    Connected, hG]

/-- The box `Λ_n = [-n, n]^d` as a finset. -/
noncomputable def boxFinset (d n : ℕ) : Finset (Site d) := (box_finite d n).toFinset

@[simp]
theorem mem_boxFinset {d n : ℕ} {x : Site d} : x ∈ boxFinset d n ↔ x ∈ box d n := by
  rw [boxFinset, Set.Finite.mem_toFinset]

end Percolation

end StatMech
