/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume
public import MathlibExt.Probability.Percolation.Theta

/-!
# The critical point of the random-cluster model

The percolation probability `θ(p, q)` of the wired infinite-volume random-cluster measure on `ℤ^d`
and the critical parameter `p_c(q)`.

## i. Overview

`fkTheta d p q` is the probability, under the wired infinite-volume measure `φ^1_{p,q}` on
`ℤ^d`, that the origin lies in an infinite open cluster. The critical point `fkPc d q` is the
supremum of the parameters `p ∈ (0, 1)` with `θ(p, q) = 0`. When `q ≤ 0` the set of such
parameters is empty and `fkPc d q = sSup ∅ = 0`.

## ii. Key results

- `fkTheta` : the percolation probability `φ^1_{p,q}(0 ↔ ∞)`.
- `fkPc` : the critical parameter `sup {p ∈ (0, 1) : θ(p, q) = 0}`.

## iii. Table of contents

- A. The percolation probability
- B. The critical parameter

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §5.1.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

/-! ## A. The percolation probability -/

/-- The percolation probability `θ(p, q) = φ^1_{p,q}(0 ↔ ∞)` of the wired infinite-volume
random-cluster measure on `ℤ^d`.
-/
noncomputable def fkTheta (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : ℝ :=
  ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)

lemma fkTheta_nonneg (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 ≤ fkTheta d hp hp1 hq (q := q) :=
  ENNReal.toReal_nonneg

lemma fkTheta_le_one (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkTheta d hp hp1 hq (q := q) ≤ 1 := by
  unfold fkTheta
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one

/-! ## B. The critical parameter -/

/-- The parameters `p ∈ (0, 1)` at which the wired measure does not percolate (`θ(p, q) = 0`). -/
def fkSubcriticalSet (d : ℕ) (q : ℝ) : Set ℝ :=
  {p : ℝ | ∃ (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q), fkTheta d hp hp1 hq (q := q) = 0}

@[simp]
lemma mem_fkSubcriticalSet {d : ℕ} {q : ℝ} {p : ℝ} :
    p ∈ fkSubcriticalSet d q ↔
      ∃ (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q), fkTheta d hp hp1 hq (q := q) = 0 :=
  Iff.rfl

/-- The critical parameter `p_c(q) = sup {p ∈ (0, 1) : θ(p, q) = 0}` of the random-cluster model on
`ℤ^d` (equal to `0` when the set is empty, e.g. for `q ≤ 0`).
-/
noncomputable def fkPc (d : ℕ) (q : ℝ) : ℝ :=
  sSup (fkSubcriticalSet d q)

end FK

end StatMech
