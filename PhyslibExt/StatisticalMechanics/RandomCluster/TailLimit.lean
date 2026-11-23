/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint
/-!
# The FK percolation probability as a limit of crossing probabilities

`θ(p, q) = φ¹(0 ↔ ∞)` is the limit of `φ¹(0 ↔ ∂Λ_n)` under the chosen wired infinite-volume
measure.

## i. Overview

The crossing events `{0 ↔ ℤ^d \ Λ_(n-1)}` decrease in `n` and their intersection is the event
that the cluster of the origin is infinite. Continuity of measure from above gives the limit.
Both sides refer to the same measure `wiredInfiniteVolume`; no finite-volume measure is involved.

## ii. Key results

- `iInter_crossingEvent_eq_percolationEvent` : `⋂_n {0 ↔ ℤ^d \ Λ_(n-1)} = {|C(0)| = ∞}`.
- `fkBoundaryConnReal_tendsto_fkTheta` : `φ¹(0 ↔ ∂Λ_n) → θ(p, q)`.
- `fkTheta_eq_lim_boundary` : the same, as an equation with `limUnder`.

## iii. Table of contents

- A. Crossing events
- B. The limit

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-!
## A. Crossing events
-/

/-- The crossing events intersect to the percolation event. See also
`Percolation.percolationEvent_eq_iInter` (`Sharpness`), the same fact indexed from `n + 1`. -/
lemma iInter_crossingEvent_eq_percolationEvent :
    (⋂ n : ℕ, crossingEvent d n) = percolationEvent d := by
  ext ω
  simp only [Set.mem_iInter, mem_crossingEvent, percolationEvent, Set.mem_ofPred_eq,
    cluster_infinite_iff]
  constructor
  · intro h m
    obtain ⟨v, hconn, hv⟩ := h (m + 1)
    exact ⟨v, by simpa using hv, hconn⟩
  · intro h n
    obtain ⟨y, hyb, hyc⟩ := h (n - 1)
    exact ⟨y, hyc, hyb⟩

/-!
## B. The limit
-/

/-- The probability, under the chosen wired infinite-volume measure, that the origin is connected to
the complement of `Λ_(n-1)`. -/
noncomputable def fkBoundaryConnReal (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (n : ℕ) : ℝ :=
  ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (crossingEvent d n)

/-- The crossing probabilities of the wired infinite-volume measure converge to the percolation
probability `fkTheta`. -/
lemma fkBoundaryConnReal_tendsto_fkTheta {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Tendsto (fun n => fkBoundaryConnReal d hp hp1 hq n) atTop
      (𝓝 (fkTheta d hp hp1 hq (q := q))) := by
  set μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) with hμ
  have hmeas : ∀ n, NullMeasurableSet (crossingEvent d n) μ :=
    fun n => (Percolation.measurableSet_crossingEvent n).nullMeasurableSet
  have hanti : Antitone (fun n => crossingEvent d n) :=
    fun m n hmn => crossingEvent_antitone m n hmn
  have hfin : ∃ i, μ (crossingEvent d i) ≠ ∞ := ⟨0, measure_ne_top μ _⟩
  have htends := tendsto_measure_iInter_atTop (μ := μ) hmeas hanti hfin
  rw [iInter_crossingEvent_eq_percolationEvent] at htends
  have hne : μ (percolationEvent d) ≠ ∞ := measure_ne_top μ _
  have hreal := (ENNReal.tendsto_toReal hne).comp htends
  convert hreal using 2 with n <;> rfl

lemma fkTheta_eq_lim_boundary {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkTheta d hp hp1 hq (q := q)
      = limUnder atTop (fun n => fkBoundaryConnReal d hp hp1 hq n) :=
  (fkBoundaryConnReal_tendsto_fkTheta hp hp1 hq).limUnder_eq.symm

end FK

end StatMech
