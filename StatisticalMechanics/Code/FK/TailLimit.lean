/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.FK.CriticalPoint
import Code.Percolation.SubcriticalDecay
import Code.Percolation.BurtonKeane

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}











theorem iInter_crossingEvent_eq_percolationEvent :
    (⋂ n : ℕ, crossingEvent d n) = percolationEvent d := by
  ext ω
  simp only [Set.mem_iInter, mem_crossingEvent, percolationEvent, Set.mem_setOf_eq,
    cluster_infinite_iff]
  constructor
  · 
    intro h m
    obtain ⟨v, hconn, hv⟩ := h (m + 1)
    exact ⟨v, by simpa using hv, hconn⟩
  · 
    intro h n
    obtain ⟨y, hyb, hyc⟩ := h (n - 1)
    exact ⟨y, hyc, hyb⟩






theorem measurableSet_crossingEvent (n : ℕ) :
    MeasurableSet (crossingEvent d n) := by
  have heq : crossingEvent d n
      = ⋃ y ∈ {y : Site d | y ∉ box d (n - 1)}, {ω | Connected d ω (origin d) y} := by
    ext ω
    simp only [mem_crossingEvent, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hc, hv⟩ => ⟨v, hv, hc⟩, fun ⟨v, hv, hc⟩ => ⟨v, hc, hv⟩⟩
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun y _ => measurableSet_connected (origin d) y)








noncomputable def fkBoundaryConnReal (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (n : ℕ) : ℝ :=
  ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (crossingEvent d n)





















theorem fkBoundaryConnReal_tendsto_fkTheta {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Tendsto (fun n => fkBoundaryConnReal d hp hp1 hq n) atTop
      (𝓝 (fkTheta d hp hp1 hq (q := q))) := by
  set μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) with hμ
  
  have hmeas : ∀ n, NullMeasurableSet (crossingEvent d n) μ :=
    fun n => (measurableSet_crossingEvent n).nullMeasurableSet
  have hanti : Antitone (fun n => crossingEvent d n) :=
    fun m n hmn => crossingEvent_antitone m n hmn
  have hfin : ∃ i, μ (crossingEvent d i) ≠ ∞ := ⟨0, measure_ne_top μ _⟩
  have htends := tendsto_measure_iInter_atTop (μ := μ) hmeas hanti hfin
  rw [iInter_crossingEvent_eq_percolationEvent] at htends
  
  have hne : μ (percolationEvent d) ≠ ∞ := measure_ne_top μ _
  have hreal := (ENNReal.tendsto_toReal hne).comp htends
  
  convert hreal using 2 with n








theorem fkTheta_eq_lim_boundary {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkTheta d hp hp1 hq (q := q)
      = limUnder atTop (fun n => fkBoundaryConnReal d hp hp1 hq n) :=
  (fkBoundaryConnReal_tendsto_fkTheta hp hp1 hq).limUnder_eq.symm

end FK

end StatMech
