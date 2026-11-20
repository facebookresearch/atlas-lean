/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Code.Foundations.WeakConvergence
import Code.Foundations.Ergodicity
import Code.FK.InfiniteVolume
import Code.Percolation.BurtonKeane

open MeasureTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice

namespace StatMech

namespace FK






















theorem erg_map_eq_of_translated_converges {E : Type*} [Countable E]
    (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) (ν : ProbabilityMeasure (ConfigSpace E))
    {T : ConfigSpace E → ConfigSpace E} (hT : Continuous T)
    (hconv : WeakConvergesTo μ ν)
    (hshift : WeakConvergesTo (fun n => (μ n).map hT.measurable.aemeasurable) ν) :
    ν.map hT.measurable.aemeasurable = ν :=
  tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hconv hT) hshift



theorem erg_measure_map_eq_of_translated_converges {E : Type*} [Countable E]
    (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) (ν : ProbabilityMeasure (ConfigSpace E))
    {T : ConfigSpace E → ConfigSpace E} (hT : Continuous T)
    (hconv : WeakConvergesTo μ ν)
    (hshift : WeakConvergesTo (fun n => (μ n).map hT.measurable.aemeasurable) ν) :
    Measure.map T (ν : Measure (ConfigSpace E)) = (ν : Measure (ConfigSpace E)) := by
  have h := erg_map_eq_of_translated_converges μ ν hT hconv hshift
  have h2 : ((ν.map hT.measurable.aemeasurable : ProbabilityMeasure (ConfigSpace E))
      : Measure (ConfigSpace E)) = (ν : Measure (ConfigSpace E)) := by rw [h]
  rwa [ProbabilityMeasure.toMeasure_map] at h2









variable {d : ℕ}



noncomputable def erg_wiredShiftedFinite {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (wiredFiniteMeasure d n hp hp1 hq).map (continuous_shift g).measurable.aemeasurable


noncomputable def erg_freeShiftedFinite {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (freeFiniteMeasure d n hp hp1 hq).map (continuous_shift g).measurable.aemeasurable














theorem erg_wiredIV_map_shift {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d))
    (hshift : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n))
          (wiredInfiniteVolume d hp hp1 hq)) :
    Measure.map (shift g)
        (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  obtain ⟨φ, hφ, hconv⟩ := wiredInfiniteVolume_isLimit d hp hp1 hq
  exact erg_measure_map_eq_of_translated_converges
    (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq)
    (continuous_shift g) hconv (hshift φ hφ hconv)



theorem erg_freeIV_map_shift {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d))
    (hshift : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n))
          (freeInfiniteVolume d hp hp1 hq)) :
    Measure.map (shift g)
        (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  obtain ⟨φ, hφ, hconv⟩ := freeInfiniteVolume_isLimit d hp hp1 hq
  exact erg_measure_map_eq_of_translated_converges
    (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq)
    (continuous_shift g) hconv (hshift φ hφ hconv)










theorem erg_wiredIV_isTranslationInvariant {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hshift : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n))
          (wiredInfiniteVolume d hp hp1 hq)) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, erg_wiredIV_map_shift hp hp1 hq g (hshift g)⟩




theorem erg_freeIV_isTranslationInvariant {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hshift : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n))
          (freeInfiniteVolume d hp hp1 hq)) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, erg_freeIV_map_shift hp hp1 hq g (hshift g)⟩

end FK

end StatMech
