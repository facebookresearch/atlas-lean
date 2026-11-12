/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.WeakConvergence
public import MathlibExt.Probability.Configuration.Ergodicity
public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume
public import MathlibExt.Probability.Percolation.InfiniteClusterCount

/-!
# Translation invariance of infinite-volume random-cluster measures

If the shifted finite-volume random-cluster measures converge to the same limit as the unshifted
ones, the wired and free infinite-volume measures on `ℤ^d` are translation invariant.

## i. Overview

A weak limit `ν` of measures `μ_n` is invariant under a continuous map `T` as soon as the pushed
forward measures `T_* μ_n` also converge to `ν`. Applied to the wired and free finite-volume
measures on boxes and the translations of `ℤ^d`, this gives translation invariance of the
infinite-volume measures, conditional on the convergence of the shifted sequences (`hshift`).

## ii. Key results

- `erg_map_eq_of_translated_converges` : invariance of weak limits.
- `erg_wiredIV_isTranslationInvariant`, `erg_freeIV_isTranslationInvariant` : translation
  invariance of the wired and free infinite-volume measures, given `hshift`.

## iii. Table of contents

- A. Invariance of weak limits
- B. Shifted finite-volume measures
- C. Translation invariance

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.19.
-/

@[expose] public section

open MeasureTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice

namespace StatMech

namespace FK

/-! ## A. Invariance of weak limits -/

lemma erg_map_eq_of_translated_converges {E : Type*} [Countable E]
    (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) (ν : ProbabilityMeasure (ConfigSpace E))
    {T : ConfigSpace E → ConfigSpace E} (hT : Continuous T)
    (hconv : WeakConvergesTo μ ν)
    (hshift : WeakConvergesTo (fun n => (μ n).map T) ν) :
    ν.map T = ν :=
  tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hconv hT) hshift

lemma erg_measure_map_eq_of_translated_converges {E : Type*} [Countable E]
    (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) (ν : ProbabilityMeasure (ConfigSpace E))
    {T : ConfigSpace E → ConfigSpace E} (hT : Continuous T)
    (hconv : WeakConvergesTo μ ν)
    (hshift : WeakConvergesTo (fun n => (μ n).map T) ν) :
    Measure.map T (ν : Measure (ConfigSpace E)) = (ν : Measure (ConfigSpace E)) := by
  have h := erg_map_eq_of_translated_converges μ ν hT hconv hshift
  have h2 : ((ν.map T : ProbabilityMeasure (ConfigSpace E))
      : Measure (ConfigSpace E)) = (ν : Measure (ConfigSpace E)) := by rw [h]
  rwa [ProbabilityMeasure.toMeasure_map] at h2

variable {d : ℕ}

/-! ## B. Shifted finite-volume measures -/

/-- The wired finite-volume random-cluster measure on `Λ_n` translated by `g`. -/
noncomputable def erg_wiredShiftedFinite {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (wiredFiniteMeasure d n hp hp1 hq).map (shift g)

/-- The free finite-volume random-cluster measure on `Λ_n` translated by `g`. -/
noncomputable def erg_freeShiftedFinite {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (freeFiniteMeasure d n hp hp1 hq).map (shift g)

lemma erg_wiredIV_map_shift {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
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

lemma erg_freeIV_map_shift {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
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

/-! ## C. Translation invariance -/

lemma erg_wiredIV_isTranslationInvariant {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hshift : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n))
          (wiredInfiniteVolume d hp hp1 hq)) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, erg_wiredIV_map_shift hp hp1 hq g (hshift g)⟩

lemma erg_freeIV_isTranslationInvariant {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
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
