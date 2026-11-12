/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.FrontierB.CurrentTraceInsertion
import Code.FrontierB.CurrentTraceLatticeUniquenessCore

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation




theorem latticeFiniteEnergyMerge_excludes_finite_ge_two
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasLatticeFiniteEnergyMerge μ) {k : ℕ∞}
    (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (hk2 : 2 ≤ k) (hktop : k ≠ ⊤) : False :=
  latticeInsertionMerge_excludes_finite_ge_two μ hfe hk hk2 hktop




theorem latticeFiniteEnergy_canonical_uniqueness
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasLatticeFiniteEnergyMerge μ)
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsCanonicalTrifurcation d ω 0}) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  latticeInsertion_canonical_uniqueness μ hd herg hfe htrif



theorem freeFreeSuperposedTraceLaw_canonical_uniqueness
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d)))))
    (htrif : 0 < (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))
          {ω | numInfiniteClusters d ω = ⊤} →
      0 < (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))
          {ω | IsCanonicalTrifurcation d ω 0}) :
    let μ := (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  dsimp only
  exact latticeFiniteEnergy_canonical_uniqueness (d := d) _ hd herg
    (freeFreeSuperposedTraceLaw_hasLatticeFiniteEnergyMerge d beta hbeta) htrif



theorem freePlusSuperposedTraceLaw_canonical_uniqueness
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d)))))
    (htrif : 0 < (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))
          {ω | numInfiniteClusters d ω = ⊤} →
      0 < (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))
          {ω | IsCanonicalTrifurcation d ω 0}) :
    let μ := (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  dsimp only
  exact latticeFiniteEnergy_canonical_uniqueness (d := d) _ hd herg
    (freePlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge d beta hbeta) htrif



theorem plusPlusSuperposedTraceLaw_canonical_uniqueness
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d)))))
    (htrif : 0 < (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))
          {ω | numInfiniteClusters d ω = ⊤} →
      0 < (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d))))
          {ω | IsCanonicalTrifurcation d ω 0}) :
    let μ := (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  dsimp only
  exact latticeFiniteEnergy_canonical_uniqueness (d := d) _ hd herg
    (plusPlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge d beta hbeta) htrif

end StatMech.FrontierB
