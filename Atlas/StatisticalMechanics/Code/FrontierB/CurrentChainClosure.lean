/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.MixedCurrentTraceFactor
import Code.FrontierB.InfinitePlusFreeSourceSwitching
import Code.FrontierB.CurrentContinuityPersistence

open MeasureTheory Set

namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation Sharpness Ising



theorem plusFreeSuperposedTraceLaw_uniqueness
    (d : Nat) (beta : Real) (hbeta : 0 <= beta) (hd : 1 <= d) :
    let mu := (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d beta hbeta)
      (infiniteFreeCurrentMeasure d beta hbeta) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨
        mu {omega | numInfiniteClusters d omega = 1} = 1) ∧
      mu (atLeastTwoInfinite d) = 0 ∧
      mu {omega | numInfiniteClusters d omega <= 1} = 1 := by
  dsimp only
  rw [independentSuperposedTraceLaw_comm]
  exact freePlusSuperposedTraceLaw_uniqueness d beta hbeta hd



theorem infinitePlusFreeSource_switching
    (d N : Nat) (hd : 1 <= d) (beta : Real) (hbeta : 0 < beta)
    (x y : Site d) (hx : x ∈ box d N) (hy : y ∈ box d N)
    (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    ((∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
      (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) *
      (((infinitePlusPairSourceCurrentMeasure
          d N beta hbeta x y hx hy hxy).prod
        (infiniteFreePairSourceCurrentMeasure
          d N beta hbeta x y hx hy hxy) : Measure _).real
            (superposedCurrentTrace ⁻¹' Q)) =
      (((infinitePlusCurrentMeasure d beta hbeta.le).prod
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real
          (currentPairTraceConnectionGate Q x y)) := by
  have hunique :=
    (plusFreeSuperposedTraceLaw_uniqueness
      d beta hbeta.le hd).2.1
  exact infinitePlusFreeSource_switching_of_uniqueInfiniteCluster
    d N beta hbeta x y hx hy hxy hunique Q hQ



theorem currentContinuityMixedTraceLaw_genMixing
    (d : Nat) (hd : 1 <= d) (beta : Real) (hbeta : 0 < beta) :
    fmu_GenMixing (G := Multiplicative (Site d))
      (currentContinuityMixedTraceLaw d beta hbeta :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  change fmu_GenMixing (G := Multiplicative (Site d))
    (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d))))
  rw [independentSuperposedTraceLaw_comm]
  exact freePlusSuperposedTraceLaw_genMixing hd hbeta

theorem currentContinuityMixedTraceLaw_isTranslationInvariant
    (d : Nat) (beta : Real) (hbeta : 0 < beta) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (currentContinuityMixedTraceLaw d beta hbeta :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  change IsTranslationInvariant (G := Multiplicative (Site d))
    (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d))))
  rw [independentSuperposedTraceLaw_comm]
  exact freePlusSuperposedTraceLaw_isTranslationInvariant hbeta

theorem currentContinuityMixedTraceLaw_uniqueInfiniteCluster
    (d : Nat) (hd : 1 <= d) (beta : Real) (hbeta : 0 < beta) :
    (currentContinuityMixedTraceLaw d beta hbeta : Measure _)
      (atLeastTwoInfinite d) = 0 := by
  exact (plusFreeSuperposedTraceLaw_uniqueness
    d beta hbeta.le hd).2.1



theorem currentContinuityMixedTraceLaw_percolationPrinciple
    (d : Nat) (hd : 1 <= d) (beta : Real) (hbeta : 0 < beta) :
    CurrentContinuityPercolationPrinciple d
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
  exact currentContinuityPercolationPrinciple_of_genMixing
    d hd (currentContinuityMixedTraceLaw d beta hbeta)
    (currentContinuityMixedTraceLaw_isTranslationInvariant d beta hbeta)
    (currentContinuityMixedTraceLaw_genMixing d hd beta hbeta)
    (currentContinuityMixedTraceLaw_uniqueInfiniteCluster
      d hd beta hbeta)

end StatMech.FrontierB
