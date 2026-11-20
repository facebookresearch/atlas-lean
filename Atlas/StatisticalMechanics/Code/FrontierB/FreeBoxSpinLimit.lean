/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.FreeBoxEvenLimit

open MeasureTheory Filter Topology

namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

theorem isingExpectation_boxSpinSupport_mono_field
    (d : ℕ) {n m : ℕ} (hnm : n ≤ m) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (A : Finset (Site d)) (hA : ↑A ⊆ box d n) :
    isingExpectation (sctBoxGraph d n) beta h
        (spinProd (boxSpinSupport d n A)) ≤
      isingExpectation (sctBoxGraph d m) beta h
        (spinProd (boxSpinSupport d m A)) := by
  let e := sctBoxInclusionEquiv d hnm
  calc
    isingExpectation (sctBoxGraph d n) beta h
        (spinProd (boxSpinSupport d n A)) =
        isingExpectation
          ((sctBoxGraph d m).comap
            (Subtype.val :
              {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m)) beta h
          (spinProd ((boxSpinSupport d n A).map e.toEmbedding)) := by
      exact isingExpectation_spinProd_relabel (sctBoxGraph d n)
        ((sctBoxGraph d m).comap
          (Subtype.val :
            {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m))
        e (sctBoxInclusionEquiv_adj d hnm) beta h (boxSpinSupport d n A)
    _ ≤ isingExpectation (sctBoxGraph d m) beta h
          (spinProd (((boxSpinSupport d n A).map e.toEmbedding).map
            (Function.Embedding.subtype (sctBoxInLarger d n m)))) :=
      isingExpectation_spinProd_induce_le (sctBoxGraph d m)
        (sctBoxInLarger d n m) beta h hbeta hh _
    _ = isingExpectation (sctBoxGraph d m) beta h
          (spinProd (boxSpinSupport d m A)) := by
      rw [boxSpinSupport_map_inclusion d hnm A hA]



theorem integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field
    (d : ℕ) (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (A : Finset (Site d)) :
    Tendsto
      (fun n => ∫ omega, spinProd A omega
        ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta h : Measure (ConfigSpace (Site d))))) := by
  let a : ℕ → ℝ := fun n =>
    ∫ omega, spinProd A omega
      ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d)))
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  have hA_add (k : ℕ) : ↑A ⊆ box d (k + N) :=
    hAN.trans (box_mono d (Nat.le_add_left N k))
  have htail_mono : Monotone (fun k => a (k + N)) := by
    intro k l hkl
    change a (k + N) ≤ a (l + N)
    rw [show a (k + N) = isingExpectation (sctBoxGraph d (k + N)) beta h
        (spinProd (boxSpinSupport d (k + N) A)) by
      exact integral_freeMeasure_spinProd d (k + N) beta h A (hA_add k)]
    rw [show a (l + N) = isingExpectation (sctBoxGraph d (l + N)) beta h
        (spinProd (boxSpinSupport d (l + N) A)) by
      exact integral_freeMeasure_spinProd d (l + N) beta h A (hA_add l)]
    exact isingExpectation_boxSpinSupport_mono_field d
      (Nat.add_le_add_right hkl N) beta h hbeta hh A (hA_add k)
  have htail_bdd : BddAbove (Set.range (fun k => a (k + N))) := by
    refine ⟨1, ?_⟩
    rintro y ⟨k, rfl⟩
    change a (k + N) ≤ 1
    rw [show a (k + N) = isingExpectation (sctBoxGraph d (k + N)) beta h
        (spinProd (boxSpinSupport d (k + N) A)) by
      exact integral_freeMeasure_spinProd d (k + N) beta h A (hA_add k)]
    exact isingExpectation_spinProd_le_one (sctBoxGraph d (k + N)) beta h _
  let L : ℝ := ⨆ k, a (k + N)
  have htail : Tendsto (fun k => a (k + N)) atTop (nhds L) := by
    simpa only [L] using tendsto_atTop_ciSup htail_mono htail_bdd
  have hfull : Tendsto a atTop (nhds L) :=
    (tendsto_add_atTop_iff_nat N).1 htail
  obtain ⟨phi, hphi, hweak⟩ := freeState_isInfiniteVolumeState d beta h
  have hsub_free := hweak.tendsto_integral (spinProdBCF d A)
  have hsub_L : Tendsto (fun k => a (phi k)) atTop (nhds L) :=
    hfull.comp hphi.tendsto_atTop
  have hsub_free' : Tendsto (fun k => a (phi k)) atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta h : Measure (ConfigSpace (Site d))))) := by
    simpa only [a, Function.comp_apply, spinProdBCF_apply] using hsub_free
  have hL : L = ∫ omega, spinProd A omega
      ∂(freeState d beta h : Measure (ConfigSpace (Site d))) :=
    tendsto_nhds_unique hsub_L hsub_free'
  simpa only [a, hL] using hfull

end StatMech.FrontierB
