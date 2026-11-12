/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.GenMixingCofinite
import Code.FrontierB.CurrentContinuityReduction
import Code.OSSS.FKSharpnessWeightedPhaseTransport

open MeasureTheory Set

namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation
open StatMech.OSSS.FKSharpnessWeightedPhaseTransport


noncomputable def originShiftBox (d R : Nat) :
    Finset (Multiplicative (Site d)) :=
  (box_finite d R).toFinset.image
    (fun x => Multiplicative.ofAdd (-x))

theorem inverse_smul_origin_not_mem_box_of_not_mem_originShiftBox
    {d R : Nat} (g : Multiplicative (Site d))
    (hg : g ∉ originShiftBox d R) :
    g⁻¹ • origin d ∉ box d R := by
  intro hx
  apply hg
  rw [originShiftBox, Finset.mem_image]
  refine ⟨g⁻¹ • origin d, ?_, ?_⟩
  · exact (Set.Finite.mem_toFinset (box_finite d R)).2 hx
  · change -(g⁻¹ • origin d) = Multiplicative.toAdd g
    funext i
    simp [smul_site_apply, origin]




theorem currentContinuityPercolationPrinciple_of_genMixing
    (d : Nat) (hd : 1 ≤ d)
    (rho : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (rho : Measure (ConfigSpace (Sym2 (Site d)))))
    (hmix : fmu_GenMixing (G := Multiplicative (Site d))
      (rho : Measure (ConfigSpace (Sym2 (Site d)))))
    (hunique : (rho : Measure (ConfigSpace (Sym2 (Site d))))
      (atLeastTwoInfinite d) = 0) :
    CurrentContinuityPercolationPrinciple d
      (rho : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro htheta
  let theta := (rho : Measure (ConfigSpace (Sym2 (Site d)))).real
    (percolationEvent d)
  let epsilon := theta ^ 2 / 2
  have htheta' : 0 < theta := htheta
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  refine ⟨epsilon, hepsilon, ?_⟩
  intro R
  let tolerance := theta ^ 2 / 20
  have htolerance : 0 < tolerance := by
    dsimp [tolerance]
    positivity
  let E := clusterInfiniteEvent d (origin d)
  have hEmeas : MeasurableSet E :=
    measurableSet_clusterInfiniteEvent (origin d)
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI : Infinite (Multiplicative (Site d)) := by infer_instance
  obtain ⟨g, hgfar, hcorr⟩ := fmu_genMixing_event_exists_not_mem
    hti hmix E hEmeas (originShiftBox d R) tolerance htolerance
  let x : Site d := g⁻¹ • origin d
  have hxfar : x ∉ box d R :=
    inverse_smul_origin_not_mem_box_of_not_mem_originShiftBox g hgfar
  refine ⟨x, hxfar, ?_⟩
  have hEmass : (rho : Measure (ConfigSpace (Sym2 (Site d)))).real E = theta := rfl
  have hshift :
      (shift g : ConfigSpace (Sym2 (Site d)) →
        ConfigSpace (Sym2 (Site d))) ⁻¹' E =
        clusterInfiniteEvent d x := by
    simpa [E, x] using
      (shift_preimage_clusterInfiniteEvent (d := d) g x)
  have hcorrLower : epsilon ≤
      (rho : Measure (ConfigSpace (Sym2 (Site d)))).real
        (E ∩ (shift g) ⁻¹' E) := by
    have habs := (abs_lt.mp hcorr).1
    rw [hEmass] at habs
    dsimp [epsilon, tolerance] at habs ⊢
    nlinarith [sq_pos_of_pos htheta']
  rw [hshift] at hcorrLower
  exact hcorrLower.trans
    (infinite_cluster_inter_le_twoPoint
      (rho : Measure (ConfigSpace (Sym2 (Site d)))) hunique (origin d) x)

end StatMech.FrontierB
