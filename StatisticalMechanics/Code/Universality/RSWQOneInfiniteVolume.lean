/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























import Code.Universality.RSWQOneMixedSquare
import Code.FK.WiredDomChain

open Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Lattice
open StatMech.FK
open StatMech.RSW.Box

variable {d : ℕ}





private theorem rq1_innerEdgeLE_mem_edgeFinset {N m : ℕ} (hNm : N ≤ m)
    (eb : Sym2 (boxVerts d N)) (heb : eb ∈ (boxGraph d N).edgeFinset) :
    innerEdgeLE d hNm eb ∈ (boxGraph d m).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset] at heb ⊢
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    rw [innerEdgeLE, Sym2.map_mk, SimpleGraph.mem_edgeSet, boxGraph,
      SimpleGraph.comap_adj]
    exact heb



theorem rq1_boxRestrictLE_event_dependsOn {N m : ℕ} (hNm : N ≤ m)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N))))
    (hS : _root_.DependsOn (S.indicator (fun _ => (1 : ℝ)))
      ((boxGraph d N).edgeFinset : Set (Sym2 (boxVerts d N)))) :
    _root_.DependsOn
      ((boxRestrictLE d hNm ⁻¹' S).indicator (fun _ => (1 : ℝ)))
      ((boxGraph d m).edgeFinset : Set (Sym2 (boxVerts d m))) := by
  intro eta eta' hagree
  apply hS
  intro eb heb
  exact hagree (innerEdgeLE d hNm eb)
    (rq1_innerEdgeLE_mem_edgeFinset hNm eb heb)





private theorem rq1_wiredFiniteMeasure_real_boxRestrictEvent (m : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d m))))
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (wiredFiniteMeasure d m hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S) =
      ∑ omega : ConfigSpace (Sym2 (boxVerts d m)),
        S.indicator (fun _ => (1 : ℝ)) omega *
          wiredFkProb (boxGraph d m) (boxBoundary d m) p q omega := by
  have hw : (wiredFiniteMeasure d m hp hp1 hq : Measure _).real
        (boxRestrict d m ⁻¹' S) =
      ((wiredFkPMF (boxGraph d m) (boxBoundary d m) hp hp1 hq).toMeasure
        (extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d m) hmeas]
  have hpre : extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S) = S := by
    ext omega
    simp only [Set.mem_preimage, boxRestrict_extendEdge]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d m hp hp1 hq]



theorem rq1_wiredFinite_graphCylinder_eq_bernoulli {N m : ℕ} (hNm : N ≤ m)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N))))
    (hS : _root_.DependsOn (S.indicator (fun _ => (1 : ℝ)))
      ((boxGraph d N).edgeFinset : Set (Sym2 (boxVerts d N)))) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 1) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) =
      (bernoulliProductMeasure (E := Sym2 (Site d))
        (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real
        (boxRestrict d N ⁻¹' S) := by
  let T : Set (ConfigSpace (Sym2 (boxVerts d m))) := boxRestrictLE d hNm ⁻¹' S
  have hTdep : _root_.DependsOn (T.indicator (fun _ => (1 : ℝ)))
      ((boxGraph d m).edgeFinset : Set (Sym2 (boxVerts d m))) := by
    exact rq1_boxRestrictLE_event_dependsOn hNm S hS
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [T, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent,
    rq1_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (by norm_num : (0 : ℝ) < 1) T hmeas]
  calc
    (∑ omega : ConfigSpace (Sym2 (boxVerts d m)),
        T.indicator (fun _ => (1 : ℝ)) omega *
          wiredFkProb (boxGraph d m) (boxBoundary d m) p 1 omega) =
        ∑ omega : ConfigSpace (Sym2 (boxVerts d m)),
          T.indicator (fun _ => (1 : ℝ)) omega *
            fkProb (boxGraph d m) p 1 omega := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [← bcProb_clique_eq_wiredFkProb,
        rq1_bcProb_one_eq_fkProb]
    _ = (bernoulliProductMeasure (E := Sym2 (boxVerts d m))
          (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real T :=
      fkProbOne_event_eq_bernoulli (boxGraph d m) hp hp1 T hTdep
    _ = (bernoulliProductMeasure (E := Sym2 (Site d))
          (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real
          (boxRestrict d m ⁻¹' T) :=
      (bernoulliProduct_boxRestrict_preimage
        (d := d) (⟨p, hp.le⟩ : ℝ≥0)
        (by exact_mod_cast hp1.le) m T).symm








theorem rq1_wiredInfiniteVolume_graphCylinder_eq_bernoulli (N : ℕ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N))))
    (hS : _root_.DependsOn (S.indicator (fun _ => (1 : ℝ)))
      ((boxGraph d N).edgeFinset : Set (Sym2 (boxVerts d N)))) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 1) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) =
      (bernoulliProductMeasure (E := Sym2 (Site d))
        (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    wiredInfiniteVolume_isLimit d hp hp1 (by norm_num : (0 : ℝ) < 1)
  have hlimit := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N S)
  have heq :
      (fun k => (wiredFiniteMeasure d (phi k) hp hp1
          (by norm_num : (0 : ℝ) < 1) :
            Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S)) =ᶠ[atTop]
        (fun _ => (bernoulliProductMeasure (E := Sym2 (Site d))
          (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real
          (boxRestrict d N ⁻¹' S)) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    exact rq1_wiredFinite_graphCylinder_eq_bernoulli
      (hk.trans (hphi.id_le k)) hp hp1 S hS
  have hconstant : Tendsto
      (fun k => (wiredFiniteMeasure d (phi k) hp hp1
          (by norm_num : (0 : ℝ) < 1) :
            Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S)) atTop
      (nhds ((bernoulliProductMeasure (E := Sym2 (Site d))
        (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real
        (boxRestrict d N ⁻¹' S))) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique hlimit hconstant





theorem rq1_wiredInfiniteVolume_centeredSquare_eq (n : ℕ) :
    (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
  rw [← rq1_finiteMixedSquareEvent_preimage n]
  have h := rq1_wiredInfiniteVolume_graphCylinder_eq_bernoulli
    (d := 2) n (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)
    (rq1_finiteMixedSquareEvent n) (rq1_finiteMixedSquareEvent_dependsOn n)
  simpa [rba_selfDualMeasure] using h



theorem rq1_wiredInfiniteVolume_centeredSquare_half (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤
      (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
  rw [rq1_wiredInfiniteVolume_centeredSquare_eq]
  exact rq1_centeredSquare_crossing_half n hn

end Universality
end StatMech
