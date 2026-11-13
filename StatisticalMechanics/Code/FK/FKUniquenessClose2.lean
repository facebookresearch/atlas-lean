/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.FK.FKUniquenessClose
import Code.FK.ComparisonHolley
import Code.FK.MonoBC
import Code.FK.IvProperties

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice









section FixedBC

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C : SimpleGraph V) [DecidableRel C.Adj]







theorem bcWeight_cross_p {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2)
    (hp2' : p2 < 1) (hle : p1 ≤ p2) (hq : 1 ≤ q) (a b : ConfigSpace (Sym2 V)) :
    bcWeight G C p1 q a * bcWeight G C p2 q b
      ≤ bcWeight G C p1 q (a ⊓ b) * bcWeight G C p2 q (a ⊔ b) := by
  
  set A1 := edgeProduct G p1 a with hA1
  set B1 := edgeProduct G p2 b with hB1
  set A2 := edgeProduct G p1 (a ⊓ b) with hA2
  set B2 := edgeProduct G p2 (a ⊔ b) with hB2
  
  have hedge : A1 * B1 ≤ A2 * B2 := edgeProduct_cross G hp1 hp1' hp2 hp2' hle a b
  
  have hclust : q ^ numClustersBC G C a * q ^ numClustersBC G C b
      ≤ q ^ numClustersBC G C (a ⊓ b) * q ^ numClustersBC G C (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    refine pow_le_pow_right₀ hq ?_
    exact mixed_supermodular_bc G C C (le_refl C) a b
  
  have hA1n : 0 ≤ A1 := (edgeProduct_pos G hp1 hp1' a).le
  have hB1n : 0 ≤ B1 := (edgeProduct_pos G hp2 hp2' b).le
  have hA2n : 0 ≤ A2 := (edgeProduct_pos G hp1 hp1' (a ⊓ b)).le
  have hB2n : 0 ≤ B2 := (edgeProduct_pos G hp2 hp2' (a ⊔ b)).le
  have hqa : (0 : ℝ) ≤ q ^ numClustersBC G C a := pow_nonneg (by linarith) _
  have hqb : (0 : ℝ) ≤ q ^ numClustersBC G C b := pow_nonneg (by linarith) _
  have hqab2 : (0 : ℝ) ≤ q ^ numClustersBC G C (a ⊓ b) := pow_nonneg (by linarith) _
  have hqab3 : (0 : ℝ) ≤ q ^ numClustersBC G C (a ⊔ b) := pow_nonneg (by linarith) _
  
  unfold bcWeight
  have e1 : A1 * q ^ numClustersBC G C a * (B1 * q ^ numClustersBC G C b)
      = (A1 * B1) * (q ^ numClustersBC G C a * q ^ numClustersBC G C b) := by ring
  have e2 : A2 * q ^ numClustersBC G C (a ⊓ b) * (B2 * q ^ numClustersBC G C (a ⊔ b))
      = (A2 * B2) * (q ^ numClustersBC G C (a ⊓ b) * q ^ numClustersBC G C (a ⊔ b)) := by ring
  rw [e1, e2]
  exact mul_le_mul hedge hclust (mul_nonneg hqa hqb) (mul_nonneg hA2n hB2n)






theorem bcProb_cross_p {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2)
    (hp2' : p2 < 1) (hle : p1 ≤ p2) (hq : 1 ≤ q) (a b : ConfigSpace (Sym2 V)) :
    bcProb G C p1 q a * bcProb G C p2 q b
      ≤ bcProb G C p1 q (a ⊓ b) * bcProb G C p2 q (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < bcZ G C p1 q := bcZ_pos G C hp1 hp1' hq0
  have hZ2 : 0 < bcZ G C p2 q := bcZ_pos G C hp2 hp2' hq0
  unfold bcProb
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
  exact bcWeight_cross_p G C hp1 hp1' hp2 hp2' hle hq a b









theorem bcProb_monotone_in_p {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hle : p1 ≤ p2) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p1 q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p2 q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun ω => bcProb_nonneg G C hp1 hp1' hq0 ω
  · exact fun ω => bcProb_nonneg G C hp2 hp2' hq0 ω
  · rw [bcProb_sum_eq_one G C hp1 hp1' hq0, bcProb_sum_eq_one G C hp2 hp2' hq0]
  · exact fun a b => bcProb_cross_p G C hp1 hp1' hp2 hp2' hle hq a b

end FixedBC









variable {d : ℕ}










theorem wiredFiniteMeasure_real_monotone_in_p (m : ℕ) {p1 p2 : ℝ}
    (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2) (hp2' : p2 < 1) (hle : p1 ≤ p2)
    {T : Set (ConfigSpace (Sym2 (boxVerts d m)))} (hT : IsIncreasing T)
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' T)) :
    (wiredFiniteMeasure d m hp1 hp1' (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' T)
      ≤ (wiredFiniteMeasure d m hp2 hp2' (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' T) := by
  
  rw [wiredFiniteMeasure_real_boxRestrictEvent m hp1 hp1' T hmeas,
    wiredFiniteMeasure_real_boxRestrictEvent m hp2 hp2' T hmeas]
  
  have hrw1 : ∀ ω, wiredFkProb (boxGraph d m) (boxBoundary d m) p1 2 ω
      = bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p1 2 ω :=
    fun ω => (bcProb_clique_eq_wiredFkProb (boxGraph d m) (boxBoundary d m) p1 2 ω).symm
  have hrw2 : ∀ ω, wiredFkProb (boxGraph d m) (boxBoundary d m) p2 2 ω
      = bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p2 2 ω :=
    fun ω => (bcProb_clique_eq_wiredFkProb (boxGraph d m) (boxBoundary d m) p2 2 ω).symm
  simp only [hrw1, hrw2]
  
  exact bcProb_monotone_in_p (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m))
    hp1 hp1' hp2 hp2' hle (by norm_num) hT











theorem wiredFiniteMeasure_real_monotone_in_p_inner (N m : ℕ) (hNm : N ≤ m) {p1 p2 : ℝ}
    (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2) (hp2' : p2 < 1) (hle : p1 ≤ p2)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (wiredFiniteMeasure d m hp1 hp1' (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredFiniteMeasure d m hp2 hp2' (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq]
  exact wiredFiniteMeasure_real_monotone_in_p m hp1 hp1' hp2 hp2' hle hTinc hmeas



















theorem wiredEdgeDensity_q2_monotoneOn (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    MonotoneOn (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) := by
  intro p1 hp1mem p2 hp2mem hle
  obtain ⟨hp1, hp1'⟩ := hp1mem
  obtain ⟨hp2, hp2'⟩ := hp2mem
  
  have hTinc : IsIncreasing (boxEdgeOpenEvent d N eb) := boxEdgeOpenEvent_isIncreasing d N eb
  
  have htend1 := wiredEdgeDensity_q2_tendsto d N eb hp1 hp1'
  have htend2 := wiredEdgeDensity_q2_tendsto d N eb hp2 hp2'
  
  have hmono : ∀ᶠ m in atTop,
      (wiredFiniteMeasure d m hp1 hp1' (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
        ≤ (wiredFiniteMeasure d m hp2 hp2' (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
    filter_upwards [Filter.eventually_ge_atTop N] with m hNm
    exact wiredFiniteMeasure_real_monotone_in_p_inner N m hNm hp1 hp1' hp2 hp2' hle hTinc
  
  exact le_of_tendsto_of_tendsto htend1 htend2 hmono













theorem countable_density_ne_Ioo (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (heq_at_cont : ∀ p ∈ Ioo (0 : ℝ) 1,
      ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p →
        freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p) :
    {p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧ freeEdgeDensity d 2 (edgeIncl d N eb) p
        ≠ wiredEdgeDensity d 2 (edgeIncl d N eb) p}.Countable := by
  have hmono := wiredEdgeDensity_q2_monotoneOn d N eb
  refine (hmono.countable_not_continuousWithinAt).mono ?_
  intro p hp
  simp only [mem_setOf_eq] at hp ⊢
  obtain ⟨hpmem, hne⟩ := hp
  exact ⟨hpmem, fun hcont => hne (heq_at_cont p hpmem hcont)⟩



































theorem fk_uniqueness_off_countable_q2_no_hb (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (heq_at_cont : ∀ p ∈ Ioo (0 : ℝ) 1,
      ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p →
        freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1)
        (phi : Measure (ConfigSpace (Sym2 (Site d)))),
        ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real
              (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
          ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
              ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) →
        phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
            = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
          ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
              = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
  
  refine ⟨{p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧ freeEdgeDensity d 2 (edgeIncl d N eb) p
      ≠ wiredEdgeDensity d 2 (edgeIncl d N eb) p},
    countable_density_ne_Ioo d N eb heq_at_cont, ?_⟩
  intro p hp hp0 hp1 phi hsand
  
  have hdens : freeEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb) p := by
    by_contra hne
    exact hp ⟨⟨hp0, hp1⟩, hne⟩
  
  have hfw := hcrit_edgeOpenEvent_q2 d N eb hp0 hp1 hdens
  
  exact dlr_sandwich_unique hsand hfw

end FK

end StatMech
