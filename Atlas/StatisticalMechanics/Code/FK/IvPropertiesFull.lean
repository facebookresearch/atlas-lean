/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.FK.FKG
import Code.FK.MonoBC
import Code.FK.FreeWeakLimit
import Code.FK.MonotoneWeakLimit
import Code.FK.WiredDomChain
import Code.FK.Limits
import Code.FK.InfiniteVolume
import Code.Lattice.BoundaryConditions
import Code.Inequalities.FKG
import Code.Foundations.StochasticDomination

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators
open StatMech.Lattice StatMech.IsingFK

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

variable {d : ℕ}




















theorem freeFiniteMeasure_fkg (N m : ℕ) (hNm : N ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
      * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
      ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  
  set T₁ := boxRestrictLE d hNm ⁻¹' S₁ with hT₁
  set T₂ := boxRestrictLE d hNm ⁻¹' S₂ with hT₂
  have hT₁inc : IsIncreasing T₁ := fun a b hab ha => hS₁ (boxRestrictLE_monotone d hNm hab) ha
  have hT₂inc : IsIncreasing T₂ := fun a b hab ha => hS₂ (boxRestrictLE_monotone d hNm hab) ha
  have heq₁ : boxRestrict d N ⁻¹' S₁ = boxRestrict d m ⁻¹' T₁ := by
    ext ω; simp only [hT₁, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have heq₂ : boxRestrict d N ⁻¹' S₂ = boxRestrict d m ⁻¹' T₂ := by
    ext ω; simp only [hT₂, Set.mem_preimage, boxRestrictLE_boxRestrict]
  
  have hmeas₁ : MeasurableSet (boxRestrict d m ⁻¹' T₁) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  have hmeas₂ : MeasurableSet (boxRestrict d m ⁻¹' T₂) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  have hmeascap : MeasurableSet (boxRestrict d m ⁻¹' (T₁ ∩ T₂)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq₁, heq₂, ← Set.preimage_inter,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) T₁ hmeas₁,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) T₂ hmeas₂,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) (T₁ ∩ T₂) hmeascap]
  
  have hfkg := fkProb_positively_associated_events (boxGraph d m) hp hp1
    (by norm_num : (1:ℝ) ≤ 2) hT₁inc hT₂inc
  calc (∑ ω, T₁.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d m) p 2 ω)
        * (∑ ω, T₂.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d m) p 2 ω)
      = (∑ ω, fkProb (boxGraph d m) p 2 ω * T₁.indicator (fun _ => (1:ℝ)) ω)
        * (∑ ω, fkProb (boxGraph d m) p 2 ω * T₂.indicator (fun _ => (1:ℝ)) ω) := by
        rw [Finset.sum_congr rfl (fun ω _ => mul_comm _ _),
          Finset.sum_congr rfl (fun ω _ => mul_comm (T₂.indicator _ ω) _)]
    _ ≤ ∑ ω, fkProb (boxGraph d m) p 2 ω * (T₁ ∩ T₂).indicator (fun _ => (1:ℝ)) ω := hfkg
    _ = ∑ ω, (T₁ ∩ T₂).indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d m) p 2 ω :=
        Finset.sum_congr rfl (fun ω _ => mul_comm _ _)






















theorem ivp_iv_fkg (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
      * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
      ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  
  
  have hcap : IsIncreasing (S₁ ∩ S₂) := hS₁.inter hS₂
  have heqcap : boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂
      = boxRestrict d N ⁻¹' (S₁ ∩ S₂) := (Set.preimage_inter).symm
  rw [heqcap]
  
  have hlim₁ := fk_free_infinite_measure N hp hp1 hS₁
  have hlim₂ := fk_free_infinite_measure N hp hp1 hS₂
  have hlimcap := fk_free_infinite_measure N hp hp1 hcap
  
  have hprod := hlim₁.mul hlim₂
  
  have heventually :
      ∀ᶠ m in atTop,
        (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
          * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
          ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (boxRestrict d N ⁻¹' (S₁ ∩ S₂)) := by
    filter_upwards [eventually_ge_atTop N] with m hNm
    have h := freeFiniteMeasure_fkg N m hNm hp hp1 hS₁ hS₂
    rwa [← Set.preimage_inter] at h
  exact le_of_tendsto_of_tendsto hprod hlimcap heventually









section Wired
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]




theorem wiredFkProb_eq_bcProb_clique (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q ω
      = bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω := by
  have hw : ∀ η, wiredFkWeight G bdry p q η
      = bcWeight G (StatMech.Lattice.boundaryCliqueGraph bdry) p q η := by
    intro η
    rw [wiredFkWeight, bcWeight, numClustersBC_boundaryClique]
  have hZ : wiredFkZ G bdry p q = bcZ G (StatMech.Lattice.boundaryCliqueGraph bdry) p q := by
    rw [wiredFkZ, bcZ]; exact Finset.sum_congr rfl (fun η _ => hw η)
  rw [wiredFkProb, bcProb, hw, hZ]





theorem wiredFkProb_FKGLatticeCondition {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FKGLatticeCondition (fun ω => wiredFkProb G bdry p q ω) := by
  intro a b
  simp only [wiredFkProb_eq_bcProb_clique]
  have hcross := bcProb_cross G (StatMech.Lattice.boundaryCliqueGraph bdry)
    (StatMech.Lattice.boundaryCliqueGraph bdry) le_rfl hp hp1 hq a b
  calc bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q a
        * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q b
      ≤ bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q (a ⊓ b)
          * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q (a ⊔ b) := hcross
    _ = bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q (a ⊔ b)
          * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q (a ⊓ b) := mul_comm _ _



theorem wiredFkProb_positively_associated_events {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A B : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (∑ ω, wiredFkProb G bdry p q ω * A.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, wiredFkProb G bdry p q ω * B.indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ ω, wiredFkProb G bdry p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact fkg_inequality_events
    (fun ω => wiredFkProb_nonneg G bdry hp hp1 hq0 ω)
    (wiredFkProb_sum_eq_one G bdry hp hp1 hq0)
    (wiredFkProb_FKGLatticeCondition G bdry hp hp1 hq) hA hB

end Wired













theorem wiredFiniteMeasure_fkg (N m : ℕ) (hNm : N ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
      * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  set T₁ := boxRestrictLE d hNm ⁻¹' S₁ with hT₁
  set T₂ := boxRestrictLE d hNm ⁻¹' S₂ with hT₂
  have hT₁inc : IsIncreasing T₁ := fun a b hab ha => hS₁ (boxRestrictLE_monotone d hNm hab) ha
  have hT₂inc : IsIncreasing T₂ := fun a b hab ha => hS₂ (boxRestrictLE_monotone d hNm hab) ha
  have heq₁ : boxRestrict d N ⁻¹' S₁ = boxRestrict d m ⁻¹' T₁ := by
    ext ω; simp only [hT₁, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have heq₂ : boxRestrict d N ⁻¹' S₂ = boxRestrict d m ⁻¹' T₂ := by
    ext ω; simp only [hT₂, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas₁ : MeasurableSet (boxRestrict d m ⁻¹' T₁) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  have hmeas₂ : MeasurableSet (boxRestrict d m ⁻¹' T₂) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  have hmeascap : MeasurableSet (boxRestrict d m ⁻¹' (T₁ ∩ T₂)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq₁, heq₂, ← Set.preimage_inter,
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 T₁ hmeas₁,
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 T₂ hmeas₂,
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 (T₁ ∩ T₂) hmeascap]
  have hfkg := wiredFkProb_positively_associated_events (boxGraph d m) (boxBoundary d m)
    hp hp1 (by norm_num : (1:ℝ) ≤ 2) hT₁inc hT₂inc
  calc (∑ ω, T₁.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω)
        * (∑ ω, T₂.indicator (fun _ => (1:ℝ)) ω
            * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω)
      = (∑ ω, wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω
            * T₁.indicator (fun _ => (1:ℝ)) ω)
        * (∑ ω, wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω
            * T₂.indicator (fun _ => (1:ℝ)) ω) := by
        rw [Finset.sum_congr rfl (fun ω _ => mul_comm _ _),
          Finset.sum_congr rfl (fun ω _ => mul_comm (T₂.indicator _ ω) _)]
    _ ≤ ∑ ω, wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω
          * (T₁ ∩ T₂).indicator (fun _ => (1:ℝ)) ω := hfkg
    _ = ∑ ω, (T₁ ∩ T₂).indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω :=
        Finset.sum_congr rfl (fun ω _ => mul_comm _ _)











theorem ivp_iv_fkg_wired (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
      * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  have hcap : IsIncreasing (S₁ ∩ S₂) := hS₁.inter hS₂
  have heqcap : boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂
      = boxRestrict d N ⁻¹' (S₁ ∩ S₂) := (Set.preimage_inter).symm
  rw [heqcap]
  have hlim₁ := fk_wired_infinite_measure N hp hp1 hS₁
  have hlim₂ := fk_wired_infinite_measure N hp hp1 hS₂
  have hlimcap := fk_wired_infinite_measure N hp hp1 hcap
  have hprod := hlim₁.mul hlim₂
  have heventually :
      ∀ᶠ m in atTop,
        (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
          * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
          ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (boxRestrict d N ⁻¹' (S₁ ∩ S₂)) := by
    filter_upwards [eventually_ge_atTop N] with m hNm
    have h := wiredFiniteMeasure_fkg N m hNm hp hp1 hS₁ hS₂
    rwa [← Set.preimage_inter] at h
  exact le_of_tendsto_of_tendsto hprod hlimcap heventually
































theorem ivp_iv_monotone (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  have hAinc : IsIncreasing (boxRestrict d N ⁻¹' S) :=
    fkFreeLimit_isIncreasing_preimage N hS
  have hAmeas : MeasurableSet (boxRestrict d N ⁻¹' S) :=
    fkFreeLimit_measurableSet_preimage N S
  
  have hfree := fk_free_infinite_measure N hp hp1 hS
  have hwired := fk_wired_infinite_measure N hp hp1 hS
  
  have heventually :
      ∀ᶠ m in atTop,
        (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
          ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
    filter_upwards with m
    have hdom := freeFiniteMeasure_dominated d m hp hp1 (by norm_num : (1:ℝ) ≤ 2)
      (boxRestrict d N ⁻¹' S) hAmeas hAinc
    
    exact hdom
  exact le_of_tendsto_of_tendsto hfree hwired heventually

end FK

end StatMech
