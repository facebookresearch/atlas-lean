/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































































import Mathlib
import Code.Walls.bc91hcanonfree
import Code.Walls.bc85bootstrap
import Code.Walls.bc78mergedichotomy
import Code.Walls.bc75spanningtree
import Code.Walls.bc62coarseclose

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}














def bc92_GoodEvent (L R : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | bc73_SublatticeForest ω L R}






theorem bc92_count_on_good_event (L R : ℕ) {ω : ConfigSpace (Sym2 (Site d))}
    (hω : ω ∈ bc92_GoodEvent (d := d) L R) : bc73_SublatticeForest ω L R := hω




theorem bc92_coarseTcount_le_on_good_event (L R : ℕ) {ω : ConfigSpace (Sym2 (Site d))}
    (hω : ω ∈ bc92_GoodEvent (d := d) L R) :
    bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R :=
  bc73_covering ω L R (bc92_count_on_good_event L R hω)












theorem bc92_good_event_of_gnData (L R : ℕ) {ω : ConfigSpace (Sym2 (Site d))}
    (h : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
    ω ∈ bc92_GoodEvent (d := d) L R :=
  bc75_sublatticeForest_of_gnTrifData ω L R h




theorem bc92_good_event_of_noTrif (L R : ℕ) {ω : ConfigSpace (Sym2 (Site d))}
    (hno : bc61_coarseTrifFinset ω L R = ∅) : ω ∈ bc92_GoodEvent (d := d) L R :=
  bc73_sublatticeForest_of_noTrif ω L R hno












theorem bc92_measurableSet_coarseTrifFinset_eq (L R : ℕ) (T : Finset (Site d)) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | bc61_coarseTrifFinset ω L R = T} := by
  classical
  by_cases hTsub : T ⊆ boxFinsetBK d R
  · 
    
    have hset : {ω : ConfigSpace (Sym2 (Site d)) | bc61_coarseTrifFinset ω L R = T}
        = (⋂ y ∈ (boxFinsetBK d R).filter (fun y => y ∈ T),
              {ω | bc61_IsCoarseTrifurcation ω L y})
          ∩ (⋂ y ∈ (boxFinsetBK d R).filter (fun y => y ∉ T),
              {ω | bc61_IsCoarseTrifurcation ω L y}ᶜ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_filter,
        Set.mem_compl_iff]
      constructor
      · intro hEq
        refine ⟨?_, ?_⟩
        · intro y ⟨hyb, hyT⟩
          have : y ∈ bc61_coarseTrifFinset ω L R := hEq ▸ hyT
          exact (bc61_mem_coarseTrifFinset.mp this).2
        · intro y ⟨hyb, hyT⟩ hct
          have : y ∈ bc61_coarseTrifFinset ω L R := by
            rw [bc61_mem_coarseTrifFinset]
            exact ⟨(Set.Finite.mem_toFinset _).mp hyb, hct⟩
          exact hyT (hEq ▸ this)
      · rintro ⟨h1, h2⟩
        ext y
        rw [bc61_mem_coarseTrifFinset]
        constructor
        · rintro ⟨hyb, hct⟩
          by_contra hyT
          have hybF : y ∈ boxFinsetBK d R := (Set.Finite.mem_toFinset _).mpr hyb
          exact h2 y ⟨hybF, hyT⟩ hct
        · intro hyT
          have hyb : y ∈ box d R := (Set.Finite.mem_toFinset _).mp (hTsub hyT)
          exact ⟨hyb, h1 y ⟨hTsub hyT, hyT⟩⟩
    rw [hset]
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.biInter (Finset.countable_toSet _)
        (fun y _ => bc62_measurableSet_coarseTrif L y)
    · exact MeasurableSet.biInter (Finset.countable_toSet _)
        (fun y _ => (bc62_measurableSet_coarseTrif L y).compl)
  · 
    have hempty : {ω : ConfigSpace (Sym2 (Site d)) | bc61_coarseTrifFinset ω L R = T} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hEq
      apply hTsub
      intro y hyT
      have : y ∈ bc61_coarseTrifFinset ω L R := hEq ▸ hyT
      rw [bc61_coarseTrifFinset, Finset.mem_filter] at this
      exact this.1
    rw [hempty]; exact MeasurableSet.empty





theorem bc92_measurableSet_goodEvent (L R : ℕ) :
    MeasurableSet (bc92_GoodEvent (d := d) L R) := by
  classical
  
  have hset : bc92_GoodEvent (d := d) L R
      = ⋃ T ∈ (boxFinsetBK d R).powerset.filter
          (fun T => ∀ c : Fin d → Fin (2 * L + 1),
            (T.filter (fun y => bc73_resVec L y = c)).card ≤ boxSV_boundaryCard d R),
        {ω : ConfigSpace (Sym2 (Site d)) | bc61_coarseTrifFinset ω L R = T} := by
    ext ω
    simp only [bc92_GoodEvent, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_powerset, exists_prop]
    constructor
    · intro hforest
      refine ⟨bc61_coarseTrifFinset ω L R, ⟨?_, ?_⟩, rfl⟩
      · intro y hy; rw [bc61_coarseTrifFinset, Finset.mem_filter] at hy; exact hy.1
      · intro c
        have := hforest c
        rwa [bc73_fiber] at this
    · rintro ⟨T, ⟨hTsub, hTcount⟩, hEq⟩
      intro c
      rw [bc73_fiber, hEq]
      exact hTcount c
  rw [hset]
  exact MeasurableSet.biUnion (Finset.countable_toSet _)
    (fun T _ => bc92_measurableSet_coarseTrifFinset_eq L R T)





theorem bc92_good_event_ae_iff_forest_ae (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ) :
    (∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1) ↔
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) := by
  have hcompl_eq : ∀ R : ℕ,
      μ {ω | ¬ bc73_SublatticeForest ω L R} = μ (bc92_GoodEvent (d := d) L R)ᶜ := fun R => rfl
  have hms : ∀ R : ℕ, MeasurableSet (bc92_GoodEvent (d := d) L R) := fun R =>
    bc92_measurableSet_goodEvent L R
  constructor
  · intro h R
    rw [ae_iff, hcompl_eq R, prob_compl_eq_zero_iff (hms R)]
    exact h R
  · intro h R
    have hae := h R
    rw [ae_iff, hcompl_eq R] at hae
    exact (prob_compl_eq_zero_iff (hms R)).mp hae








theorem bc92_ae_count_of_good_event_ae (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hgood : ∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc85_dc_bootstrap μ hd L hinv
    ((bc92_good_event_ae_iff_forest_ae μ L).mp hgood) hexist






















theorem bc92_good_event_ae_of_dichotomy (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
    ∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1 :=
  (bc92_good_event_ae_iff_forest_ae μ L).mpr
    (bc78_ae_forest_of_dichotomy μ L hinv h0)















theorem bc92_good_event_ae_from_finiteEnergy_is_circular
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hexist : bc61_CoarseTrifExistence μ L) :
    
    ((∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1) →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) →
      ∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1) := by
  refine ⟨fun hgood => bc92_ae_count_of_good_event_ae μ hd L hinv hgood hexist, ?_⟩
  intro h0
  exact bc92_good_event_ae_of_dichotomy μ L hinv h0













theorem bc92_upperLines_N_top :
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc60_numInfiniteClusters_top





theorem bc92_upperLines_null_of_goal
    (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (htop : μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) :
    μ {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 := by
  refine measure_mono_null ?_ htop
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [hω]; exact bc60_numInfiniteClusters_top




































theorem bc92_status :
    
    (∀ (L R : ℕ) (ω : ConfigSpace (Sym2 (Site 2))), ω ∈ bc92_GoodEvent (d := 2) L R →
      bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ 2 * boxSV_boundaryCard 2 R) ∧
    
    (∀ (L R : ℕ) (ω : ConfigSpace (Sym2 (Site 2))), bc61_coarseTrifFinset ω L R = ∅ →
      ω ∈ bc92_GoodEvent (d := 2) L R) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      (∀ R : ℕ, μ (bc92_GoodEvent (d := 2) L R) = 1) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      (∀ R : ℕ, μ (bc92_GoodEvent (d := 2) L R) = 1) ↔
        (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 →
      ∀ R : ℕ, μ (bc92_GoodEvent (d := 2) L R) = 1) ∧
    
    (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L R ω hω; exact bc92_coarseTcount_le_on_good_event L R hω
  · intro L R ω hno; exact bc92_good_event_of_noTrif L R hno
  · intro μ _ L hinv hgood hexist
    exact bc92_ae_count_of_good_event_ae μ (by norm_num) L hinv hgood hexist
  · intro μ _ L; exact bc92_good_event_ae_iff_forest_ae μ L
  · intro μ _ L hinv h0; exact bc92_good_event_ae_of_dichotomy μ L hinv h0
  · exact bc92_upperLines_N_top

end StatMech.Walls
