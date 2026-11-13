/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Code.FK.FKUniquenessClose2
import Code.FK.WiredDomChain
import Code.FK.MonotoneWeakLimit
import Code.FK.TailLimit
import Code.FK.BoxTailLimit
import Code.FK.PcNontrivial

open MeasureTheory Filter Topology
open scoped BigOperators NNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}






















theorem tzp_fkTheta_iv_monotone_boxBdry (n : ℕ) {p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1) (hle : p₁ ≤ p₂) :
    (wiredInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  
  set S : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {ω' : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω' (IsingFK.boxOrigin d n)} with hS
  have hSinc : IsIncreasing S := isIncreasing_connToBdryEvent n
  have hEvent : boxBdryConnEvent d n = boxRestrict d n ⁻¹' S := rfl
  
  have htend₁ := fk_wired_infinite_measure n hp₁ hp₁' hSinc
  have htend₂ := fk_wired_infinite_measure n hp₂ hp₂' hSinc
  
  have hmono : ∀ᶠ m in atTop,
      (wiredFiniteMeasure d m hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
        ≤ (wiredFiniteMeasure d m hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hnm
    exact wiredFiniteMeasure_real_monotone_in_p_inner n m hnm hp₁ hp₁' hp₂ hp₂' hle hSinc
  
  rw [hEvent]
  exact le_of_tendsto_of_tendsto htend₁ htend₂ hmono





















theorem tzp_fkTheta_monotone_in_p {p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1) (hle : p₁ ≤ p₂) :
    fkTheta d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2) (q := 2)
      ≤ fkTheta d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  
  have htend₁ := wiredIv_boxBdryConnEvent_tendsto (d := d) hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
  have htend₂ := wiredIv_boxBdryConnEvent_tendsto (d := d) hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
  
  have hmono : ∀ᶠ n in atTop,
      (wiredInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
        ≤ (wiredInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) :=
    Filter.Eventually.of_forall
      (fun n => tzp_fkTheta_iv_monotone_boxBdry n hp₁ hp₁' hp₂ hp₂' hle)
  
  exact le_of_tendsto_of_tendsto htend₁ htend₂ hmono




















theorem tzp_fkTheta_eq_zero_of_lt_pc {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpc : p < FK.fkPc d 2) :
    FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
  
  have hne : (FK.fkSubcriticalSet d 2).Nonempty := by
    rcases (FK.fkSubcriticalSet d 2).eq_empty_or_nonempty with hempty | hne
    · exfalso; rw [FK.fkPc, hempty, Real.sSup_empty] at hpc; linarith
    · exact hne
  
  obtain ⟨p', hp'mem, hpp'⟩ := exists_lt_of_lt_csSup hne hpc
  
  obtain ⟨hp'0, hp'1, _hq, hθ'⟩ := hp'mem
  
  have hmono : FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)
      ≤ FK.fkTheta d hp'0 hp'1 (by norm_num : (0 : ℝ) < 2) (q := 2) :=
    tzp_fkTheta_monotone_in_p hp hp1 hp'0 hp'1 hpp'.le
  
  refine le_antisymm ?_ (FK.fkTheta_nonneg d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
  calc FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)
      ≤ FK.fkTheta d hp'0 hp'1 (by norm_num : (0 : ℝ) < 2) (q := 2) := hmono
    _ = 0 := hθ'

























theorem tzp_fkTheta_eq_zero_of_le_pc_of_pc
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
    ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
  intro p hp hp1 hple
  rcases lt_or_eq_of_le hple with hlt | heq
  · exact tzp_fkTheta_eq_zero_of_lt_pc hp hp1 hlt
  · 
    subst heq
    exact hθpc hp hp1

end FK

end StatMech
