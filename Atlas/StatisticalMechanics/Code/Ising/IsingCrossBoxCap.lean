/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.Ising.FVConsistencyProve
import Code.Ising.GibbsExtreme
import Code.Ising.IsingFKGLayer
import Code.Ising.IsingPlusErgodicClose
import Code.FK.FKMixingUpperClose
import Code.FK.ErgodicExtremeUpgrade
import Code.Percolation.BurtonKeane

open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.FK
open StatMech.Percolation

variable {d : ℕ}











theorem icb_plus_box_monotone {N m : ℕ} (hNm : N ≤ m) (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) (hAinc : IsIncreasing A) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A
      ≤ (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A := by
  set g0 : ConfigSpace (Site d) → ℝ := A.indicator (fun _ => (1:ℝ)) with hg0
  have hcds := consistency_double_sum hNm (plusField d) β h g0
  have hpm_m : (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A
      = ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ * g0 (glue (plusField d) σ) := by
    rw [plusMeasure_coe, fvMeasure_real_eq (plusField d) m (bondFinsetTouch d m) β h hA]
  rw [hpm_m, ← hcds]
  have hterm : ∀ σ : {x // x ∈ box d m} → Bool,
      fvProb (plusField d) m (bondFinsetTouch d m) β h σ
        * ∑ τ : {x // x ∈ box d N} → Bool,
            fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * g0 (glue (glue (plusField d) σ) τ)
      ≤ fvProb (plusField d) m (bondFinsetTouch d m) β h σ
          * (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A := by
    intro σ
    apply mul_le_mul_of_nonneg_left _ (fvProb_nonneg _ _ _ _ _ _)
    have hinner : (∑ τ : {x // x ∈ box d N} → Bool,
            fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * g0 (glue (glue (plusField d) σ) τ))
        = (fvMeasure (glue (plusField d) σ) N (bondFinsetTouch d N) β h).real A := by
      rw [fvMeasure_real_eq (glue (plusField d) σ) N (bondFinsetTouch d N) β h hA]
    rw [hinner]
    have hdom := fvMeasure_le_plusField N (bondFinsetTouch d N) β h hβ hh (glue (plusField d) σ)
      A hA hAinc
    refine hdom.trans (le_of_eq ?_)
    rw [plusMeasure_coe]
  calc (∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * ∑ τ : {x // x ∈ box d N} → Bool,
                fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
                  * g0 (glue (glue (plusField d) σ) τ))
      ≤ ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A := by
        rw [← Finset.sum_mul, fvProb_sum_eq_one, one_mul]








theorem icb_multiOpen_glue_ovrBox_eq {N m : ℕ} (hNm : N ≤ m) (S : Finset (Site d))
    (hS : ∀ x ∈ S, x ∉ box d N)
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d N} → Bool) :
    (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) (ovrBox hNm σ τ))
      = (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ) := by
  have heq : ∀ x ∈ S, glue (plusField d) (ovrBox hNm σ τ) x = glue (plusField d) σ x :=
    fun x hx => glue_ovrBox_eq_off_box hNm (plusField d) σ τ (hS x hx)
  by_cases hmem : glue (plusField d) (ovrBox hNm σ τ) ∈ fmu_multiOpen S
  · have hmem' : glue (plusField d) σ ∈ fmu_multiOpen S := by
      intro x hx; rw [← heq x hx]; exact hmem x hx
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
  · have hmem' : glue (plusField d) σ ∉ fmu_multiOpen S := by
      intro hc; apply hmem; intro x hx; rw [heq x hx]; exact hc x hx
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']










theorem icb_box_cross_cap {N m : ℕ} (hNm : N ≤ m) (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) (hAinc : IsIncreasing A)
    (S : Finset (Site d)) (hS : ∀ x ∈ S, x ∉ box d N) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (A ∩ fmu_multiOpen S)
      ≤ (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A
        * (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen S) := by
  classical
  have hBmeas : MeasurableSet (fmu_multiOpen S) := fmu_multiOpen_measurable S
  have hcapmeas : MeasurableSet (A ∩ fmu_multiOpen S) := hA.inter hBmeas
  set g0 : ConfigSpace (Site d) → ℝ := (A ∩ fmu_multiOpen S).indicator (fun _ => (1:ℝ)) with hg0
  have hcds := consistency_double_sum hNm (plusField d) β h g0
  have hpm_cap : (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (A ∩ fmu_multiOpen S)
      = ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ * g0 (glue (plusField d) σ) := by
    rw [plusMeasure_coe, fvMeasure_real_eq (plusField d) m (bondFinsetTouch d m) β h hcapmeas]
  rw [hpm_cap, ← hcds]
  have hterm : ∀ σ : {x // x ∈ box d m} → Bool,
      fvProb (plusField d) m (bondFinsetTouch d m) β h σ
        * ∑ τ : {x // x ∈ box d N} → Bool,
            fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * g0 (glue (glue (plusField d) σ) τ)
      ≤ fvProb (plusField d) m (bondFinsetTouch d m) β h σ
          * ((plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A
              * (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ)) := by
    intro σ
    apply mul_le_mul_of_nonneg_left _ (fvProb_nonneg _ _ _ _ _ _)
    have hsplit : ∀ τ : {x // x ∈ box d N} → Bool,
        fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
            * g0 (glue (glue (plusField d) σ) τ)
        = ((fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ))
            * (fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * A.indicator (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ)) := by
      intro τ
      have hind : ∀ y : ConfigSpace (Site d),
          g0 y = A.indicator (fun _ => (1:ℝ)) y * (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) y := by
        intro y; rw [hg0]
        have := Set.inter_indicator_mul (s := A) (t := fmu_multiOpen S)
          (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) y
        simpa using this
      rw [hind, glue_glue_eq_glue_ovrBox hNm (plusField d) σ τ,
        icb_multiOpen_glue_ovrBox_eq hNm S hS σ τ,
        ← glue_glue_eq_glue_ovrBox hNm (plusField d) σ τ]
      ring
    rw [Finset.sum_congr rfl (fun τ _ => hsplit τ), ← Finset.mul_sum]
    rw [mul_comm ((plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A) _]
    apply mul_le_mul_of_nonneg_left _ (Set.indicator_nonneg (fun _ _ => by norm_num) _)
    have hinner : (∑ τ : {x // x ∈ box d N} → Bool,
            fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
              * A.indicator (fun _ => (1:ℝ)) (glue (glue (plusField d) σ) τ))
        = (fvMeasure (glue (plusField d) σ) N (bondFinsetTouch d N) β h).real A := by
      rw [fvMeasure_real_eq (glue (plusField d) σ) N (bondFinsetTouch d N) β h hA]
    rw [hinner]
    have hdom := fvMeasure_le_plusField N (bondFinsetTouch d N) β h hβ hh (glue (plusField d) σ)
      A hA hAinc
    refine hdom.trans (le_of_eq ?_); rw [plusMeasure_coe]
  calc (∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * ∑ τ : {x // x ∈ box d N} → Bool,
                fvProb (glue (plusField d) σ) N (bondFinsetTouch d N) β h τ
                  * g0 (glue (glue (plusField d) σ) τ))
      ≤ ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb (plusField d) m (bondFinsetTouch d m) β h σ
            * ((plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A
                * (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ)) :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A
          * (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen S) := by
        rw [show (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen S)
              = ∑ σ : {x // x ∈ box d m} → Bool,
                  fvProb (plusField d) m (bondFinsetTouch d m) β h σ
                    * (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ) from by
            rw [plusMeasure_coe, fvMeasure_real_eq (plusField d) m (bondFinsetTouch d m) β h hBmeas]]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro σ _; ring









noncomputable def icb_shiftVec {d : ℕ} (i₀ : Fin d) (R : ℤ) : Site d :=
  fun i => if i = i₀ then R else 0


theorem icb_inv_smul (i₀ : Fin d) (R : ℤ) (x : Site d) :
    ((Multiplicative.ofAdd (- icb_shiftVec i₀ R))⁻¹ • x) = x + icb_shiftVec i₀ R := by
  funext i
  rw [smul_site_apply]
  change Multiplicative.toAdd (Multiplicative.ofAdd (- icb_shiftVec i₀ R))⁻¹ i + x i
      = x i + icb_shiftVec i₀ R i
  rw [← ofAdd_neg, neg_neg, toAdd_ofAdd]
  ring



theorem icb_shifted_notMem_box (i₀ : Fin d) {N : ℕ} {R : ℤ} {x : Site d}
    (hR : (N : ℤ) + |x i₀| < R) :
    ((Multiplicative.ofAdd (- icb_shiftVec i₀ R))⁻¹ • x) ∉ box d N := by
  rw [icb_inv_smul]
  intro hmem
  have hi : ((x + icb_shiftVec i₀ R) i₀).natAbs ≤ N := hmem i₀
  have hcoord : (x + icb_shiftVec i₀ R) i₀ = x i₀ + R := by
    simp [Pi.add_apply, icb_shiftVec]
  rw [hcoord] at hi
  
  have hge : - x i₀ ≤ |x i₀| := neg_le_abs (x i₀)
  have hpos : 0 < x i₀ + R := by nlinarith [Nat.cast_nonneg (α := ℤ) N]
  have hnatabs : ((x i₀ + R).natAbs : ℤ) = x i₀ + R := by
    rw [Int.natAbs_of_nonneg (le_of_lt hpos)]
  have hiZ : ((x i₀ + R).natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hi
  rw [hnatabs] at hiZ
  nlinarith




theorem icb_exists_far_shift (hd : 1 ≤ d) (P : Finset (Finset (Site d))) (N : ℕ) :
    ∃ g : Multiplicative (Site d), ∀ T' ∈ P, ∀ x ∈ T',
      (g⁻¹ • x : Site d) ∉ box d N := by
  classical
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  
  set M : ℕ := P.sup (fun T => T.sup (fun x => (x i₀).natAbs)) with hM
  have hMbound : ∀ T' ∈ P, ∀ x ∈ T', |x i₀| ≤ (M : ℤ) := by
    intro T' hT' x hx
    have h1 : (x i₀).natAbs ≤ T'.sup (fun x => (x i₀).natAbs) :=
      Finset.le_sup (f := fun x => (x i₀).natAbs) hx
    have h2 : T'.sup (fun x => (x i₀).natAbs) ≤ M :=
      Finset.le_sup (f := fun T => T.sup (fun x => (x i₀).natAbs)) hT'
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1.trans h2
  set R : ℤ := (N : ℤ) + (M : ℤ) + 1 with hR
  refine ⟨Multiplicative.ofAdd (- icb_shiftVec i₀ R), fun T' hT' x hx => ?_⟩
  refine icb_shifted_notMem_box i₀ (N := N) (R := R) (x := x) ?_
  have := hMbound T' hT' x hx
  rw [hR]; linarith











theorem icb_plusState_upperDecay (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    fmu_UpperDecay (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) := by
  classical
  set μ := (plusState d β h : Measure (ConfigSpace (Site d))) with hμdef
  intro P δ hδ
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  
  have hconvNear : ∀ T : Finset (Site d),
      Tendsto (fun k => (plusMeasure d (φ k) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T)) atTop (𝓝 (μ.real (fmu_multiOpen T))) :=
    fun T => hconv.tendsto_real_of_isClopen (ipe_multiOpen_isClopen T)
  
  have hclose : ∀ T ∈ P, ∀ᶠ k in atTop,
      (plusMeasure d (φ k) β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T)
        ≤ μ.real (fmu_multiOpen T) + δ := by
    intro T _
    have := (hconvNear T).eventually (eventually_le_nhds (by linarith : μ.real (fmu_multiOpen T) < μ.real (fmu_multiOpen T) + δ))
    exact this
  have hallclose : ∀ᶠ k in atTop, ∀ T ∈ P,
      (plusMeasure d (φ k) β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T)
        ≤ μ.real (fmu_multiOpen T) + δ := by
    rw [Filter.eventually_all_finset P]; intro T hT; exact hclose T hT
  obtain ⟨K, hK⟩ := hallclose.exists
  set N₀ := φ K with hN₀
  
  obtain ⟨g, hg⟩ := icb_exists_far_shift hd P N₀
  refine ⟨g, fun T hT T' hT' => ?_⟩
  
  set S := T'.image (fun e => g⁻¹ • e) with hSdef
  have hShift : (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' fmu_multiOpen T'
      = fmu_multiOpen S := fmu_shift_multiOpen g T'
  have hSdisj : ∀ y ∈ S, y ∉ box d N₀ := by
    intro y hy
    rw [hSdef, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hg T' hT' x hx
  
  have hConvCross :
      Tendsto (fun k => (plusMeasure d (φ k) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T ∩ fmu_multiOpen S)) atTop
        (𝓝 (μ.real (fmu_multiOpen T ∩ fmu_multiOpen S))) :=
    hconv.tendsto_real_of_isClopen ((ipe_multiOpen_isClopen T).inter (ipe_multiOpen_isClopen S))
  have hConvFar : Tendsto (fun k => (plusMeasure d (φ k) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen S)) atTop (𝓝 (μ.real (fmu_multiOpen S))) := hconvNear S
  
  have hbound : ∀ᶠ k in atTop,
      (plusMeasure d (φ k) β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T ∩ fmu_multiOpen S)
        ≤ (plusMeasure d N₀ β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T)
          * (plusMeasure d (φ k) β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen S) := by
    have hev : ∀ᶠ k in atTop, N₀ ≤ φ k := by
      have : ∀ᶠ k in atTop, K ≤ k := eventually_ge_atTop K
      exact this.mono (fun k hk => by rw [hN₀]; exact hφ.monotone hk)
    refine hev.mono (fun k hk => ?_)
    exact icb_box_cross_cap hk β h hβ hh
      (IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T))
      (fmu_multiOpen_isIncreasing T) S hSdisj
  
  have hlimit : μ.real (fmu_multiOpen T ∩ fmu_multiOpen S)
      ≤ (plusMeasure d N₀ β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T)
        * μ.real (fmu_multiOpen S) :=
    le_of_tendsto_of_tendsto hConvCross (tendsto_const_nhds.mul hConvFar) hbound
  
  have hfarTI : μ.real (fmu_multiOpen S) = μ.real (fmu_multiOpen T') := by
    rw [← hShift]
    exact fmc_real_preimage_shift hti g (fmu_multiOpen_measurable T')
  
  have hN₀close : (plusMeasure d N₀ β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T)
      ≤ μ.real (fmu_multiOpen T) + δ := hK T hT
  have hfar_nonneg : 0 ≤ μ.real (fmu_multiOpen T') := measureReal_nonneg
  have hfar_le_one : μ.real (fmu_multiOpen T') ≤ 1 := by
    rw [hμdef]; exact measureReal_le_one
  rw [hfarTI] at hlimit
  rw [show (fmu_multiOpen T ∩
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' fmu_multiOpen T')
      = fmu_multiOpen T ∩ fmu_multiOpen S by rw [hShift]]
  calc μ.real (fmu_multiOpen T ∩ fmu_multiOpen S)
      ≤ (plusMeasure d N₀ β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T)
          * μ.real (fmu_multiOpen T') := hlimit
    _ ≤ (μ.real (fmu_multiOpen T) + δ) * μ.real (fmu_multiOpen T') :=
        mul_le_mul_of_nonneg_right hN₀close hfar_nonneg
    _ = μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T') + δ * μ.real (fmu_multiOpen T') := by
        ring
    _ ≤ μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T') + δ := by
        have : δ * μ.real (fmu_multiOpen T') ≤ δ * 1 :=
          mul_le_mul_of_nonneg_left hfar_le_one (le_of_lt hδ)
        rw [mul_one] at this; linarith










theorem icb_plusState_isErgodic (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  ipe_plusState_isErgodic_of_upperDecay hβ h hti (icb_plusState_upperDecay hd hβ hh hti)







theorem icb_plusState_isInvariantExtremePoint (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  ipe_plusState_isInvariantExtremePoint_of_upperDecay hβ h hti
    (icb_plusState_upperDecay hd hβ hh hti)

end Ising

end StatMech
