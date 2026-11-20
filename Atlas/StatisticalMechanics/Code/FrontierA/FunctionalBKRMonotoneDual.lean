/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.FunctionalBKRMonotoneReal
import Code.Inequalities.ReimerButterfly

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

private theorem sum_four_comm {A B C D R : Type*} [AddCommMonoid R]
    (sA : Finset A) (sB : Finset B) (sC : Finset C) (sD : Finset D)
    (f : A → B → C → D → R) :
    (Finset.sum sA fun a => Finset.sum sB fun b =>
      Finset.sum sC fun c => Finset.sum sD fun d => f a b c d) =
      Finset.sum sC fun c => Finset.sum sD fun d =>
        Finset.sum sA fun a => Finset.sum sB fun b => f a b c d := by
  calc
    (Finset.sum sA fun a => Finset.sum sB fun b =>
        Finset.sum sC fun c => Finset.sum sD fun d => f a b c d) =
        Finset.sum sA fun a => Finset.sum sC fun c =>
          Finset.sum sB fun b => Finset.sum sD fun d => f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = Finset.sum sC fun c => Finset.sum sA fun a =>
        Finset.sum sB fun b => Finset.sum sD fun d => f a b c d := by
      rw [Finset.sum_comm]
    _ = Finset.sum sC fun c => Finset.sum sA fun a =>
        Finset.sum sD fun d => Finset.sum sB fun b => f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = Finset.sum sC fun c => Finset.sum sD fun d =>
        Finset.sum sA fun a => Finset.sum sB fun b => f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

private theorem sum_three_comm {A B C R : Type*} [AddCommMonoid R]
    (sA : Finset A) (sB : Finset B) (sC : Finset C)
    (f : A → B → C → R) :
    (Finset.sum sA fun a => Finset.sum sB fun b =>
      Finset.sum sC fun c => f a b c) =
      Finset.sum sB fun b => Finset.sum sC fun c =>
        Finset.sum sA fun a => f a b c := by
  calc
    (Finset.sum sA fun a => Finset.sum sB fun b =>
        Finset.sum sC fun c => f a b c) =
        Finset.sum sB fun b => Finset.sum sA fun a =>
          Finset.sum sC fun c => f a b c := by
      rw [Finset.sum_comm]
    _ = Finset.sum sB fun b => Finset.sum sC fun c =>
        Finset.sum sA fun a => f a b c := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]



noncomputable def dualWprob (phi : E → Bool → ℝ)
    (C : Set (ConfigSpace E × ConfigSpace E)) : ℝ :=
  ∑ omega : ConfigSpace E, ∑ eta : ConfigSpace E,
    C.indicator (fun _ => (1 : ℝ)) (omega, eta) *
      (pweight phi omega * pweight phi eta)


theorem dualWprob_mono {phi : E → Bool → ℝ} (hphi0 : ∀ e b, 0 ≤ phi e b)
    {C D : Set (ConfigSpace E × ConfigSpace E)} (hCD : C ⊆ D) :
    dualWprob phi C ≤ dualWprob phi D := by
  unfold dualWprob
  apply Finset.sum_le_sum
  intro omega _
  apply Finset.sum_le_sum
  intro eta _
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
  by_cases hC : (omega, eta) ∈ C
  · rw [Set.indicator_of_mem hC, Set.indicator_of_mem (hCD hC)]
  · rw [Set.indicator_of_notMem hC]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _



theorem dualWprob_prod (phi : E → Bool → ℝ)
    (A B : Set (ConfigSpace E)) :
    dualWprob phi (A ×ˢ B) = wprob phi A * wprob phi B := by
  unfold dualWprob wprob
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  apply Finset.sum_congr rfl
  intro eta _
  by_cases hA : omega ∈ A <;> by_cases hB : eta ∈ B <;>
    simp [Set.indicator, hA, hB]

omit [Fintype E] [DecidableEq E] in


theorem dualDisjointOccurrence_subset_prod (A B : Set (ConfigSpace E)) :
    dualDisjointOccurrence A B ⊆ A ×ˢ B := by
  rintro ⟨omega, eta⟩ ⟨K, L, hKL, hA, hB⟩
  exact ⟨hA omega (agreeOn_refl K omega),
    hB eta (agreeOn_refl L eta)⟩




theorem dualBKR_wprob_increasing (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
  calc
    dualWprob phi (dualDisjointOccurrence A B) ≤
        dualWprob phi (A ×ˢ B) :=
      dualWprob_mono hphi0 (dualDisjointOccurrence_subset_prod A B)
    _ = wprob phi A * wprob phi B := dualWprob_prod phi A B
    _ ≤ wprob phi (A ∩ B) := wprob_fkg_pos phi hphi0 hphi1 hA hB

private theorem dual_sum_range_indicator_eq {m M : ℕ} (hm : m ≤ M) :
    (∑ k ∈ Finset.range M, if k < m then (1 : ℝ) else 0) = m := by
  rw [Finset.sum_boole]
  have hfilter : (Finset.range M).filter (fun k => k < m) = Finset.range m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]


def dualProductExpectation (phi : E → Bool → ℝ)
    (f : ConfigSpace E × ConfigSpace E → ℝ) : ℝ :=
  ∑ omega : ConfigSpace E, ∑ eta : ConfigSpace E,
    pweight phi omega * pweight phi eta * f (omega, eta)



theorem cylinderMinNat_mul_le_dualLevelBoxes (F G : ConfigSpace E → ℕ)
    (K L : Set E) (hKL : Disjoint K L) (omega eta : ConfigSpace E) :
    (cylinderMinNat F K omega : ℝ) * cylinderMinNat G L eta ≤
      ∑ k ∈ Finset.range (natFunctionBound F),
        ∑ l ∈ Finset.range (natFunctionBound G),
          (dualDisjointOccurrence (natUpperLevel F k) (natUpperLevel G l)).indicator
            (fun _ => (1 : ℝ)) (omega, eta) := by
  let m := cylinderMinNat F K omega
  let n := cylinderMinNat G L eta
  have hm : m ≤ natFunctionBound F :=
    (cylinderMinNat_le_self F K omega).trans
      (Nat.le_of_lt (lt_natFunctionBound F omega))
  have hn : n ≤ natFunctionBound G :=
    (cylinderMinNat_le_self G L eta).trans
      (Nat.le_of_lt (lt_natFunctionBound G eta))
  have hmLayer := dual_sum_range_indicator_eq (m := m) hm
  have hnLayer := dual_sum_range_indicator_eq (m := n) hn
  rw [← hmLayer, ← hnLayer, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  by_cases hkm : k < m <;> by_cases hln : l < n
  · have hoccF : OccursOn (natUpperLevel F k) K omega :=
      (occursOn_natUpperLevel_iff F k K omega).mpr hkm
    have hoccG : OccursOn (natUpperLevel G l) L eta :=
      (occursOn_natUpperLevel_iff G l L eta).mpr hln
    have hdual : (omega, eta) ∈
        dualDisjointOccurrence (natUpperLevel F k) (natUpperLevel G l) :=
      ⟨K, L, hKL, hoccF, hoccG⟩
    simp [hkm, hln, hdual]
  · simp only [if_pos hkm, if_neg hln, mul_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · simp only [if_neg hkm, zero_mul]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · simp only [if_neg hkm, zero_mul]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _


theorem functionalDisjointMaxAt_natAsReal_le_dualLevels
    (F G : ConfigSpace E → ℕ) (omega eta : ConfigSpace E) :
    functionalDisjointMaxAt (natAsReal F) (natAsReal G) omega eta ≤
      ∑ k ∈ Finset.range (natFunctionBound F),
        ∑ l ∈ Finset.range (natFunctionBound G),
          (dualDisjointOccurrence (natUpperLevel F k) (natUpperLevel G l)).indicator
            (fun _ => (1 : ℝ)) (omega, eta) := by
  unfold functionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  rw [cylinderMin_natAsReal, cylinderMin_natAsReal]
  exact cylinderMinNat_mul_le_dualLevelBoxes F G pair.1 pair.2
    (mem_disjointCoordinatePairs.mp hpair) omega eta



theorem productExpectation_natAsReal_mul_eq_levelIntersections
    (phi : E → Bool → ℝ) (F G : ConfigSpace E → ℕ) :
    productExpectation phi (fun omega => natAsReal F omega * natAsReal G omega) =
      ∑ k ∈ Finset.range (natFunctionBound F),
        ∑ l ∈ Finset.range (natFunctionBound G),
          wprob phi (natUpperLevel F k ∩ natUpperLevel G l) := by
  unfold productExpectation natAsReal wprob
  have hFlevel : ∀ omega : ConfigSpace E,
      (F omega : ℝ) = ∑ k ∈ Finset.range (natFunctionBound F),
        if k < F omega then (1 : ℝ) else 0 := by
    intro omega
    symm
    exact dual_sum_range_indicator_eq (Nat.le_of_lt (lt_natFunctionBound F omega))
  have hGlevel : ∀ omega : ConfigSpace E,
      (G omega : ℝ) = ∑ l ∈ Finset.range (natFunctionBound G),
        if l < G omega then (1 : ℝ) else 0 := by
    intro omega
    symm
    exact dual_sum_range_indicator_eq (Nat.le_of_lt (lt_natFunctionBound G omega))
  simp_rw [hFlevel, hGlevel, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hF : k < F omega <;> by_cases hG : l < G omega <;>
    simp [natUpperLevel, Set.indicator, hF, hG]


theorem dualFunctionalBKR_monotone_nat (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (F G : ConfigSpace E → ℕ) (hF : Monotone F) (hG : Monotone G) :
    dualProductExpectation phi
        (fun pair => functionalDisjointMaxAt (natAsReal F) (natAsReal G)
          pair.1 pair.2) ≤
      productExpectation phi (fun omega => natAsReal F omega * natAsReal G omega) := by
  calc
    dualProductExpectation phi
        (fun pair => functionalDisjointMaxAt (natAsReal F) (natAsReal G)
          pair.1 pair.2) ≤
        ∑ omega : ConfigSpace E, ∑ eta : ConfigSpace E,
          pweight phi omega * pweight phi eta *
            (∑ k ∈ Finset.range (natFunctionBound F),
              ∑ l ∈ Finset.range (natFunctionBound G),
                (dualDisjointOccurrence (natUpperLevel F k) (natUpperLevel G l)).indicator
                  (fun _ => (1 : ℝ)) (omega, eta)) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      exact mul_le_mul_of_nonneg_left
        (functionalDisjointMaxAt_natAsReal_le_dualLevels F G omega eta)
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
    _ = ∑ k ∈ Finset.range (natFunctionBound F),
          ∑ l ∈ Finset.range (natFunctionBound G),
            dualWprob phi
              (dualDisjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) := by
      simp_rw [Finset.mul_sum]
      rw [sum_four_comm (Finset.univ : Finset (ConfigSpace E))
        (Finset.univ : Finset (ConfigSpace E))
        (Finset.range (natFunctionBound F))
        (Finset.range (natFunctionBound G))]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      unfold dualWprob
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro eta _
      ring
    _ ≤ ∑ k ∈ Finset.range (natFunctionBound F),
          ∑ l ∈ Finset.range (natFunctionBound G),
            wprob phi (natUpperLevel F k ∩ natUpperLevel G l) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact dualBKR_wprob_increasing phi hphi0 hphi1
        (natUpperLevel_isIncreasing hF k) (natUpperLevel_isIncreasing hG l)
    _ = productExpectation phi
          (fun omega => natAsReal F omega * natAsReal G omega) :=
      (productExpectation_natAsReal_mul_eq_levelIntersections phi F G).symm




theorem cylinderMin_mul_le_dualRealLevelBoxes {f g : ConfigSpace E → ℝ}
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega)
    (K L : Set E) (hKL : Disjoint K L) (omega eta : ConfigSpace E) :
    cylinderMin f K omega * cylinderMin g L eta ≤
      ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
        layerF.2 * layerG.2 *
          (dualDisjointOccurrence (realUpperLevel f layerF.1)
            (realUpperLevel g layerG.1)).indicator
              (fun _ => (1 : ℝ)) (omega, eta) := by
  rw [cylinderMin_eq_layer_sum hf0, cylinderMin_eq_layer_sum hg0,
    Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro layerF hlayerF
  apply Finset.sum_le_sum
  intro layerG hlayerG
  by_cases hF : layerF.1 ≤ cylinderMin f K omega <;>
    by_cases hG : layerG.1 ≤ cylinderMin g L eta
  · have hoccF : OccursOn (realUpperLevel f layerF.1) K omega :=
      (occursOn_realUpperLevel_iff f layerF.1 K omega).mpr hF
    have hoccG : OccursOn (realUpperLevel g layerG.1) L eta :=
      (occursOn_realUpperLevel_iff g layerG.1 L eta).mpr hG
    have hdual : (omega, eta) ∈
        dualDisjointOccurrence (realUpperLevel f layerF.1)
          (realUpperLevel g layerG.1) := ⟨K, L, hKL, hoccF, hoccG⟩
    simp [hF, hG, hdual]
  · simp only [if_pos hF, if_neg hG, mul_zero]
    exact mul_nonneg
      (mul_nonneg (realLayer_increment_nonneg hf0 hlayerF)
        (realLayer_increment_nonneg hg0 hlayerG))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · simp only [if_neg hF, zero_mul]
    exact mul_nonneg
      (mul_nonneg (realLayer_increment_nonneg hf0 hlayerF)
        (realLayer_increment_nonneg hg0 hlayerG))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · simp only [if_neg hF, zero_mul]
    exact mul_nonneg
      (mul_nonneg (realLayer_increment_nonneg hf0 hlayerF)
        (realLayer_increment_nonneg hg0 hlayerG))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)


theorem functionalDisjointMaxAt_real_le_dualLevels {f g : ConfigSpace E → ℝ}
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega)
    (omega eta : ConfigSpace E) :
    functionalDisjointMaxAt f g omega eta ≤
      ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
        layerF.2 * layerG.2 *
          (dualDisjointOccurrence (realUpperLevel f layerF.1)
            (realUpperLevel g layerG.1)).indicator
              (fun _ => (1 : ℝ)) (omega, eta) := by
  unfold functionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  exact cylinderMin_mul_le_dualRealLevelBoxes hf0 hg0 pair.1 pair.2
    (mem_disjointCoordinatePairs.mp hpair) omega eta



theorem productExpectation_real_mul_eq_levelIntersections
    (phi : E → Bool → ℝ) {f g : ConfigSpace E → ℝ}
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega) :
    productExpectation phi (fun omega => f omega * g omega) =
      ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
        layerF.2 * layerG.2 *
          wprob phi (realUpperLevel f layerF.1 ∩ realUpperLevel g layerG.1) := by
  unfold productExpectation wprob
  simp_rw [real_value_eq_layer_sum hf0, real_value_eq_layer_sum hg0,
    Finset.sum_mul_sum, Finset.mul_sum]
  rw [sum_three_comm (Finset.univ : Finset (ConfigSpace E))
    (realLayerSet f) (realLayerSet g)]
  apply Finset.sum_congr rfl
  intro layerF _
  apply Finset.sum_congr rfl
  intro layerG _
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hF : omega ∈ realUpperLevel f layerF.1
  · by_cases hG : omega ∈ realUpperLevel g layerG.1
    · simp [eventIndicator, Set.indicator, hF, hG]
      ring
    · simp [eventIndicator, Set.indicator, hF, hG]
  · by_cases hG : omega ∈ realUpperLevel g layerG.1 <;>
      simp [eventIndicator, Set.indicator, hF, hG]



theorem dualFunctionalBKR_monotone_real (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (f g : ConfigSpace E → ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega)
    (hf : Monotone f) (hg : Monotone g) :
    dualProductExpectation phi
        (fun pair => functionalDisjointMaxAt f g pair.1 pair.2) ≤
      productExpectation phi (fun omega => f omega * g omega) := by
  calc
    dualProductExpectation phi
        (fun pair => functionalDisjointMaxAt f g pair.1 pair.2) ≤
        ∑ omega : ConfigSpace E, ∑ eta : ConfigSpace E,
          pweight phi omega * pweight phi eta *
            (∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
              layerF.2 * layerG.2 *
                (dualDisjointOccurrence (realUpperLevel f layerF.1)
                  (realUpperLevel g layerG.1)).indicator
                    (fun _ => (1 : ℝ)) (omega, eta)) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      exact mul_le_mul_of_nonneg_left
        (functionalDisjointMaxAt_real_le_dualLevels hf0 hg0 omega eta)
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
    _ = ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
          layerF.2 * layerG.2 *
            dualWprob phi
              (dualDisjointOccurrence (realUpperLevel f layerF.1)
                (realUpperLevel g layerG.1)) := by
      simp_rw [Finset.mul_sum]
      rw [sum_four_comm (Finset.univ : Finset (ConfigSpace E))
        (Finset.univ : Finset (ConfigSpace E))
        (realLayerSet f) (realLayerSet g)]
      apply Finset.sum_congr rfl
      intro layerF _
      apply Finset.sum_congr rfl
      intro layerG _
      unfold dualWprob
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro omega _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro eta _
      ring
    _ ≤ ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
          layerF.2 * layerG.2 *
            wprob phi
              (realUpperLevel f layerF.1 ∩ realUpperLevel g layerG.1) := by
      apply Finset.sum_le_sum
      intro layerF hlayerF
      apply Finset.sum_le_sum
      intro layerG hlayerG
      apply mul_le_mul_of_nonneg_left
      · exact dualBKR_wprob_increasing phi hphi0 hphi1
          (realUpperLevel_isIncreasing hf layerF.1)
          (realUpperLevel_isIncreasing hg layerG.1)
      · exact mul_nonneg (realLayer_increment_nonneg hf0 hlayerF)
          (realLayer_increment_nonneg hg0 hlayerG)
    _ = productExpectation phi (fun omega => f omega * g omega) :=
      (productExpectation_real_mul_eq_levelIntersections phi hf0 hg0).symm

end StatMech.FrontierA
