/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.FunctionalBKRFinite
import Code.Inequalities.BK

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


def natAsReal (F : ConfigSpace E -> ℕ) : ConfigSpace E -> ℝ :=
  fun omega => F omega


def natUpperLevel (F : ConfigSpace E -> ℕ) (k : ℕ) : Set (ConfigSpace E) :=
  {omega | k < F omega}

omit [Fintype E] [DecidableEq E] in

theorem natUpperLevel_isIncreasing {F : ConfigSpace E -> ℕ} (hF : Monotone F) (k : ℕ) :
    IsIncreasing (natUpperLevel F k) := by
  intro omega eta homega hlevel
  exact lt_of_lt_of_le hlevel (hF homega)


noncomputable def natFunctionBound (F : ConfigSpace E -> ℕ) : ℕ :=
  (Finset.univ.sup' Finset.univ_nonempty F) + 1

theorem lt_natFunctionBound (F : ConfigSpace E -> ℕ) (omega : ConfigSpace E) :
    F omega < natFunctionBound F := by
  unfold natFunctionBound
  exact Nat.lt_succ_of_le (Finset.le_sup' F (Finset.mem_univ omega))


noncomputable def cylinderMinNat (F : ConfigSpace E -> ℕ) (K : Set E)
    (omega : ConfigSpace E) : ℕ :=
  (agreementFiber K omega).inf' (agreementFiber_nonempty K omega) F


theorem cylinderMin_natAsReal (F : ConfigSpace E -> ℕ) (K : Set E)
    (omega : ConfigSpace E) :
    cylinderMin (natAsReal F) K omega = cylinderMinNat F K omega := by
  unfold cylinderMin cylinderMinNat natAsReal
  symm
  exact Finset.comp_inf'_eq_inf'_comp (agreementFiber_nonempty K omega)
    (fun n : ℕ => (n : ℝ)) (fun x y => by simp)



theorem occursOn_natUpperLevel_iff (F : ConfigSpace E -> ℕ) (k : ℕ)
    (K : Set E) (omega : ConfigSpace E) :
    OccursOn (natUpperLevel F k) K omega ↔ k < cylinderMinNat F K omega := by
  unfold OccursOn natUpperLevel cylinderMinNat
  rw [Finset.lt_inf'_iff]
  constructor
  · intro h eta heta
    exact h eta (mem_agreementFiber.mp heta)
  · intro h eta hagree
    exact h eta (mem_agreementFiber.mpr hagree)


theorem cylinderMinNat_le_self (F : ConfigSpace E -> ℕ) (K : Set E)
    (omega : ConfigSpace E) : cylinderMinNat F K omega ≤ F omega := by
  unfold cylinderMinNat
  exact Finset.inf'_le _ (mem_agreementFiber.mpr (agreeOn_refl K omega))

private theorem sum_range_indicator_eq {m M : ℕ} (hm : m ≤ M) :
    (∑ k ∈ Finset.range M, if k < m then (1 : ℝ) else 0) = m := by
  rw [Finset.sum_boole]
  have hfilter : (Finset.range M).filter (fun k => k < m) = Finset.range m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]



theorem cylinderMinNat_mul_le_levelBoxes (F G : ConfigSpace E -> ℕ)
    (K L : Set E) (hKL : Disjoint K L) (omega : ConfigSpace E) :
    (cylinderMinNat F K omega : ℝ) * cylinderMinNat G L omega ≤
      ∑ k ∈ Finset.range (natFunctionBound F),
        ∑ l ∈ Finset.range (natFunctionBound G),
          eventIndicator (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) omega := by
  let m := cylinderMinNat F K omega
  let n := cylinderMinNat G L omega
  have hm : m ≤ natFunctionBound F := by
    exact (cylinderMinNat_le_self F K omega).trans
      (Nat.le_of_lt (lt_natFunctionBound F omega))
  have hn : n ≤ natFunctionBound G := by
    exact (cylinderMinNat_le_self G L omega).trans
      (Nat.le_of_lt (lt_natFunctionBound G omega))
  have hmLayer := sum_range_indicator_eq (m := m) hm
  have hnLayer := sum_range_indicator_eq (m := n) hn
  rw [← hmLayer, ← hnLayer, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  by_cases hkm : k < m <;> by_cases hln : l < n
  · have hoccF : OccursOn (natUpperLevel F k) K omega :=
      (occursOn_natUpperLevel_iff F k K omega).mpr hkm
    have hoccG : OccursOn (natUpperLevel G l) L omega :=
      (occursOn_natUpperLevel_iff G l L omega).mpr hln
    have hbox : omega ∈ disjointOccurrence (natUpperLevel F k) (natUpperLevel G l) :=
      ⟨K, L, hKL, hoccF, hoccG⟩
    simp [eventIndicator, hkm, hln, hbox]
  · simp only [if_pos hkm, if_neg hln, mul_zero]
    unfold eventIndicator
    exact Set.indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) _
  · simp only [if_neg hkm, zero_mul]
    unfold eventIndicator
    exact Set.indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) _
  · simp only [if_neg hkm, zero_mul]
    unfold eventIndicator
    exact Set.indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) _


theorem functionalDisjointMax_natAsReal_le (F G : ConfigSpace E -> ℕ)
    (omega : ConfigSpace E) :
    functionalDisjointMax (natAsReal F) (natAsReal G) omega ≤
      ∑ k ∈ Finset.range (natFunctionBound F),
        ∑ l ∈ Finset.range (natFunctionBound G),
          eventIndicator (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) omega := by
  unfold functionalDisjointMax functionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  rw [cylinderMin_natAsReal, cylinderMin_natAsReal]
  exact cylinderMinNat_mul_le_levelBoxes F G pair.1 pair.2
    (mem_disjointCoordinatePairs.mp hpair) omega


def productExpectation (phi : E -> Bool -> ℝ) (f : ConfigSpace E -> ℝ) : ℝ :=
  ∑ omega : ConfigSpace E, pweight phi omega * f omega


theorem productExpectation_natAsReal_eq_levels (phi : E -> Bool -> ℝ)
    (F : ConfigSpace E -> ℕ) :
    productExpectation phi (natAsReal F) =
      ∑ k ∈ Finset.range (natFunctionBound F), wprob phi (natUpperLevel F k) := by
  unfold productExpectation wprob natAsReal
  have hlayer : ∀ omega : ConfigSpace E,
      (F omega : ℝ) =
        ∑ k ∈ Finset.range (natFunctionBound F),
          if k < F omega then (1 : ℝ) else 0 := by
    intro omega
    symm
    exact sum_range_indicator_eq (Nat.le_of_lt (lt_natFunctionBound F omega))
  simp_rw [hlayer, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hlevel : k < F omega <;>
    simp [natUpperLevel, Set.indicator, hlevel, mul_comm]





theorem functionalBKR_monotone_nat (phi : E -> Bool -> ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (F G : ConfigSpace E -> ℕ) (hF : Monotone F) (hG : Monotone G) :
    productExpectation phi (functionalDisjointMax (natAsReal F) (natAsReal G)) ≤
      productExpectation phi (natAsReal F) * productExpectation phi (natAsReal G) := by
  calc
    productExpectation phi (functionalDisjointMax (natAsReal F) (natAsReal G)) ≤
        ∑ omega : ConfigSpace E, pweight phi omega *
          (∑ k ∈ Finset.range (natFunctionBound F),
            ∑ l ∈ Finset.range (natFunctionBound G),
              eventIndicator
                (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) omega) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (functionalDisjointMax_natAsReal_le F G omega)
        (pweight_nonneg hphi0 omega)
    _ = ∑ k ∈ Finset.range (natFunctionBound F),
          ∑ l ∈ Finset.range (natFunctionBound G),
            wprob phi (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      unfold wprob eventIndicator
      apply Finset.sum_congr rfl
      intro omega homega
      rw [mul_comm]
    _ ≤ ∑ k ∈ Finset.range (natFunctionBound F),
          ∑ l ∈ Finset.range (natFunctionBound G),
            wprob phi (natUpperLevel F k) * wprob phi (natUpperLevel G l) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact bk_wprob_general phi hphi0 hphi1
        (natUpperLevel_isIncreasing hF k) (natUpperLevel_isIncreasing hG l)
    _ = productExpectation phi (natAsReal F) *
          productExpectation phi (natAsReal G) := by
      rw [productExpectation_natAsReal_eq_levels,
        productExpectation_natAsReal_eq_levels, Finset.sum_mul_sum]

end StatMech.FrontierA
