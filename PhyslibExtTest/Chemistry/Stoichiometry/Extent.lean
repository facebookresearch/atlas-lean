/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Stoichiometry.Extent

/-!

# Tests for reaction extent, limiting reagents and yield

-/

@[expose] public section

open Matrix Chemistry.Stoichiometry

namespace PhyslibExtTest.Chemistry.Stoichiometry

example {ι : Type*} [Fintype ι] (ν n₀ : ι → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i) (h : ∃ i, ν i < 0) :
    {ξ : ℝ | 0 ≤ ξ ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ} =
      Set.Icc 0 ((Finset.univ.filter fun i => ν i < 0).inf'
        (Finset.filter_nonempty_iff.2 (h.imp fun i hi => ⟨Finset.mem_univ i, hi⟩))
        fun i => n₀ i / |ν i|) :=
  forwardFeasibleExtents_eq_Icc ν n₀ hn₀ h

example {ι : Type*} (ν n₀ : ι → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i) (h : ∀ i, 0 ≤ ν i) :
    {ξ : ℝ | 0 ≤ ξ ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ} = Set.Ici 0 :=
  forwardFeasibleExtents_eq_Ici ν n₀ hn₀ h

example {ι : Type*} [Fintype ι] (ν n₀ : ι → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i) (h : ∃ i, 0 < ν i) :
    {ξ : ℝ | ξ ≤ 0 ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ} =
      Set.Icc (-(Finset.univ.filter fun i => 0 < ν i).inf'
        (Finset.filter_nonempty_iff.2 (h.imp fun i hi => ⟨Finset.mem_univ i, hi⟩))
        fun i => n₀ i / ν i) 0 :=
  reverseFeasibleExtents_eq_Icc ν n₀ hn₀ h

example {ι : Type*} (ν n₀ : ι → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i) (h : ∀ i, ν i ≤ 0) :
    {ξ : ℝ | ξ ≤ 0 ∧ ∀ i, 0 ≤ n₀ i + ν i * ξ} = Set.Iic 0 :=
  reverseFeasibleExtents_eq_Iic ν n₀ hn₀ h

example {ι : Type*} [Fintype ι] (ν n₀ : ι → ℝ) (h : ∃ i, ν i < 0) :
    ∃ i, ν i < 0 ∧ n₀ i / |ν i| = (Finset.univ.filter fun i => ν i < 0).inf'
      (Finset.filter_nonempty_iff.2 (h.imp fun i hi => ⟨Finset.mem_univ i, hi⟩))
      fun i => n₀ i / |ν i| :=
  exists_div_abs_eq_maxExtent ν n₀ h

/-- Methane combustion `CH₄ + 2 O₂ → CO₂ + 2 H₂O`: coefficients on the species
`[CH₄, O₂, CO₂, H₂O]`. -/
noncomputable def methaneCoeffs : Fin 4 → ℝ := ![-1, -2, 1, 2]

/-- Initial amounts of `[CH₄, O₂, CO₂, H₂O]`. -/
noncomputable def methaneInitial : Fin 4 → ℝ := ![2, 5, 0, 0]

/-- The initial amounts are nonnegative. -/
lemma methaneInitial_nonneg : ∀ i, 0 ≤ methaneInitial i := by
  intro i
  fin_cases i <;> norm_num [methaneInitial]

/-- Methane combustion consumes `CH₄`. -/
lemma methane_consumes : ∃ i, methaneCoeffs i < 0 :=
  ⟨0, by norm_num [methaneCoeffs]⟩

/-- The maximal extent of methane combustion from `[2, 5, 0, 0]` is `2`. -/
lemma methane_maxExtent : maxExtent methaneCoeffs methaneInitial methane_consumes = 2 := by
  refine le_antisymm ?_ ((le_maxExtent_iff _).2 fun i => ?_)
  · refine (maxExtent_le _ _ (i := 0) (by norm_num [methaneCoeffs])).trans_eq ?_
    norm_num [methaneCoeffs, methaneInitial]
  · fin_cases i <;> norm_num [methaneCoeffs, methaneInitial]

example : forwardFeasibleExtents methaneCoeffs methaneInitial = Set.Icc 0 2 := by
  rw [forwardFeasibleExtents_eq_Icc _ _ methaneInitial_nonneg methane_consumes, methane_maxExtent]

example : IsLimitingReagent methaneCoeffs methaneInitial 0 := by
  rw [isLimitingReagent_iff methane_consumes, methane_maxExtent]
  norm_num [methaneCoeffs, methaneInitial]

example : ¬ IsLimitingReagent methaneCoeffs methaneInitial 1 := by
  rw [isLimitingReagent_iff methane_consumes, methane_maxExtent]
  norm_num [methaneCoeffs, methaneInitial]

example : methaneCoeffs 2 * maxExtent methaneCoeffs methaneInitial methane_consumes = 2 := by
  rw [methane_maxExtent]
  norm_num [methaneCoeffs]

example : IsGreatest
    ((fun ξ => methaneCoeffs 2 * ξ) '' forwardFeasibleExtents methaneCoeffs methaneInitial) 2 := by
  convert isGreatest_mul_maxExtent methaneInitial_nonneg methane_consumes (P := 2)
    (by norm_num [methaneCoeffs]) using 1
  rw [methane_maxExtent]
  norm_num [methaneCoeffs]

example : percentYield (methaneCoeffs 2 * (3 / 2))
    (methaneCoeffs 2 * maxExtent methaneCoeffs methaneInitial methane_consumes) = 75 := by
  rw [methane_maxExtent]
  norm_num [percentYield, methaneCoeffs]

example : percentYield (methaneCoeffs 2 * (3 / 2))
    (methaneCoeffs 2 * maxExtent methaneCoeffs methaneInitial methane_consumes) ≤ 100 :=
  percentYield_le_hundred methane_consumes (by rw [methane_maxExtent]; norm_num [methaneCoeffs])
    (by rw [methane_maxExtent]; norm_num) rfl

example : percentYield (methaneCoeffs 2 * maxExtent methaneCoeffs methaneInitial methane_consumes)
    (methaneCoeffs 2 * maxExtent methaneCoeffs methaneInitial methane_consumes) = 100 :=
  percentYield_self (by rw [methane_maxExtent]; norm_num [methaneCoeffs])

/-- Amounts of `[CH₄, O₂, CO₂, H₂O]` after methane combustion advances by the extent `3 / 2`. -/
noncomputable def methaneAmountsAt : Fin 4 → ℝ := ![1 / 2, 2, 3 / 2, 3]

/-- The amounts `methaneAmountsAt` come from the initial amounts by the extent `3 / 2`. -/
lemma methaneAmountsAt_eq :
    ∀ i, methaneAmountsAt i = methaneInitial i + methaneCoeffs i * (3 / 2) := by
  intro i
  fin_cases i <;> norm_num [methaneAmountsAt, methaneInitial, methaneCoeffs]

/-- Every coefficient of methane combustion is nonzero. -/
lemma methaneCoeffs_ne_zero : ∀ i, methaneCoeffs i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num [methaneCoeffs]

example : ∀ i, (methaneAmountsAt i - methaneInitial i) / methaneCoeffs i = 3 / 2 := by
  intro i
  fin_cases i <;> norm_num [methaneAmountsAt, methaneInitial, methaneCoeffs]

example (i : Fin 4) : (methaneAmountsAt i - methaneInitial i) / methaneCoeffs i = 3 / 2 :=
  sub_div_eq_extent methaneAmountsAt_eq (methaneCoeffs_ne_zero i)

example (i j : Fin 4) :
    (methaneAmountsAt i - methaneInitial i) / methaneCoeffs i =
      (methaneAmountsAt j - methaneInitial j) / methaneCoeffs j :=
  sub_div_eq_sub_div_of_extent methaneAmountsAt_eq (methaneCoeffs_ne_zero i)
    (methaneCoeffs_ne_zero j)

/-- The stoichiometric matrix of methane combustion alone: its single column is
`methaneCoeffs = [-1, -2, 1, 2]`. -/
noncomputable def methaneStoichMatrix : Matrix (Fin 4) (Fin 1) ℝ :=
  Matrix.of fun i _ => methaneCoeffs i

example : ∀ i, methaneStoichMatrix i 0 = ![-1, -2, 1, 2] i := fun _ => rfl

/-- The unit weight `(1, 1, 1, 1)` on `[CH₄, O₂, CO₂, H₂O]`. -/
noncomputable def unitWeight : Fin 4 → ℝ := ![1, 1, 1, 1]

/-- The unit weight lies in the left kernel of the methane matrix: `-1 - 2 + 1 + 2 = 0`. -/
lemma unitWeight_mem_leftKernel : ∀ j, ∑ i, unitWeight i * methaneStoichMatrix i j = 0 := by
  intro j
  norm_num [unitWeight, methaneStoichMatrix, methaneCoeffs, Fin.sum_univ_four]

/-- The unit weight is strictly positive. -/
lemma unitWeight_pos : ∀ i, 0 < unitWeight i := by
  intro i
  fin_cases i <;> norm_num [unitWeight]

/-- The amounts at the extent `3 / 2` lie on the reachable slice. -/
lemma methaneAmountsAt_mem_reachableSlice :
    methaneAmountsAt ∈ reachableSlice methaneInitial methaneStoichMatrix := by
  refine ⟨fun _ => 3 / 2, ?_⟩
  funext i
  fin_cases i <;>
    norm_num [methaneAmountsAt, methaneInitial, methaneStoichMatrix, methaneCoeffs, mulVec,
      dotProduct]

/-- The amounts at the extent `3 / 2` are nonnegative. -/
lemma methaneAmountsAt_nonneg : ∀ i, 0 ≤ methaneAmountsAt i := by
  intro i
  fin_cases i <;> norm_num [methaneAmountsAt]

/-- The conserved unit-weight total of the initial amounts is `7`. -/
lemma unitWeight_total : ∑ i, unitWeight i * methaneInitial i = 7 := by
  norm_num [unitWeight, methaneInitial, Fin.sum_univ_four]

example : ∑ i, unitWeight i * methaneAmountsAt i = ∑ i, unitWeight i * methaneInitial i :=
  sum_mul_eq_of_mem_reachableSlice unitWeight_mem_leftKernel _ methaneAmountsAt_mem_reachableSlice

example : ∑ i, unitWeight i * methaneAmountsAt i = 7 := by
  norm_num [unitWeight, methaneAmountsAt, Fin.sum_univ_four]

/-- The bound of `le_sum_mul_div_inf'_of_mem_reachableSlice` for the unit weight is
`7 / 1 = 7`. -/
lemma unitWeight_bound :
    (∑ i, unitWeight i * methaneInitial i) / Finset.univ.inf' Finset.univ_nonempty unitWeight =
      7 := by
  have hmin : Finset.univ.inf' Finset.univ_nonempty unitWeight = 1 := by
    refine le_antisymm ((Finset.inf'_le _ (Finset.mem_univ 0)).trans_eq ?_) ?_
    · norm_num [unitWeight]
    · exact Finset.le_inf' _ _ fun i _ => by fin_cases i <;> norm_num [unitWeight]
  rw [unitWeight_total, hmin, div_one]

example : ∀ i, methaneAmountsAt i ≤ 7 := by
  intro i
  have h := le_sum_mul_div_inf'_of_mem_reachableSlice unitWeight_mem_leftKernel unitWeight_pos
    _ ⟨methaneAmountsAt_mem_reachableSlice, methaneAmountsAt_nonneg⟩ i
  rwa [unitWeight_bound] at h

example : Convex ℝ (reachableSlice methaneInitial methaneStoichMatrix ∩ {n | ∀ i, 0 ≤ n i}) :=
  convex_reachableSlice_inter_nonneg _ _

example : Bornology.IsBounded
    (reachableSlice methaneInitial methaneStoichMatrix ∩ {n | ∀ i, 0 ≤ n i}) :=
  isBounded_reachableSlice_inter_nonneg unitWeight_mem_leftKernel unitWeight_pos

example (n₀ : Fin 2 → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i) :
    forwardFeasibleExtents ![1, 2] n₀ = Set.Ici 0 :=
  forwardFeasibleExtents_eq_Ici _ _ hn₀ fun i => by fin_cases i <;> norm_num

example (n₀ : Fin 2 → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i) :
    (100 : ℝ) ∈ forwardFeasibleExtents ![1, 2] n₀ := by
  rw [forwardFeasibleExtents_eq_Ici _ _ hn₀ fun i => by fin_cases i <;> norm_num]
  norm_num

example (n₀ : Fin 2 → ℝ) (hn₀ : ∀ i, 0 ≤ n₀ i) :
    (-1 : ℝ) ∉ forwardFeasibleExtents ![1, 2] n₀ := by
  rw [forwardFeasibleExtents_eq_Ici _ _ hn₀ fun i => by fin_cases i <;> norm_num]
  norm_num

/-- With `ν = [-1, 1]` and `n₀ = [0, 1]`, running the reaction backward consumes the one unit of
species `1`, so the feasible reverse extents are `Set.Icc (-1) 0`. -/
lemma reverseFeasibleExtents_of_product_start :
    reverseFeasibleExtents ![-1, 1] ![0, 1] = Set.Icc (-1) 0 := by
  have h : ∃ i, 0 < (![-1, 1] : Fin 2 → ℝ) i := ⟨1, by norm_num⟩
  rw [reverseFeasibleExtents_eq_Icc _ _ (fun i => by fin_cases i <;> norm_num) h]
  congr 1
  refine le_antisymm ((minExtent_le_iff h).2 fun i => ?_) ?_
  · fin_cases i <;> norm_num
  · exact (neg_div_le_minExtent _ h (i := 1) (by norm_num)).trans_eq' (by norm_num)

example : (-1 : ℝ) ∈ reverseFeasibleExtents ![-1, 1] ![0, 1] := by
  rw [reverseFeasibleExtents_of_product_start]
  norm_num

example : (-2 : ℝ) ∉ reverseFeasibleExtents ![-1, 1] ![0, 1] := by
  rw [reverseFeasibleExtents_of_product_start]
  norm_num

/-- With `ν = [-1, 1]` and `n₀ = [1, 0]`, running the reaction backward would consume species
`1`, which starts at `0`, so `0` is the only feasible reverse extent: the feasible reverse
extents are `Set.Icc 0 0`, not `Set.Icc (-1) 0`, since the extent `-1` leaves `-1` of
species `1`. -/
lemma reverseFeasibleExtents_of_reactant_start :
    reverseFeasibleExtents ![-1, 1] ![1, 0] = Set.Icc 0 0 := by
  have h : ∃ i, 0 < (![-1, 1] : Fin 2 → ℝ) i := ⟨1, by norm_num⟩
  rw [reverseFeasibleExtents_eq_Icc _ _ (fun i => by fin_cases i <;> norm_num) h]
  congr 1
  refine le_antisymm ((minExtent_le_iff h).2 fun i => ?_) ?_
  · fin_cases i <;> norm_num
  · exact (neg_div_le_minExtent _ h (i := 1) (by norm_num)).trans_eq' (by norm_num)

example : (-1 : ℝ) ∉ reverseFeasibleExtents ![-1, 1] ![1, 0] := by
  rw [reverseFeasibleExtents_of_reactant_start]
  norm_num

example : (-2 : ℝ) ∉ reverseFeasibleExtents ![-1, 1] ![1, 0] := by
  rw [reverseFeasibleExtents_of_reactant_start]
  norm_num

example : reverseFeasibleExtents ![-1, 1] ![1, 0] ≠ Set.Icc (-1) 0 := by
  rw [reverseFeasibleExtents_of_reactant_start]
  intro h
  have h' : (-1 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := h ▸ Set.left_mem_Icc.2 (by norm_num)
  norm_num at h'

example : (2 : ℝ) ∉ forwardFeasibleExtents ![-1, 1] ![1, 0] := by
  have h : ∃ i, (![-1, 1] : Fin 2 → ℝ) i < 0 := ⟨0, by norm_num⟩
  rw [forwardFeasibleExtents_eq_Icc _ _ (fun i => by fin_cases i <;> norm_num) h]
  intro hmem
  have h2 := hmem.2.trans (maxExtent_le _ h (i := 0) (by norm_num))
  norm_num at h2

example : (0 : ℝ) ∉ forwardFeasibleExtents ![-1, 1] ![-1, 0] := by
  rintro ⟨-, h⟩
  have h0 := h 0
  norm_num at h0

example (h : ∃ i, (![-1, 1] : Fin 2 → ℝ) i < 0) :
    maxExtent ![-1, 1] ![-1, 0] h ∉ forwardFeasibleExtents ![-1, 1] ![-1, 0] := by
  rintro ⟨hξ, -⟩
  have h0 := hξ.trans (maxExtent_le _ h (i := 0) (by norm_num))
  norm_num at h0

example (h : ∃ i, (![-1, 1] : Fin 2 → ℝ) i < 0) :
    forwardFeasibleExtents ![-1, 1] ![1, -1] ≠ Set.Icc 0 (maxExtent ![-1, 1] ![1, -1] h) := by
  intro heq
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (maxExtent ![-1, 1] ![1, -1] h) :=
    ⟨le_rfl, (le_maxExtent_iff h).2 fun i => by fin_cases i <;> norm_num⟩
  rw [← heq] at h0
  have h1 := h0.2 1
  norm_num at h1

end PhyslibExtTest.Chemistry.Stoichiometry

#print axioms Chemistry.Stoichiometry.mem_consumedSpecies
#print axioms Chemistry.Stoichiometry.mem_producedSpecies
#print axioms Chemistry.Stoichiometry.consumedSpecies_nonempty
#print axioms Chemistry.Stoichiometry.producedSpecies_nonempty
#print axioms Chemistry.Stoichiometry.maxExtent_le
#print axioms Chemistry.Stoichiometry.le_maxExtent_iff
#print axioms Chemistry.Stoichiometry.neg_div_le_minExtent
#print axioms Chemistry.Stoichiometry.minExtent_le_iff
#print axioms Chemistry.Stoichiometry.nonneg_add_mul_iff_le_div_abs
#print axioms Chemistry.Stoichiometry.nonneg_add_mul_iff_neg_div_le
#print axioms Chemistry.Stoichiometry.forwardFeasibleExtents_eq_Icc
#print axioms Chemistry.Stoichiometry.forwardFeasibleExtents_eq_Ici
#print axioms Chemistry.Stoichiometry.reverseFeasibleExtents_eq_Icc
#print axioms Chemistry.Stoichiometry.reverseFeasibleExtents_eq_Iic
#print axioms Chemistry.Stoichiometry.exists_div_abs_eq_maxExtent
#print axioms Chemistry.Stoichiometry.isLimitingReagent_iff
#print axioms Chemistry.Stoichiometry.exists_isLimitingReagent
#print axioms Chemistry.Stoichiometry.le_maxExtent_of_mem_forwardFeasibleExtents
#print axioms Chemistry.Stoichiometry.maxExtent_mem_forwardFeasibleExtents
#print axioms Chemistry.Stoichiometry.mul_le_mul_maxExtent
#print axioms Chemistry.Stoichiometry.isGreatest_mul_maxExtent
#print axioms Chemistry.Stoichiometry.percentYield_self
#print axioms Chemistry.Stoichiometry.percentYield_le_hundred
#print axioms Chemistry.Stoichiometry.sub_div_eq_extent
#print axioms Chemistry.Stoichiometry.sub_div_eq_sub_div_of_extent
#print axioms Chemistry.Stoichiometry.convex_reachableSlice
#print axioms Chemistry.Stoichiometry.convex_reachableSlice_inter_nonneg
#print axioms Chemistry.Stoichiometry.sum_mul_eq_of_mem_reachableSlice
#print axioms Chemistry.Stoichiometry.le_sum_mul_div_of_mem_reachableSlice
#print axioms Chemistry.Stoichiometry.le_sum_mul_div_inf'_of_mem_reachableSlice
#print axioms Chemistry.Stoichiometry.isBounded_reachableSlice_inter_nonneg
