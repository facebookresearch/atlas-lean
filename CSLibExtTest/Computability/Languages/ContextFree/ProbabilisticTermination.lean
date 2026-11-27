/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.ProbabilisticTermination

/-!
# Tests for eventual termination

Certain termination at `p = 0` and `p = 1/2`, termination probability
`1/2` at `p = 2/3` with depth-3 iterate `971/2187`, and membership
witnesses for terminating and non-terminating points.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Cslib.Language

open MathlibExt.Probability

/-- Tests (p = 0): termination is certain, already at depth one; the all-leaf point
terminates. -/
private theorem test_p_zero :
    BinaryTreeAddressLaw.law 0 le_rfl zero_le_one eventualTermination = 1 ∧
      BinaryTreeAddressLaw.law 0 le_rfl zero_le_one (terminationByDepth 1) = 1 ∧
      (fun _ : List Bool => false) ∈ eventualTermination := by
  refine ⟨law_eventualTermination_of_le le_rfl zero_le_one (by norm_num), ?_, ?_⟩
  · rw [law_terminationByDepth, cgTotal_succ]
    simp [cgTotal, cgTrees]
  · exact terminationByDepth_subset_eventualTermination 1 (Or.inl rfl)

/-- Tests (p = 1/3): the fixed-point equation `s = 2/3 + s^2/3` has the roots `1`
and `2`; only `1` lies in `[0, 1]`, and it is the termination probability, matching the
existing limit `tendsto_chiGemanS_third`. -/
private theorem test_p_third :
    BinaryTreeAddressLaw.law (1 / 3) (by norm_num) (by norm_num) eventualTermination = 1 ∧
      (BinaryTreeAddressLaw.law (1 / 3) (by norm_num) (by norm_num)
        eventualTermination).toReal = 1 ∧
      (2 : ℝ) = 1 - 1 / 3 + 1 / 3 * 2 ^ 2 ∧ (2 : ℝ) ∉ Set.Icc (0 : ℝ) 1 := by
  have h1 := law_eventualTermination_of_le (p := 1 / 3) (by norm_num) (by norm_num)
    (by norm_num)
  have hlim := tendsto_chiGemanS_law_eventualTermination (p := 1 / 3) (by norm_num)
    (by norm_num)
  have h23 : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  rw [h23] at hlim
  refine ⟨h1, tendsto_nhds_unique hlim tendsto_chiGemanS_third, by norm_num, ?_⟩
  simp only [Set.mem_Icc, not_and, not_le]
  intro _
  norm_num

/-- Tests (p = 1/2, critical): termination is certain, `1` is the only root in
`[0, 1]`, the value agrees with `tendsto_chiGemanS_half`, and no finite depth captures
all of it, so continuity from below is needed. -/
private theorem test_p_half :
    BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num) eventualTermination = 1 ∧
      (BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num)
        eventualTermination).toReal = 1 ∧
      (∀ s ∈ {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ s = 1 - 1 / 2 + 1 / 2 * s ^ 2}, s = 1) ∧
      Tendsto (fun h => BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num)
          (terminationByDepth h)) atTop (𝓝 1) ∧
      (∀ h, BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num)
          (terminationByDepth h) < 1) := by
  have h1 := law_eventualTermination_of_le (p := 1 / 2) (by norm_num) (by norm_num) le_rfl
  have hlim := tendsto_chiGemanS_law_eventualTermination (p := 1 / 2) (by norm_num)
    (by norm_num)
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h12] at hlim
  refine ⟨h1, tendsto_nhds_unique hlim tendsto_chiGemanS_half, ?_, ?_, ?_⟩
  · rintro s ⟨-, hs⟩
    nlinarith [sq_nonneg (s - 1)]
  · have ht := tendsto_law_terminationByDepth (p := 1 / 2) (by norm_num) (by norm_num)
    rwa [h1] at ht
  · intro h
    rw [law_terminationByDepth, h12]
    have key : ∀ n, 0 ≤ cgTotal (1 / 2) (1 / 2) n ∧ cgTotal (1 / 2) (1 / 2) n < 1 := by
      intro n
      induction n with
      | zero => simp [cgTotal, cgTrees]
      | succ n ih =>
        rw [cgTotal_succ]
        constructor <;> nlinarith [ih.1, ih.2]
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (key h).2

/-- Tests (p = 2/3, two roots, leastness essential): both `1/2` and `1` solve
`s = 1/3 + 2 s^2/3` in `[0, 1]`; the termination probability is the smaller one, `1/2`,
not `1`; nontermination also has probability `1/2`. The value is consistent with the
existing bound `chiGeman_main_half`, the depth-2 mass `11/27`, and the supremum form. -/
private theorem test_p_two_thirds :
    (1 / 2 : ℝ) ∈ {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ s = 1 - 2 / 3 + 2 / 3 * s ^ 2} ∧
      (1 : ℝ) ∈ {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ s = 1 - 2 / 3 + 2 / 3 * s ^ 2} ∧
      (BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num)
        eventualTermination).toReal = 1 / 2 ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) eventualTermination ≠ 1 ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) eventualTerminationᶜ =
        ENNReal.ofReal (1 / 2) ∧
      (⨆ h, BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num)
        (terminationByDepth h)) = ENNReal.ofReal (1 / 2) ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) (terminationByDepth 2) =
        ENNReal.ofReal (11 / 27) ∧
      (∀ h, chiGemanS (2 / 3) (1 / 3) h ≤
        (BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num)
          eventualTermination).toReal) := by
  obtain ⟨hE, hC⟩ := law_eventualTermination_two_thirds
  have hR : (BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num)
      eventualTermination).toReal = 1 / 2 := by
    rw [hE, ENNReal.toReal_ofReal (by norm_num)]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num⟩, ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩,
    hR, ?_, hC, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, ENNReal.toReal_one] at hR
    norm_num at hR
  · rw [← law_eventualTermination_eq_iSup, hE]
  · rw [law_terminationByDepth, cgTotal_succ, cgTotal_succ]
    simp [cgTotal, cgTrees]
    norm_num
  · intro h
    rw [hR]
    exact chiGeman_main_half h

/-- Tests (p = 1): two roots `0` and `1` in `[0, 1]`; termination has probability
`0`, the least one, although the event is nonempty; nontermination is certain and the
all-branch point never terminates. -/
private theorem test_p_one :
    BinaryTreeAddressLaw.law 1 zero_le_one le_rfl eventualTermination = 0 ∧
      BinaryTreeAddressLaw.law 1 zero_le_one le_rfl eventualTerminationᶜ = 1 ∧
      (1 : ℝ) ∈ {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ s = 1 - 1 + 1 * s ^ 2} ∧
      (fun _ : List Bool => false) ∈ eventualTermination ∧
      (fun _ : List Bool => true) ∉ eventualTermination := by
  have h0 := law_eventualTermination_of_gt (p := 1) zero_le_one le_rfl (by norm_num)
  have hc := law_compl_eventualTermination_of_gt (p := 1) zero_le_one le_rfl (by norm_num)
  norm_num at h0 hc
  refine ⟨h0, hc, ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩,
    terminationByDepth_subset_eventualTermination 1 (Or.inl rfl), ?_⟩
  intro hmem
  obtain ⟨h, hh⟩ := Set.mem_iUnion.1 hmem
  induction h with
  | zero => exact hh
  | succ n ih =>
    rcases hh with h1 | ⟨⟨-, hl⟩, -⟩
    · exact Bool.noConfusion h1
    · exact ih hl

/-- Tests (cutoff masses are PGF iterates): at `p = 2/3` the depth-3 cutoff mass is
`971/2187 = f^[3] 0` for `f s = 1/3 + 2 s^2/3`, and the depth-2 mass `11/27` is the
probability that generation 2 of the binary Galton-Watson process is empty. -/
private theorem test_iterates :
    (pgf id (GaltonWatson.binaryOffspring (2 / 3)))^[3] 0 = 971 / 2187 ∧
      (GaltonWatson.law (GaltonWatson.binaryOffspring (2 / 3)) 2).real {0} = 11 / 27 := by
  have hc : ∀ h, cgTotal (2 / 3) (1 - 2 / 3) h =
      (pgf id (GaltonWatson.binaryOffspring (2 / 3)))^[h] 0 :=
    cgTotal_eq_iterate_pgf_binaryOffspring (by norm_num) (by norm_num)
  have hz := law_terminationByDepth_eq_law_real_zero (p := 2 / 3) (by norm_num)
    (by norm_num) 2
  rw [law_terminationByDepth] at hz
  have h0 : cgTotal (2 / 3) (1 - 2 / 3) 0 = 0 := by simp [cgTotal, cgTrees]
  have h2 : cgTotal (2 / 3) (1 - 2 / 3) 2 = 11 / 27 := by
    rw [cgTotal_succ, cgTotal_succ, h0]; norm_num
  refine ⟨?_, ?_⟩
  · rw [← hc, cgTotal_succ, h2]; norm_num
  · rw [h2] at hz
    have hnn : 0 ≤ (GaltonWatson.law (GaltonWatson.binaryOffspring (2 / 3)) 2).real {0} :=
      measureReal_nonneg
    exact ((ENNReal.ofReal_eq_ofReal_iff (by norm_num) hnn).1 hz).symm

/-- Tests (regime boundary and the extinction link): termination is certain at
`p = 1/2` but not at `p = 2/3`; at `p = 2/3` the termination probability is the binary
extinction probability `1/2`, which is the least fixed point. -/
private theorem test_regimes :
    BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num) eventualTermination = 1 ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) eventualTermination ≠ 1 ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) eventualTermination =
        ENNReal.ofReal (GaltonWatson.extinctionProb (GaltonWatson.binaryOffspring (2 / 3))) ∧
      GaltonWatson.extinctionProb (GaltonWatson.binaryOffspring (2 / 3)) = 1 / 2 ∧
      (∀ s ∈ {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ s = 1 - 2 / 3 + 2 / 3 * s ^ 2},
        (BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num)
          eventualTermination).toReal ≤ s) := by
  have hiff := law_eventualTermination_eq_one_iff (p := 2 / 3) (by norm_num) (by norm_num)
  have hgt := law_eventualTermination_of_gt (p := 2 / 3) (by norm_num) (by norm_num)
    (by norm_num)
  have hlink := law_eventualTermination (p := 2 / 3) (by norm_num) (by norm_num)
  refine ⟨(law_eventualTermination_eq_one_iff (by norm_num) (by norm_num)).2 le_rfl,
    fun h => absurd (hiff.1 h) (by norm_num), hlink, ?_,
    (isLeast_law_eventualTermination (p := 2 / 3) (by norm_num) (by norm_num)).2⟩
  rw [hgt] at hlink
  have hnn : 0 ≤ GaltonWatson.extinctionProb (GaltonWatson.binaryOffspring (2 / 3)) :=
    ((GaltonWatson.isLeast_extinctionProb_binaryOffspring' (p := 2 / 3) (by norm_num)
      (by norm_num)).1.1.1)
  have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) hnn).1 hlink
  rw [← this]; norm_num

/-- Tests (main theorem at p = 2/3): measurability, the depth limit, and the
supercritical value `(1 - 2/3)/(2/3) = 1/2` all follow from the single statement; the
subcritical branch is vacuous there. -/
private theorem test_main :
    MeasurableSet eventualTermination ∧
      Tendsto (fun h => BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num)
        (terminationByDepth h)) atTop (𝓝 (ENNReal.ofReal (1 / 2))) ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) eventualTermination =
        ENNReal.ofReal (1 / 2) := by
  obtain ⟨hm, ht, -, -, -, hgt⟩ :=
    binaryGrammar_eventualTermination (p := 2 / 3) (by norm_num) (by norm_num)
  have hv := hgt (by norm_num)
  have hq : ((1 : ℝ) - 2 / 3) / (2 / 3) = 1 / 2 := by norm_num
  rw [hq] at hv
  rw [hv] at ht
  exact ⟨hm, ht, hv⟩

/-- Tests (event membership): a root branch with two leaf children terminates (it
lies in the depth-2 event); the measurability of the event does not depend on `p`. -/
private theorem test_membership :
    (fun a : List Bool => decide (a.length ≠ 1)) ∈ eventualTermination ∧
      MeasurableSet (eventualTermination ∩ BinaryTreeAddressLaw.branchAt []) := by
  refine ⟨terminationByDepth_subset_eventualTermination 2 ?_,
    measurableSet_eventualTermination.inter (BinaryTreeAddressLaw.measurableSet_branchAt [])⟩
  exact Or.inr ⟨⟨rfl, Or.inl rfl⟩, Or.inl rfl⟩


end Cslib.Language
