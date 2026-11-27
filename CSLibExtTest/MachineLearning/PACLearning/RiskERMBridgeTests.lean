/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.RiskERMBridge

/-!
# Risk ERM bridge tests

Closed checks over the two-point domain `Bool`: on the realizable sample `id` is a 0-1 empirical
risk minimizer while `not` is not (and Mathlib's `IsMinOn` API applies to `id` through
`isERM_iff_isMinOn`), a finite class has a consistent ERM learner, the finite-family selector lands
in the version space, both 0-1 bridges evaluate exactly (the empirical error is derived from the
empirical 0-1 risk through the bridge), plus boundary cases (single-point samples, one-member and
duplicate families, empty classes, and empty domains or label sets, where every learner is vacuously
an ERM learner) and negative cases (an ERM outside the version space on a non-realizable sample, a
consistent learner that is not an ERM learner, and an infinite class with no minimizer).
-/

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open CSLibExt.MachineLearning.GeneralizationBounds (risk empiricalRisk empiricalRisk_eq_inv_mul_sum)

/-! ### Two-point domain: `id` minimizes, `not` does not -/

example : IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
    (![(true, true), (false, false)] : LabeledSample Bool Bool 2) id := by
  have hreal : Realizable ({id, not} : ConceptClass Bool Bool)
      (![(true, true), (false, false)] : LabeledSample Bool Bool 2) :=
    ⟨id, Set.mem_insert _ _, by decide⟩
  rw [isERM_zeroOneLoss_iff_mem_versionSpace hreal]
  exact ⟨Set.mem_insert _ _, by decide⟩

example : ¬ IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
    (![(true, true), (false, false)] : LabeledSample Bool Bool 2) not := by
  intro hcon
  have hle := hcon.2 id (Set.mem_insert _ _)
  rw [empiricalRisk_zeroOneLoss_eq_miscount_div,
    empiricalRisk_zeroOneLoss_eq_miscount_div] at hle
  have e1 : empiricalMiscount not
      (![(true, true), (false, false)] : LabeledSample Bool Bool 2) = 2 := by
    decide
  have e2 : empiricalMiscount id
      (![(true, true), (false, false)] : LabeledSample Bool Bool 2) = 0 := by
    decide
  rw [e1, e2] at hle
  norm_num at hle

example : id ∈ VersionSpace ({id, not} : ConceptClass Bool Bool)
    (![(true, true), (false, false)] : LabeledSample Bool Bool 2) :=
  ⟨Set.mem_insert _ _, by decide⟩

example : IsMinOn (empiricalRisk zeroOneLoss
    (![(true, true), (false, false)] : LabeledSample Bool Bool 2)) {not} id := by
  have hreal : Realizable ({id, not} : ConceptClass Bool Bool)
      (![(true, true), (false, false)] : LabeledSample Bool Bool 2) :=
    ⟨id, Set.mem_insert _ _, by decide⟩
  have herm : IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
      (![(true, true), (false, false)] : LabeledSample Bool Bool 2) id :=
    (isERM_zeroOneLoss_iff_mem_versionSpace hreal).mpr ⟨Set.mem_insert _ _, by decide⟩
  exact (isERM_iff_isMinOn.mp herm).2.of_subset (Set.subset_insert _ _)

/-! ### A finite class has a consistent ERM learner -/

example : ∃ A : Learner Bool Bool 2,
    IsConsistent A ({id, not} : ConceptClass Bool Bool) := by
  have hC : ({id, not} : ConceptClass Bool Bool).Finite :=
    Set.Finite.insert id (Set.finite_singleton not)
  have hne : ({id, not} : ConceptClass Bool Bool).Nonempty := ⟨id, Set.mem_insert _ _⟩
  obtain ⟨A, hA⟩ := exists_isERMLearner_of_finite (m := 2) zeroOneLoss hC hne
  exact ⟨A, hA.isConsistent⟩

/-! ### The finite-family selector lands in the version space -/

example : ((![id, not] : Fin 2 → (Bool → Bool))
      (ProbabilityTheory.ermIdx
        (fun j => zeroOneLoss ((![id, not] : Fin 2 → (Bool → Bool)) j))
        (![(true, true), (false, false)] : LabeledSample Bool Bool 2))) ∈
    VersionSpace (Set.range (![id, not] : Fin 2 → (Bool → Bool)))
      (![(true, true), (false, false)] : LabeledSample Bool Bool 2) := by
  have hreal : Realizable (Set.range (![id, not] : Fin 2 → (Bool → Bool)))
      (![(true, true), (false, false)] : LabeledSample Bool Bool 2) :=
    ⟨id, ⟨0, by simp⟩, by decide⟩
  have herm := isERM_ermIdx zeroOneLoss (![id, not] : Fin 2 → (Bool → Bool))
    (![(true, true), (false, false)] : LabeledSample Bool Bool 2)
  rw [isERM_zeroOneLoss_iff_mem_versionSpace hreal] at herm
  exact herm

/-! ### Both 0-1 bridges evaluate exactly -/

example : empiricalRisk zeroOneLoss
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2) not = 1 / 2 ∧
    (empiricalError not
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2)).toReal = 1 / 2 := by
  have hL : empiricalRisk zeroOneLoss
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2) not = 1 / 2 := by
    rw [empiricalRisk_zeroOneLoss_eq_miscount_div]
    norm_num [empiricalMiscount]
    decide
  have hR : (empiricalError not
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2)).toReal = 1 / 2 := by
    have hb := empiricalRisk_zeroOneLoss_eq_toReal_empiricalError
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2) not
    linarith
  exact ⟨hL, hR⟩

example : risk zeroOneLoss (Measure.dirac ((true, true) : Bool × Bool)) not = 1 := by
  have hmem : ((true, true) : Bool × Bool) ∈ {p : Bool × Bool | not p.1 ≠ p.2} := by
    decide
  rw [risk, integral_dirac]
  unfold zeroOneLoss
  rw [Set.indicator_of_mem hmem]

/-! ### Boundary: single-point samples -/

example : empiricalRisk zeroOneLoss
    (![(true, false)] : LabeledSample Bool Bool 1) not = 0 := by
  have e : empiricalMiscount not (![(true, false)] : LabeledSample Bool Bool 1) = 0 := by
    decide
  rw [empiricalRisk_zeroOneLoss_eq_miscount_div, e]
  norm_num

example : empiricalRisk zeroOneLoss
      (![(true, false)] : LabeledSample Bool Bool 1) not = 0 ∧
    (empiricalError not
      (![(true, false)] : LabeledSample Bool Bool 1)).toReal = 0 := by
  have e : empiricalMiscount not (![(true, false)] : LabeledSample Bool Bool 1) = 0 := by
    decide
  have hL : empiricalRisk zeroOneLoss
      (![(true, false)] : LabeledSample Bool Bool 1) not = 0 := by
    rw [empiricalRisk_zeroOneLoss_eq_miscount_div, e]
    norm_num
  have hR : (empiricalError not
      (![(true, false)] : LabeledSample Bool Bool 1)).toReal = 0 := by
    have hb := empiricalRisk_zeroOneLoss_eq_toReal_empiricalError
      (![(true, false)] : LabeledSample Bool Bool 1) not
    linarith
  exact ⟨hL, hR⟩

example : ∃ h, IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
    (![(true, true)] : LabeledSample Bool Bool 1) h ∧ h = id := by
  have hC : ({id, not} : ConceptClass Bool Bool).Finite :=
    Set.Finite.insert id (Set.finite_singleton not)
  have hne : ({id, not} : ConceptClass Bool Bool).Nonempty := ⟨id, Set.mem_insert _ _⟩
  obtain ⟨h, hh⟩ := exists_isERM_of_finite (n := 1) zeroOneLoss hC hne
    (![(true, true)] : LabeledSample Bool Bool 1)
  have hreal : Realizable ({id, not} : ConceptClass Bool Bool)
      (![(true, true)] : LabeledSample Bool Bool 1) :=
    ⟨id, Set.mem_insert _ _, by decide⟩
  have hmem : h ∈ VersionSpace ({id, not} : ConceptClass Bool Bool)
      (![(true, true)] : LabeledSample Bool Bool 1) :=
    (isERM_zeroOneLoss_iff_mem_versionSpace hreal).mp hh
  rw [mem_versionSpace_iff] at hmem
  obtain ⟨hmC, hall⟩ := hmem
  have h0 := hall 0
  have q : ((![(true, true)] : LabeledSample Bool Bool 1) 0) = (true, true) := by
    decide
  rw [q] at h0
  change h true = true at h0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmC
  refine ⟨h, hh, ?_⟩
  rcases hmC with rfl | rfl
  · rfl
  · exact absurd h0 (by decide)

example : ∃ A : Learner Bool Bool 1, IsERMLearner zeroOneLoss
    ({id, not} : ConceptClass Bool Bool) A ∧
    A (![(true, true)] : LabeledSample Bool Bool 1) = id := by
  have hC : ({id, not} : ConceptClass Bool Bool).Finite :=
    Set.Finite.insert id (Set.finite_singleton not)
  have hne : ({id, not} : ConceptClass Bool Bool).Nonempty := ⟨id, Set.mem_insert _ _⟩
  obtain ⟨A, hA⟩ := exists_isERMLearner_of_finite (m := 1) zeroOneLoss hC hne
  have hreal : Realizable ({id, not} : ConceptClass Bool Bool)
      (![(true, true)] : LabeledSample Bool Bool 1) :=
    ⟨id, Set.mem_insert _ _, by decide⟩
  have hh : IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
      (![(true, true)] : LabeledSample Bool Bool 1)
      (A (![(true, true)] : LabeledSample Bool Bool 1)) :=
    hA (![(true, true)] : LabeledSample Bool Bool 1)
  have hmem : A (![(true, true)] : LabeledSample Bool Bool 1) ∈
      VersionSpace ({id, not} : ConceptClass Bool Bool)
        (![(true, true)] : LabeledSample Bool Bool 1) :=
    (isERM_zeroOneLoss_iff_mem_versionSpace hreal).mp hh
  rw [mem_versionSpace_iff] at hmem
  obtain ⟨hmC, hall⟩ := hmem
  have h0 := hall 0
  have q : ((![(true, true)] : LabeledSample Bool Bool 1) 0) = (true, true) := by
    decide
  rw [q] at h0
  change (A (![(true, true)] : LabeledSample Bool Bool 1)) true = true at h0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmC
  refine ⟨A, hA, ?_⟩
  rcases hmC with hid | hnot
  · exact hid
  · rw [hnot] at h0
    exact absurd h0 (by decide)

example : IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
      (![(true, true)] : LabeledSample Bool Bool 1) id ∧
    ¬ IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
      (![(true, true)] : LabeledSample Bool Bool 1) not := by
  have hreal : Realizable ({id, not} : ConceptClass Bool Bool)
      (![(true, true)] : LabeledSample Bool Bool 1) :=
    ⟨id, Set.mem_insert _ _, by decide⟩
  rw [isERM_zeroOneLoss_iff_mem_versionSpace hreal,
    isERM_zeroOneLoss_iff_mem_versionSpace hreal]
  constructor
  · exact ⟨Set.mem_insert _ _, by decide⟩
  · intro hmem
    rw [mem_versionSpace_iff] at hmem
    obtain ⟨-, hall⟩ := hmem
    have h0 := hall 0
    have q : ((![(true, true)] : LabeledSample Bool Bool 1) 0) = (true, true) := by
      decide
    rw [q] at h0
    change (false : Bool) = true at h0
    exact absurd h0 (by decide)

example : IsConsistent (fun S : LabeledSample Bool Bool 1 =>
      if (S 0).1 = (S 0).2 then id else not)
    ({id, not} : ConceptClass Bool Bool) ∧
    ((fun S : LabeledSample Bool Bool 1 => if (S 0).1 = (S 0).2 then id else not)
      (![(true, false)] : LabeledSample Bool Bool 1) = not) ∧
    IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
      (![(true, false)] : LabeledSample Bool Bool 1)
      ((fun S : LabeledSample Bool Bool 1 => if (S 0).1 = (S 0).2 then id else not)
        (![(true, false)] : LabeledSample Bool Bool 1)) := by
  have hcons : IsConsistent (fun S : LabeledSample Bool Bool 1 =>
      if (S 0).1 = (S 0).2 then id else not)
      ({id, not} : ConceptClass Bool Bool) := by
    intro S hS
    obtain ⟨c, hcC, hc⟩ := hS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcC
    have h0 := hc 0
    rcases hcC with rfl | rfl
    · have hif : (S 0).1 = (S 0).2 := h0.symm
      change (if (S 0).1 = (S 0).2 then id else not) ∈
        VersionSpace ({id, not} : ConceptClass Bool Bool) S
      rw [ite_eq_left hif]
      refine ⟨Set.mem_insert _ _, fun i => ?_⟩
      have hi0 : i = 0 := Subsingleton.elim _ _
      rw [hi0]
      exact hif
    · have hne : (S 0).1 ≠ (S 0).2 := by
        rw [h0]
        exact (by decide : ∀ b : Bool, b ≠ not b) _
      change (if (S 0).1 = (S 0).2 then id else not) ∈
        VersionSpace ({id, not} : ConceptClass Bool Bool) S
      rw [ite_eq_right hne]
      refine ⟨by simp, fun i => ?_⟩
      have hi0 : i = 0 := Subsingleton.elim _ _
      rw [hi0]
      exact h0.symm
  have hreal : Realizable ({id, not} : ConceptClass Bool Bool)
      (![(true, false)] : LabeledSample Bool Bool 1) :=
    ⟨not, by simp, by decide⟩
  have hout : (fun S : LabeledSample Bool Bool 1 =>
      if (S 0).1 = (S 0).2 then id else not)
      (![(true, false)] : LabeledSample Bool Bool 1) = not := by
    have hcond : ¬ ((![(true, false)] : LabeledSample Bool Bool 1) 0).1 =
        ((![(true, false)] : LabeledSample Bool Bool 1) 0).2 := by
      decide
    change (if ((![(true, false)] : LabeledSample Bool Bool 1) 0).1 =
      ((![(true, false)] : LabeledSample Bool Bool 1) 0).2 then id else not) = not
    rw [ite_eq_right hcond]
  have herm : IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
      (![(true, false)] : LabeledSample Bool Bool 1)
      ((fun S : LabeledSample Bool Bool 1 => if (S 0).1 = (S 0).2 then id else not)
        (![(true, false)] : LabeledSample Bool Bool 1)) :=
    isConsistent_iff_forall_realizable_isERM.mp hcons _ hreal
  exact ⟨hcons, hout, herm⟩

example : ∃ A : Learner Bool Bool 1, IsERMLearner zeroOneLoss
    ({id, not} : ConceptClass Bool Bool) A ∧
    IsConsistent A ({id, not} : ConceptClass Bool Bool) ∧
    A (![(true, false)] : LabeledSample Bool Bool 1) = not := by
  have hC : ({id, not} : ConceptClass Bool Bool).Finite :=
    Set.Finite.insert id (Set.finite_singleton not)
  have hne : ({id, not} : ConceptClass Bool Bool).Nonempty := ⟨id, Set.mem_insert _ _⟩
  obtain ⟨A, hA⟩ := exists_isERMLearner_of_finite (m := 1) zeroOneLoss hC hne
  have hreal : Realizable ({id, not} : ConceptClass Bool Bool)
      (![(true, false)] : LabeledSample Bool Bool 1) :=
    ⟨not, by simp, by decide⟩
  have hmem : A (![(true, false)] : LabeledSample Bool Bool 1) ∈
      VersionSpace ({id, not} : ConceptClass Bool Bool)
        (![(true, false)] : LabeledSample Bool Bool 1) :=
    hA.isConsistent _ hreal
  rw [mem_versionSpace_iff] at hmem
  obtain ⟨hmC, hall⟩ := hmem
  have h0 := hall 0
  have q : ((![(true, false)] : LabeledSample Bool Bool 1) 0) = (true, false) := by
    decide
  rw [q] at h0
  change (A (![(true, false)] : LabeledSample Bool Bool 1)) true = false at h0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmC
  refine ⟨A, hA, hA.isConsistent, ?_⟩
  rcases hmC with hid | hnot
  · rw [hid] at h0
    exact absurd h0 (by decide)
  · exact hnot

/-! ### Boundary: one-member and duplicate families -/

example : ((![id] : Fin 1 → (Bool → Bool))
      (ProbabilityTheory.ermIdx (fun j => zeroOneLoss ((![id] : Fin 1 → (Bool → Bool)) j))
        (![(true, true)] : LabeledSample Bool Bool 1))) = id ∧
    IsERM zeroOneLoss (Set.range (![id] : Fin 1 → (Bool → Bool)))
      (![(true, true)] : LabeledSample Bool Bool 1)
      ((![id] : Fin 1 → (Bool → Bool))
        (ProbabilityTheory.ermIdx
          (fun j => zeroOneLoss ((![id] : Fin 1 → (Bool → Bool)) j))
          (![(true, true)] : LabeledSample Bool Bool 1))) := by
  have herm := isERM_ermIdx zeroOneLoss (![id] : Fin 1 → (Bool → Bool))
    (![(true, true)] : LabeledSample Bool Bool 1)
  have hsel : ((![id] : Fin 1 → (Bool → Bool))
      (ProbabilityTheory.ermIdx (fun j => zeroOneLoss ((![id] : Fin 1 → (Bool → Bool)) j))
        (![(true, true)] : LabeledSample Bool Bool 1))) = id := by
    obtain ⟨j, hj⟩ := herm.1
    have hj0 : j = 0 := Subsingleton.elim _ _
    rw [← hj, hj0]
    simp
  exact ⟨hsel, herm⟩

example : ((![id, id] : Fin 2 → (Bool → Bool))
      (ProbabilityTheory.ermIdx
        (fun j => zeroOneLoss ((![id, id] : Fin 2 → (Bool → Bool)) j))
        (![(true, true), (false, false)] : LabeledSample Bool Bool 2))) = id ∧
    IsERM zeroOneLoss (Set.range (![id, id] : Fin 2 → (Bool → Bool)))
      (![(true, true), (false, false)] : LabeledSample Bool Bool 2)
      ((![id, id] : Fin 2 → (Bool → Bool))
        (ProbabilityTheory.ermIdx
          (fun j => zeroOneLoss ((![id, id] : Fin 2 → (Bool → Bool)) j))
          (![(true, true), (false, false)] : LabeledSample Bool Bool 2))) := by
  have herm := isERM_ermIdx zeroOneLoss (![id, id] : Fin 2 → (Bool → Bool))
    (![(true, true), (false, false)] : LabeledSample Bool Bool 2)
  have hsel : ((![id, id] : Fin 2 → (Bool → Bool))
      (ProbabilityTheory.ermIdx
        (fun j => zeroOneLoss ((![id, id] : Fin 2 → (Bool → Bool)) j))
        (![(true, true), (false, false)] : LabeledSample Bool Bool 2))) = id := by
    obtain ⟨j, hj⟩ := herm.1
    rw [← hj]
    fin_cases j <;> simp
  exact ⟨hsel, herm⟩

/-! ### Boundary: empty classes -/

example : ¬ IsERM zeroOneLoss (∅ : ConceptClass Bool Bool)
    (![(true, true)] : LabeledSample Bool Bool 1) id :=
  fun hcon => hcon.1

example (A : Learner Bool Bool 1) :
    ¬ IsERMLearner zeroOneLoss (∅ : ConceptClass Bool Bool) A := by
  intro hA
  exact (hA (![(true, true)] : LabeledSample Bool Bool 1)).1

-- With an empty domain or an empty label set there is no labelled sample, so even the empty class
-- has an ERM learner.
example : ∃ A : Learner Empty Bool 1, IsERMLearner zeroOneLoss (∅ : ConceptClass Empty Bool) A :=
  ⟨fun _ => Empty.elim, fun S => (S 0).1.elim⟩

example : ∃ A : Learner Bool Empty 1, IsERMLearner zeroOneLoss (∅ : ConceptClass Bool Empty) A :=
  ⟨fun S => (S 0).2.elim, fun S => (S 0).2.elim⟩

-- Samples of size `m = 0` are outside the API: `IsERMLearner` requires `[NeZero m]`.

/-! ### Negative: ERM without realizability, outside the version space -/

example : (∃ h, IsERM zeroOneLoss (Set.univ : ConceptClass Bool Bool)
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2) h) ∧
    VersionSpace (Set.univ : ConceptClass Bool Bool)
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2) = ∅ := by
  have e1 : empiricalMiscount id
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2) = 1 := by
    decide
  have herm : IsERM zeroOneLoss (Set.univ : ConceptClass Bool Bool)
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2) id := by
    refine ⟨Set.mem_univ _, fun h' _ => ?_⟩
    rw [empiricalRisk_zeroOneLoss_eq_miscount_div,
      empiricalRisk_zeroOneLoss_eq_miscount_div, e1]
    have hcard : 1 ≤ empiricalMiscount h'
        (![(true, true), (true, false)] : LabeledSample Bool Bool 2) := by
      cases htb : h' true
      case false =>
        have e0 : ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 0).1 = true ∧
            ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 0).2 = true := by
          decide
        have herr : h' ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 0).1 ≠
            ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 0).2 := by
          rw [e0.1, e0.2, htb]
          decide
        have hmem : (0 : Fin 2) ∈ Finset.univ.filter (fun i : Fin 2 =>
            h' ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) i).1 ≠
            ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) i).2) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, herr⟩
        have hpos := Finset.card_pos.mpr ⟨(0 : Fin 2), hmem⟩
        exact hpos
      case true =>
        have e1 : ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 1).1 = true ∧
            ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 1).2 = false := by
          decide
        have herr : h' ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 1).1 ≠
            ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 1).2 := by
          rw [e1.1, e1.2, htb]
          decide
        have hmem : (1 : Fin 2) ∈ Finset.univ.filter (fun i : Fin 2 =>
            h' ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) i).1 ≠
            ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) i).2) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, herr⟩
        have hpos := Finset.card_pos.mpr ⟨(1 : Fin 2), hmem⟩
        exact hpos
    have hk : ((1 : ℕ) : ℝ) ≤
        (empiricalMiscount h' (![(true, true), (true, false)] :
          LabeledSample Bool Bool 2) : ℝ) := by
      exact_mod_cast hcard
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hk (by positivity)
  have hvs : VersionSpace (Set.univ : ConceptClass Bool Bool)
      (![(true, true), (true, false)] : LabeledSample Bool Bool 2) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro h hmem
    rw [mem_versionSpace_iff] at hmem
    obtain ⟨-, hall⟩ := hmem
    have h0 := hall 0
    have h1 := hall 1
    have q0 : ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 0) =
        (true, true) := by
      decide
    have q1 : ((![(true, true), (true, false)] : LabeledSample Bool Bool 2) 1) =
        (true, false) := by
      decide
    rw [q0] at h0
    rw [q1] at h1
    change h true = true at h0
    change h true = false at h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  exact ⟨⟨id, herm⟩, hvs⟩

/-! ### Negative: a consistent learner that is not an ERM learner -/

example : ∃ A : Learner Bool Bool 3,
    IsConsistent A ({id, not} : ConceptClass Bool Bool) ∧
    ¬ IsERMLearner zeroOneLoss ({id, not} : ConceptClass Bool Bool) A := by
  classical
  have hC : ({id, not} : ConceptClass Bool Bool).Finite :=
    Set.Finite.insert id (Set.finite_singleton not)
  have hne : ({id, not} : ConceptClass Bool Bool).Nonempty := ⟨id, Set.mem_insert _ _⟩
  obtain ⟨Aerm, hAerm⟩ := exists_isERMLearner_of_finite (m := 3) zeroOneLoss hC hne
  have hcons := hAerm.isConsistent
  have hnr : ¬ Realizable ({id, not} : ConceptClass Bool Bool)
      (![(true, true), (false, false), (true, false)] : LabeledSample Bool Bool 3) := by
    rintro ⟨c, hcC, hc⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcC
    rcases hcC with rfl | rfl
    · have h2 := hc 2
      have q2 : ((![(true, true), (false, false), (true, false)] :
          LabeledSample Bool Bool 3) 2) = (true, false) := by
        decide
      rw [q2] at h2
      change (false : Bool) = true at h2
      exact absurd h2 (by decide)
    · have h0 := hc 0
      have q0 : ((![(true, true), (false, false), (true, false)] :
          LabeledSample Bool Bool 3) 0) = (true, true) := by
        decide
      rw [q0] at h0
      change (true : Bool) = false at h0
      exact absurd h0 (by decide)
  have hnotmin : ¬ IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
      (![(true, true), (false, false), (true, false)] : LabeledSample Bool Bool 3) not := by
    intro hcon
    have hle := hcon.2 id (Set.mem_insert _ _)
    rw [empiricalRisk_zeroOneLoss_eq_miscount_div,
      empiricalRisk_zeroOneLoss_eq_miscount_div] at hle
    have e1 : empiricalMiscount not
        (![(true, true), (false, false), (true, false)] : LabeledSample Bool Bool 3) = 2 := by
      decide
    have e2 : empiricalMiscount id
        (![(true, true), (false, false), (true, false)] : LabeledSample Bool Bool 3) = 1 := by
      decide
    rw [e1, e2] at hle
    norm_num at hle
  refine ⟨fun S => if S = (![(true, true), (false, false), (true, false)] :
      LabeledSample Bool Bool 3) then not else Aerm S, ?_, ?_⟩
  · intro S hS
    have hne' : S ≠ (![(true, true), (false, false), (true, false)] :
        LabeledSample Bool Bool 3) := by
      rintro rfl
      exact hnr hS
    change (if S = (![(true, true), (false, false), (true, false)] :
      LabeledSample Bool Bool 3) then not else Aerm S) ∈
      VersionSpace ({id, not} : ConceptClass Bool Bool) S
    split_ifs with h
    · exact absurd h hne'
    · exact hcons S hS
  · intro hA
    have hstar : IsERM zeroOneLoss ({id, not} : ConceptClass Bool Bool)
        (![(true, true), (false, false), (true, false)] : LabeledSample Bool Bool 3)
        (if (![(true, true), (false, false), (true, false)] : LabeledSample Bool Bool 3) =
          (![(true, true), (false, false), (true, false)] : LabeledSample Bool Bool 3)
          then not else Aerm (![(true, true), (false, false), (true, false)] :
          LabeledSample Bool Bool 3)) :=
      hA (![(true, true), (false, false), (true, false)] : LabeledSample Bool Bool 3)
    split_ifs at hstar with h
    · exact hnotmin hstar
    · exact absurd rfl h

/-! ### Negative: an infinite class with no minimizer -/

example : ¬ ∃ h : ℝ, IsERM (fun h _ => h) (Set.Ioi (0 : ℝ))
    ((![0] : Fin 1 → ℝ)) h := by
  have hn0 : ((1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne 1)
  have hrisk : ∀ g : ℝ, empiricalRisk (fun h _ => h) ((![0] : Fin 1 → ℝ)) g = g := by
    intro g
    rw [empiricalRisk_eq_inv_mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  rintro ⟨h, hm, hmin⟩
  rw [Set.mem_Ioi] at hm
  have hhalf : h / 2 ∈ Set.Ioi (0 : ℝ) := by
    rw [Set.mem_Ioi]
    linarith
  have hle := hmin (h / 2) hhalf
  rw [hrisk h, hrisk (h / 2)] at hle
  linarith

end Cslib.MachineLearning.PACLearning

#print axioms Cslib.MachineLearning.PACLearning.empiricalRisk_zeroOneLoss_eq_toReal_empiricalError
#print axioms Cslib.MachineLearning.PACLearning.isERM_iff_isMinOn
#print axioms Cslib.MachineLearning.PACLearning.exists_isERM_of_finite
#print axioms Cslib.MachineLearning.PACLearning.exists_isERMLearner_of_finite
#print axioms Cslib.MachineLearning.PACLearning.isERM_zeroOneLoss_iff_mem_versionSpace
#print axioms Cslib.MachineLearning.PACLearning.isConsistent_iff_forall_realizable_isERM
#print axioms Cslib.MachineLearning.PACLearning.IsERMLearner.isConsistent
#print axioms CSLibExt.MachineLearning.GeneralizationBounds.empiricalRisk_eq_inv_mul_sum
#print axioms Cslib.MachineLearning.PACLearning.isERM_ermIdx
