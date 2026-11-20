/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.Z2GaugeDualCoupling

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

noncomputable local instance gaugeSupportPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in


theorem gaugeWilsonSurfaceTerm_pos (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (A : Finset P) :
    0 < ∏ p ∈ A, Real.tanh (K p) := by
  exact Finset.prod_pos fun p _ => tanh_pos_of_pos (hK p)

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in


theorem abs_wilsonSpin (L : Finset E) (omega : GaugeConfig E) :
    |wilsonSpin L omega| = 1 := by
  unfold wilsonSpin
  rw [abs_prod]
  apply Finset.prod_eq_one
  intro e _
  rcases gaugeEdgeSpin_eq_one_or_neg_one omega e with h | h <;> simp [h]

omit [DecidableEq P] in

theorem abs_gaugeWilsonNumerator_le_partition
    (incidence : P → Finset E) (K : P → ℝ) (L : Finset E) :
    |gaugeWilsonNumerator incidence K L| ≤ gaugePartition incidence K := by
  unfold gaugeWilsonNumerator gaugePartition
  calc
    |∑ omega : GaugeConfig E,
        wilsonSpin L omega * gaugeWeight incidence K omega| ≤
        ∑ omega : GaugeConfig E,
          |wilsonSpin L omega * gaugeWeight incidence K omega| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ omega : GaugeConfig E, gaugeWeight incidence K omega := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_wilsonSpin, abs_of_pos]
      · simp
      · exact Real.exp_pos _

omit [DecidableEq P] in


theorem abs_gaugeWilsonExpectation_le_one
    (incidence : P → Finset E) (K : P → ℝ) (L : Finset E) :
    |gaugeWilsonExpectation incidence K L| ≤ 1 := by
  unfold gaugeWilsonExpectation
  rw [abs_div, abs_of_pos (gaugePartition_pos incidence K),
    div_le_one (gaugePartition_pos incidence K)]
  exact abs_gaugeWilsonNumerator_le_partition incidence K L

omit [Fintype E] [DecidableEq P] in


theorem gaugeWilsonSurfaceSum_pos_iff_exists_boundary
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) :
    0 < gaugeWilsonSurfaceSum incidence K L ↔
      ∃ A : Finset P, HasWilsonBoundary incidence A L := by
  classical
  unfold gaugeWilsonSurfaceSum
  constructor
  · intro hsum
    by_contra hnone
    push Not at hnone
    have hempty :
        (Finset.univ : Finset P).powerset.filter
            (fun A => HasWilsonBoundary incidence A L) = ∅ := by
      ext A
      simp [hnone A]
    rw [hempty, Finset.sum_empty] at hsum
    exact lt_irrefl 0 hsum
  · rintro ⟨A, hA⟩
    apply Finset.sum_pos
    · intro B _
      exact gaugeWilsonSurfaceTerm_pos K hK B
    · exact ⟨A, by simp [hA]⟩

omit [DecidableEq P] in


theorem gaugeWilsonExpectation_pos_iff_exists_boundary
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) :
    0 < gaugeWilsonExpectation incidence K L ↔
      ∃ A : Finset P, HasWilsonBoundary incidence A L := by
  rw [gaugeWilsonExpectation_eq_surfaceRatio]
  have hden : 0 < gaugeClosedSurfaceSum incidence K :=
    gaugeClosedSurfaceSum_pos incidence K
  constructor
  · intro hratio
    rcases div_pos_iff.mp hratio with hpos | hneg
    · exact (gaugeWilsonSurfaceSum_pos_iff_exists_boundary
        incidence K hK L).mp hpos.1
    · exact False.elim ((not_lt_of_ge hden.le) hneg.2)
  · intro hexists
    exact div_pos
      ((gaugeWilsonSurfaceSum_pos_iff_exists_boundary
        incidence K hK L).mpr hexists) hden

omit [DecidableEq P] in


theorem gaugeWilsonExpectation_eq_zero_iff_no_boundary
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) :
    gaugeWilsonExpectation incidence K L = 0 ↔
      ¬ ∃ A : Finset P, HasWilsonBoundary incidence A L := by
  have hnonneg : 0 ≤ gaugeWilsonExpectation incidence K L := by
    rw [gaugeWilsonExpectation_eq_surfaceRatio]
    exact div_nonneg
      (Finset.sum_nonneg fun A _ =>
        (gaugeWilsonSurfaceTerm_pos K hK A).le)
      (gaugeClosedSurfaceSum_pos incidence K).le
  constructor
  · intro hzero hexists
    have hpos := (gaugeWilsonExpectation_pos_iff_exists_boundary
      incidence K hK L).mpr hexists
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · intro hnone
    apply le_antisymm _ hnonneg
    by_contra hnotle
    have hpos : 0 < gaugeWilsonExpectation incidence K L := lt_of_not_ge hnotle
    exact hnone ((gaugeWilsonExpectation_pos_iff_exists_boundary
      incidence K hK L).mp hpos)

omit [DecidableEq P] in


theorem gaugeWilsonExpectation_mem_Icc
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) :
    gaugeWilsonExpectation incidence K L ∈ Set.Icc (0 : ℝ) 1 := by
  have hnonneg : 0 ≤ gaugeWilsonExpectation incidence K L := by
    rw [gaugeWilsonExpectation_eq_surfaceRatio]
    exact div_nonneg
      (Finset.sum_nonneg fun A _ =>
        (gaugeWilsonSurfaceTerm_pos K hK A).le)
      (gaugeClosedSurfaceSum_pos incidence K).le
  exact ⟨hnonneg,
    le_trans (le_abs_self _) (abs_gaugeWilsonExpectation_le_one incidence K L)⟩

end StatMech.FrontierA
