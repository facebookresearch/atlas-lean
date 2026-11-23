/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Decision.FiniteBinaryOptimal

/-!
# Tests for the weighted-score binary Bayes rule

Concrete two-point instances: the four deterministic risks, strict
optimality of the identity rule, a genuine weighted tie with different
densities, one-sided support, and joint-zero support.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExtTest.Probability.Decision

theorem weightedScore_det_constFalse_risk :
    (1 - (1/3 : ℝ)) * 1 * ((3/4 : ℝ) * 0 + (1/4) * 0)
      + (1/3) * 4 * ((1/4 : ℝ) * (1 - 0) + (3/4) * (1 - 0)) = 4/3 := by
  norm_num

/-- Nonvacuity: identity deterministic rule has risk `1/2` (the optimum). -/
theorem weightedScore_det_id_risk :
    (1 - (1/3 : ℝ)) * 1 * ((3/4 : ℝ) * 0 + (1/4) * 1)
      + (1/3) * 4 * ((1/4 : ℝ) * (1 - 0) + (3/4) * (1 - 1)) = 1/2 := by
  norm_num

/-- Nonvacuity: swapped deterministic rule has risk `3/2`. -/
theorem weightedScore_det_swap_risk :
    (1 - (1/3 : ℝ)) * 1 * ((3/4 : ℝ) * 1 + (1/4) * 0)
      + (1/3) * 4 * ((1/4 : ℝ) * (1 - 1) + (3/4) * (1 - 0)) = 3/2 := by
  norm_num

/-- Nonvacuity: always-positive deterministic rule has risk `2/3`. -/
theorem weightedScore_det_constTrue_risk :
    (1 - (1/3 : ℝ)) * 1 * ((3/4 : ℝ) * 1 + (1/4) * 1)
      + (1/3) * 4 * ((1/4 : ℝ) * (1 - 1) + (3/4) * (1 - 1)) = 2/3 := by
  norm_num

/-- Nonvacuity: the identity rule (risk `1/2`) strictly beats the other
three deterministic rules (`4/3`, `3/2`, `2/3`) in the instance above. -/
theorem weightedScore_det_id_strictly_optimal :
    (1/2 : ℝ) < 4/3 ∧ (1/2 : ℝ) < 3/2 ∧ (1/2 : ℝ) < 2/3 := by
  norm_num

/-- Nonvacuity, genuine tie with arbitrary randomization: same
`π = 1/3, cFP = 1, cFN = 4`, but `P0 = (1/2, 1/2)`, `P1 = (1/4, 3/4)`.
At `x = 0` the weighted scores tie:
`(1 - 1/3) * 1 * (1/2) = (1/3) * 4 * (1/4) = 1/3`, although the densities
differ (`P0 0 = 1/2 ≠ 1/4 = P1 0`). Every randomization level at `0` gives
the same contribution, and two rules differing only at `0` have equal risk.
Equal densities alone would not give this: the tie is the weighted one. -/
theorem weightedScore_genuine_tie :
    (1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ) = (1/3) * 4 * (1/4 : ℝ)
    ∧ ∀ a b : ℝ,
        a * ((1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ)) + (1 - a) * ((1/3) * 4 * (1/4 : ℝ))
        = b * ((1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ)) + (1 - b) * ((1/3) * 4 * (1/4 : ℝ)) := by
  constructor
  · norm_num
  · intro a b
    have h : (1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ) = (1/3) * 4 * (1/4 : ℝ) := by norm_num
    rw [h]
    ring

/-- Nonvacuity, one-sided support: `P0 x = 0 < P1 x` strictly favors
deciding `true` at `x` (weighted-score inequality, no division by `P0 x`). -/
theorem weightedScore_oneSidedSupport :
    ∀ π cFP cFN : ℝ, 0 < π → π < 1 → 0 < cFP → 0 < cFN
      → (1 - π) * cFP * (0 : ℝ) < π * cFN * (1/2 : ℝ) := by
  intro π cFP cFN hπ0 hπ1 hcFP hcFN
  simp only [mul_zero]
  have h : 0 < π * cFN * (1/2 : ℝ) := by positivity
  exact h

/-- Nonvacuity, joint-zero support: if `P0 x = P1 x = 0` then both weighted
scores at `x` are `0`, the point is a genuine tie, and every randomization
level contributes `0` there. -/
theorem weightedScore_jointZeroSupport :
    ∀ π cFP cFN a : ℝ,
      a * ((1 - π) * cFP * (0 : ℝ)) + (1 - a) * (π * cFN * (0 : ℝ)) = 0
      ∧ π * cFN * (0 : ℝ) = (1 - π) * cFP * (0 : ℝ) := by
  intro π cFP cFN a
  simp



theorem weightedScore_oneSidedSupport_false :
    ∀ π cFP cFN : ℝ, 0 < π → π < 1 → 0 < cFP → 0 < cFN
      → π * cFN * (0 : ℝ) < (1 - π) * cFP * (1/2 : ℝ) := by
  intro π cFP cFN hπ0 hπ1 hcFP hcFN
  have h1 : (0 : ℝ) < 1 - π := by linarith
  simp only [mul_zero]
  positivity


theorem test_api_weightedScore_optimal :
    (∃ f : Fin 2 → Bool, f 0 = false ∧ f 1 = true)
    ∧ ((1 - (1/3 : ℝ)) * 1 * (∑ x, (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4) x
          * (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1) x)
        + (1/3) * 4 * (∑ x, (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4) x
          * (1 - (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1) x))
        ≤ (1 - (1/3 : ℝ)) * 1 * (∑ x, (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4) x
          * (fun _ : Fin 2 => (1/2 : ℝ)) x)
        + (1/3) * 4 * (∑ x, (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4) x
          * (1 - (fun _ : Fin 2 => (1/2 : ℝ)) x)))
    ∧ ((¬ (1/3 : ℝ) * 4 * (3/4) = (1 - 1/3) * 1 * (1/4))
        ∧ (((1/3 : ℝ) * 4 * (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4) 1
          = (1 - 1/3) * 1 * (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4) 1)
          → ∀ a b : ℝ, MathlibExt.Probability.Decision.weightedScoreContribution
            (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4)
            (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4)
            (1/3) 1 4 a 1
            = MathlibExt.Probability.Decision.weightedScoreContribution
            (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4)
            (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4)
            (1/3) 1 4 b 1))
    ∧ ((1 - (1/3 : ℝ)) * 1 * 0 < (1/3) * 4 * (1/2)) := by
  have hP0 : ∀ x : Fin 2, 0 ≤ (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4) x := by
    rw [Fin.forall_fin_two]
    constructor
    · show (0 : ℝ) ≤ 3/4; norm_num
    · show (0 : ℝ) ≤ 1/4; norm_num
  have hP0sum : ∑ x : Fin 2, (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4) x = 1 := by
    rw [Fin.sum_univ_two]
    show (3/4 : ℝ) + 1/4 = 1; norm_num
  have hP1 : ∀ x : Fin 2, 0 ≤ (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4) x := by
    rw [Fin.forall_fin_two]
    constructor
    · show (0 : ℝ) ≤ 1/4; norm_num
    · show (0 : ℝ) ≤ 3/4; norm_num
  have hP1sum : ∑ x : Fin 2, (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4) x = 1 := by
    rw [Fin.sum_univ_two]
    show (1/4 : ℝ) + 3/4 = 1; norm_num
  have hπ0 : 0 < (1/3 : ℝ) := by norm_num
  have hπ1 : (1/3 : ℝ) < 1 := by norm_num
  have hcFP : 0 < (1 : ℝ) := by norm_num
  have hcFN : 0 < (4 : ℝ) := by norm_num
  have hH := MathlibExt.Probability.Decision.weightedScore_binary_optimal
    (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4)
    (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4)
    (1/3) 1 4 hP0 hP0sum hP1 hP1sum hπ0 hπ1 hcFP hcFN
  obtain ⟨f, -, htrue, hfalse, -⟩ := hH.1
  have hf0 : f 0 = false := by
    apply hfalse 0
    show (1/3 : ℝ) * 4 * (1/4) < (1 - 1/3) * 1 * (3/4); norm_num
  have hf1 : f 1 = true := by
    apply htrue 1
    show (1 - (1/3 : ℝ)) * 1 * (1/4) < (1/3) * 4 * (3/4); norm_num
  have hδmem : ∀ x : Fin 2, (fun _ : Fin 2 => (1/2 : ℝ)) x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    show (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) 1
    rw [Set.mem_Icc]
    norm_num
  have hδ'mem : ∀ x : Fin 2, (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1) x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Fin.forall_fin_two]
    constructor
    · show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1; rw [Set.mem_Icc]; norm_num
    · show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1; rw [Set.mem_Icc]; norm_num
  have h1' : ∀ x : Fin 2, (1 - (1/3 : ℝ)) * 1 * (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4) x
      < (1/3) * 4 * (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4) x
      → (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1) x = 1 := by
    intro x hlt
    by_cases hx : x = 0
    · subst hx
      change (1 - (1/3 : ℝ)) * 1 * (3/4) < (1/3) * 4 * (1/4) at hlt
      norm_num at hlt
    · simp [hx]
  have h0' : ∀ x : Fin 2, (1/3 : ℝ) * 4 * (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4) x
      < (1 - (1/3 : ℝ)) * 1 * (fun x : Fin 2 => if x = 0 then (3/4 : ℝ) else 1/4) x
      → (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1) x = 0 := by
    intro x hlt
    by_cases hx : x = 0
    · subst hx
      rfl
    · have hx1 : x = 1 := Fin.eq_one_of_ne_zero x hx
      subst hx1
      change (1/3 : ℝ) * 4 * (3/4) < (1 - (1/3 : ℝ)) * 1 * (1/4) at hlt
      norm_num at hlt
  have hRisk := hH.2.1 (fun _ : Fin 2 => (1/2 : ℝ))
    (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1) hδmem hδ'mem h1' h0'
  have hNoTie : ¬ (1/3 : ℝ) * 4 * (3/4) = (1 - 1/3) * 1 * (1/4) := by norm_num
  have hTieImp := hH.2.2.1 1
  have hP0'' : ∀ x : Fin 2, 0 ≤ (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1) x := by
    rw [Fin.forall_fin_two]
    constructor
    · show (0 : ℝ) ≤ 0; norm_num
    · show (0 : ℝ) ≤ 1; norm_num
  have hP0''sum : ∑ x : Fin 2, (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1) x = 1 := by
    rw [Fin.sum_univ_two]
    show (0 : ℝ) + 1 = 1; norm_num
  have hP1'' : ∀ x : Fin 2, 0 ≤ (fun x : Fin 2 => if x = 0 then (1/2 : ℝ) else 1/2) x := by
    rw [Fin.forall_fin_two]
    constructor
    · show (0 : ℝ) ≤ 1/2; norm_num
    · show (0 : ℝ) ≤ 1/2; norm_num
  have hP1''sum : ∑ x : Fin 2, (fun x : Fin 2 => if x = 0 then (1/2 : ℝ) else 1/2) x = 1 := by
    rw [Fin.sum_univ_two]
    show (1/2 : ℝ) + 1/2 = 1; norm_num
  have hH'' := MathlibExt.Probability.Decision.weightedScore_binary_optimal
    (fun x : Fin 2 => if x = 0 then (0 : ℝ) else 1)
    (fun x : Fin 2 => if x = 0 then (1/2 : ℝ) else 1/2)
    (1/3) 1 4 hP0'' hP0''sum hP1'' hP1''sum hπ0 hπ1 hcFP hcFN
  have hOneSided := hH''.2.2.2.1 0 rfl (by show (0 : ℝ) < 1/2; norm_num)
  exact ⟨⟨f, hf0, hf1⟩, hRisk, ⟨hNoTie, hTieImp⟩, hOneSided⟩

theorem test_api_weightedScoreContribution_tie_iff :
    ((1/3 : ℝ) * 4 * (1/4) = (1 - 1/3) * 1 * (1/2))
    ∧ (MathlibExt.Probability.Decision.weightedScoreContribution
          (fun _ : Fin 2 => (1/2 : ℝ))
          (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4)
          (1/3) 1 4 (1/4) 0
        = MathlibExt.Probability.Decision.weightedScoreContribution
          (fun _ : Fin 2 => (1/2 : ℝ))
          (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4)
          (1/3) 1 4 (3/4) 0) := by
  have htie : (1/3 : ℝ) * 4 * (1/4) = (1 - 1/3) * 1 * (1/2) := by norm_num
  have hconst : ∀ a b : ℝ, MathlibExt.Probability.Decision.weightedScoreContribution
      (fun _ : Fin 2 => (1/2 : ℝ))
      (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4)
      (1/3) 1 4 a 0
      = MathlibExt.Probability.Decision.weightedScoreContribution
      (fun _ : Fin 2 => (1/2 : ℝ))
      (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4)
      (1/3) 1 4 b 0 := by
    intro a b
    unfold MathlibExt.Probability.Decision.weightedScoreContribution
    show a * ((1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ)) + (1 - a) * ((1/3) * 4 * (1/4 : ℝ))
      = b * ((1 - (1/3 : ℝ)) * 1 * (1/2 : ℝ)) + (1 - b) * ((1/3) * 4 * (1/4 : ℝ))
    rw [htie]
    ring
  have hIff := MathlibExt.Probability.Decision.weightedScoreContribution_constant_iff
    (fun _ : Fin 2 => (1/2 : ℝ))
    (fun x : Fin 2 => if x = 0 then (1/4 : ℝ) else 3/4)
    (1/3) 1 4 0
  exact ⟨hIff.mp hconst, hIff.mpr htie (1/4) (3/4)⟩

end MathlibExtTest.Probability.Decision
