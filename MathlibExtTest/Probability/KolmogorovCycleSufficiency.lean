/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovCycleNecessity
public import MathlibExt.Probability.KolmogorovCycleSufficiency
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for Kolmogorov's cycle theorem, sufficiency half

Concrete checks on `StochasticMatrix.kolmogorov_cycle_sufficiency`:
the uniform two-state chain (whose reversible distribution must be
`(1/2, 1/2)`), the cycle weight on that chain, a one-way chain violating
the cycle condition, and the one-state chain. The nonuniform two-state
chain checks a cycle weight of `1/2`, a three-edge ratio product,
normalizer `3/2`, normalized masses `(2/3, 1/3)`, and the actual
sufficiency witness's masses.
-/

public section

namespace MathlibExtTest.Probability.KolmogorovCycleSufficiency

/-- Both theorem halves apply to the same canonical matrix, giving the equivalence. -/
example {M : ℕ} (P : StochasticMatrix M) (hirr : P.IsIrreducible) :
    P.IsReversible ↔ P.KolmogorovCycleCondition :=
  ⟨StochasticMatrix.kolmogorov_cycle_necessity P hirr,
    StochasticMatrix.kolmogorov_cycle_sufficiency P hirr⟩

/-- The uniform two-state chain satisfies the hypotheses of the sufficiency
theorem, and the reversible distribution it produces is `(1/2, 1/2)`:
detailed balance forces the two masses to be equal, and they sum to `1`. -/
example :
    ∃ π : StochasticMatrix.Distribution 1,
      (⟨fun _ _ => (1 / 2 : ℝ), fun _ _ => by norm_num,
        fun _ => by
          show ∑ _j : Fin 2, (1 / 2 : ℝ) = 1
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num⟩ : StochasticMatrix 1).IsStationary π ∧
      (⟨fun _ _ => (1 / 2 : ℝ), fun _ _ => by norm_num,
        fun _ => by
          show ∑ _j : Fin 2, (1 / 2 : ℝ) = 1
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num⟩ : StochasticMatrix 1).DetailedBalance π ∧
      π.val 0 = 1 / 2 ∧ π.val 1 = 1 / 2 := by
  let P : StochasticMatrix 1 :=
    { prob := fun _ _ => 1 / 2
      nonneg := fun _ _ => by norm_num
      row_sum := fun _ => by
        show ∑ _j : Fin 2, (1 / 2 : ℝ) = 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num }
  have hprob : ∀ x y : Fin 2, P.prob x y = 1 / 2 := fun _ _ => rfl
  have hirr : P.IsIrreducible := by
    show ∀ i j : Fin 2, ∃ n : ℕ, 0 < n ∧ 0 < P.matPow n i j
    intro i j
    refine ⟨1, one_pos, ?_⟩
    show 0 < ∑ k, P.prob i k * P.matPow 0 k j
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · show 0 < P.prob i j * P.matPow 0 j j
      rw [show P.matPow 0 j j = 1 by simp [StochasticMatrix.matPow]]
      rw [mul_one]
      show (0 : ℝ) < 1 / 2
      norm_num
    · intro k _ hkj
      show P.prob i k * P.matPow 0 k j = 0
      rw [show P.matPow 0 k j = 0 by simp [StochasticMatrix.matPow, hkj]]
      simp

  have hcycle : P.KolmogorovCycleCondition := by
    refine ⟨?_, ?_⟩
    · intro x y _
      show (0 : ℝ) < 1 / 2
      norm_num
    · intro n c _ _
      simp [hprob]
  have hrev : ∃ π : StochasticMatrix.Distribution 1,
      P.IsStationary π ∧ P.DetailedBalance π :=
    StochasticMatrix.kolmogorov_cycle_sufficiency P hirr hcycle
  obtain ⟨π, hstat, hdb⟩ := hrev
  refine ⟨π, hstat, hdb, ?_, ?_⟩
  · have h01 := hdb 0 1
    simp only [hprob] at h01
    have hsum := π.sum_one
    rw [Fin.sum_univ_two] at hsum
    have heq : π.val 0 = π.val 1 := by linarith
    linarith
  · have h01 := hdb 0 1
    simp only [hprob] at h01
    have hsum := π.sum_one
    rw [Fin.sum_univ_two] at hsum
    have heq : π.val 0 = π.val 1 := by linarith
    linarith

/-- On the uniform two-state chain, every cycle weight is `1`: every ratio
`P(x, y) / P(y, x)` is `(1/2) / (1/2) = 1`. -/
example :
    ∃ (P : StochasticMatrix 1) (hirr : P.IsIrreducible),
      ∀ i₀ j, StochasticMatrix.cycleWeight P hirr i₀ j = 1 := by
  let P : StochasticMatrix 1 :=
    { prob := fun _ _ => 1 / 2
      nonneg := fun _ _ => by norm_num
      row_sum := fun _ => by
        show ∑ _j : Fin 2, (1 / 2 : ℝ) = 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num }
  have hirr : P.IsIrreducible := by
    show ∀ i j : Fin 2, ∃ n : ℕ, 0 < n ∧ 0 < P.matPow n i j
    intro i j
    refine ⟨1, one_pos, ?_⟩
    show 0 < ∑ k, P.prob i k * P.matPow 0 k j
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · show 0 < P.prob i j * P.matPow 0 j j
      rw [show P.matPow 0 j j = 1 by simp [StochasticMatrix.matPow]]
      rw [mul_one]
      show (0 : ℝ) < 1 / 2
      norm_num
    · intro k _ hkj
      show P.prob i k * P.matPow 0 k j = 0
      rw [show P.matPow 0 k j = 0 by simp [StochasticMatrix.matPow, hkj]]
      simp

  have hpath : ∀ path : List (Fin 2),
      StochasticMatrix.listRatioProduct P path = 1 := by
    intro path
    induction path with
    | nil => rfl
    | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b rest =>
        show (P.prob a b / P.prob b a) *
            StochasticMatrix.listRatioProduct P (b :: rest) = 1
        rw [ih]
        have h1 : P.prob a b / P.prob b a = 1 := by
          show (1 / 2 : ℝ) / (1 / 2) = 1
          norm_num
        rw [h1, mul_one]
  exact ⟨P, hirr, fun i₀ j => by
    show StochasticMatrix.listRatioProduct P
        (Classical.choose (hirr.exists_path i₀ j)) = 1
    rw [hpath]⟩

/-- The one-way two-state chain (`0 → 1` with probability `1`, no return)
violates symmetric support, hence violates the cycle condition. -/
example (P : StochasticMatrix 1) (h01 : P.prob 0 1 = 1) (h10 : P.prob 1 0 = 0) :
    ¬ P.KolmogorovCycleCondition := by
  intro hcycle
  have hpos : P.prob 1 0 > 0 := hcycle.symm_support 0 1 (by rw [h01]; norm_num)
  rw [h10] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- The one-state chain: the sufficiency theorem produces the unique
distribution, which puts mass `1` on the single state. -/
example :
    ∃ π : StochasticMatrix.Distribution 0,
      (⟨fun _ _ => (1 : ℝ), fun _ _ => by norm_num,
        fun _ => by simp⟩ : StochasticMatrix 0).IsStationary π ∧
      π.val 0 = 1 := by
  let P : StochasticMatrix 0 :=
    { prob := fun _ _ => 1
      nonneg := fun _ _ => by norm_num
      row_sum := fun _ => by simp }
  have hprob : ∀ x y : Fin 1, P.prob x y = 1 := fun _ _ => rfl
  have hirr : P.IsIrreducible := by
    show ∀ i j : Fin 1, ∃ n : ℕ, 0 < n ∧ 0 < P.matPow n i j
    intro i j
    refine ⟨1, one_pos, ?_⟩
    show 0 < ∑ k, P.prob i k * P.matPow 0 k j
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · show 0 < P.prob i j * P.matPow 0 j j
      rw [show P.matPow 0 j j = 1 by simp [StochasticMatrix.matPow]]
      rw [mul_one]
      show (0 : ℝ) < 1
      norm_num
    · intro k _ hkj
      show P.prob i k * P.matPow 0 k j = 0
      rw [show P.matPow 0 k j = 0 by simp [StochasticMatrix.matPow, hkj]]
      simp

  have hcycle : P.KolmogorovCycleCondition := by
    refine ⟨?_, ?_⟩
    · intro x y _
      show (0 : ℝ) < 1
      norm_num
    · intro n c _ _
      simp [hprob]
  have hrev : ∃ π : StochasticMatrix.Distribution 0,
      P.IsStationary π ∧ P.DetailedBalance π :=
    StochasticMatrix.kolmogorov_cycle_sufficiency P hirr hcycle
  obtain ⟨π, hstat, -⟩ := hrev
  refine ⟨π, hstat, ?_⟩
  have hsum := π.sum_one
  rw [Fin.sum_univ_one] at hsum
  exact hsum

/-- A nonuniform two-state chain with both rows `(2/3, 1/3)`. -/
noncomputable def nonuniformTwo : StochasticMatrix 1 where
  prob := fun _ j => if j = 0 then 2 / 3 else 1 / 3
  nonneg := by intro i j; split_ifs <;> norm_num
  row_sum := by
    intro i
    change (∑ j : Fin 2, if j = 0 then (2 / 3 : ℝ) else 1 / 3) = 1
    norm_num [Fin.sum_univ_two]

/-- The explicit reversible input distribution is independent of cycle weights. -/
noncomputable def nonuniformPi : StochasticMatrix.Distribution 1 where
  val := fun j => if j = 0 then 2 / 3 else 1 / 3
  nonneg := by intro j; split_ifs <;> norm_num
  sum_one := by
    change (∑ j : Fin 2, if j = 0 then (2 / 3 : ℝ) else 1 / 3) = 1
    norm_num [Fin.sum_univ_two]

/-- Every state can reach every other state in one positive-probability step. -/
theorem nonuniformTwo_irreducible : nonuniformTwo.IsIrreducible := by
  intro i j
  refine ⟨1, by norm_num, ?_⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [StochasticMatrix.matPow, nonuniformTwo, Fin.sum_univ_two]

/-- Detailed balance follows from the explicit row masses, not from sufficiency. -/
theorem nonuniformTwo_detailedBalance : nonuniformTwo.DetailedBalance nonuniformPi := by
  intro i j
  change nonuniformPi.val i * nonuniformPi.val j = nonuniformPi.val j * nonuniformPi.val i
  exact mul_comm _ _

/-- Canonical necessity supplies the cycle condition for the asymmetric fixture. -/
theorem nonuniformTwo_cycle : nonuniformTwo.KolmogorovCycleCondition :=
  StochasticMatrix.kolmogorov_cycle_necessity nonuniformTwo nonuniformTwo_irreducible
    ⟨nonuniformPi, StochasticMatrix.detailedBalance_isStationary
      nonuniformTwo nonuniformPi nonuniformTwo_detailedBalance, nonuniformTwo_detailedBalance⟩

/-- Compare the chosen cycle-weight path with an explicit positive path. -/
theorem nonuniformTwo_cycleWeight_as_path (j : Fin 2) (path : List (Fin 2))
    (hhead : path.head? = some 0) (hlast : path.getLast? = some j)
    (hpos : 0 < StochasticMatrix.listPathProduct nonuniformTwo path) :
    StochasticMatrix.cycleWeight nonuniformTwo nonuniformTwo_irreducible 0 j =
      StochasticMatrix.listRatioProduct nonuniformTwo path := by
  change StochasticMatrix.listRatioProduct nonuniformTwo
    (Classical.choose (nonuniformTwo_irreducible.exists_path 0 j)) = _
  have hspec := Classical.choose_spec (nonuniformTwo_irreducible.exists_path 0 j)
  exact StochasticMatrix.cycleWeight_path_independent nonuniformTwo nonuniformTwo_cycle
    nonuniformTwo_irreducible 0 j
    (Classical.choose (nonuniformTwo_irreducible.exists_path 0 j)) path
    hspec.1 hspec.2.1 hhead hlast hspec.2.2 hpos

/-- The reference-state weight is computed using the singleton path `[0]`. -/
theorem nonuniformTwo_cycleWeight_zero :
    StochasticMatrix.cycleWeight nonuniformTwo nonuniformTwo_irreducible 0 0 = 1 := by
  rw [nonuniformTwo_cycleWeight_as_path 0 [0] (by simp) (by simp)
    (by norm_num [StochasticMatrix.listPathProduct])]
  rfl

/-- The path `[0,1]` selects `P(0,1)/P(1,0) = 1/2`, not its inverse. -/
theorem nonuniformTwo_cycleWeight_one :
    StochasticMatrix.cycleWeight nonuniformTwo nonuniformTwo_irreducible 0 1 = 1 / 2 := by
  rw [nonuniformTwo_cycleWeight_as_path 1 [0, 1] (by simp) (by simp)
    (by norm_num [StochasticMatrix.listPathProduct, nonuniformTwo])]
  norm_num [StochasticMatrix.listRatioProduct, nonuniformTwo]

/-- Three non-unit edge factors multiply as `(1/2) * 2 * (1/2)`. -/
theorem nonuniformTwo_three_edge_ratio :
    StochasticMatrix.listRatioProduct nonuniformTwo [0, 1, 0, 1] = 1 / 2 := by
  norm_num [StochasticMatrix.listRatioProduct, nonuniformTwo]

/-- The cycle-weight normalizer is `1 + 1/2 = 3/2`. -/
theorem nonuniformTwo_normalizer :
    (∑ j : Fin 2, StochasticMatrix.cycleWeight nonuniformTwo nonuniformTwo_irreducible 0 j) =
      3 / 2 := by
  rw [Fin.sum_univ_two, nonuniformTwo_cycleWeight_zero, nonuniformTwo_cycleWeight_one]
  norm_num

/-- Normalizing the actual cycle weights gives masses `(2/3,1/3)`. -/
theorem nonuniformTwo_normalized_weights :
    StochasticMatrix.cycleWeight nonuniformTwo nonuniformTwo_irreducible 0 0 /
        (∑ j : Fin 2, StochasticMatrix.cycleWeight nonuniformTwo nonuniformTwo_irreducible 0 j) =
      2 / 3 ∧
    StochasticMatrix.cycleWeight nonuniformTwo nonuniformTwo_irreducible 0 1 /
        (∑ j : Fin 2, StochasticMatrix.cycleWeight nonuniformTwo nonuniformTwo_irreducible 0 j) =
      1 / 3 := by
  constructor <;> rw [nonuniformTwo_normalizer]
  · rw [nonuniformTwo_cycleWeight_zero]
    norm_num
  · rw [nonuniformTwo_cycleWeight_one]
    norm_num

/-- The distribution obtained directly from sufficiency has the same asymmetric masses. -/
theorem nonuniformTwo_sufficiency_masses :
    ∃ π : StochasticMatrix.Distribution 1,
      nonuniformTwo.IsStationary π ∧ nonuniformTwo.DetailedBalance π ∧
        π.val 0 = 2 / 3 ∧ π.val 1 = 1 / 3 := by
  obtain ⟨π, hstat, hdb⟩ := StochasticMatrix.kolmogorov_cycle_sufficiency
    nonuniformTwo nonuniformTwo_irreducible nonuniformTwo_cycle
  have h01 := hdb 0 1
  change π.val 0 * (1 / 3) = π.val 1 * (2 / 3) at h01
  have hsum := π.sum_one
  rw [Fin.sum_univ_two] at hsum
  have hmass0 : π.val 0 = 2 / 3 := by linarith
  have hmass1 : π.val 1 = 1 / 3 := by linarith
  exact ⟨π, hstat, hdb, hmass0, hmass1⟩

#check nonuniformTwo_cycleWeight_zero
#check nonuniformTwo_cycleWeight_one
#check nonuniformTwo_three_edge_ratio
#check nonuniformTwo_normalizer
#check nonuniformTwo_normalized_weights
#check nonuniformTwo_sufficiency_masses
#print axioms nonuniformTwo_cycleWeight_one
#print axioms nonuniformTwo_normalized_weights
#print axioms nonuniformTwo_sufficiency_masses

#check StochasticMatrix.kolmogorov_cycle_necessity
#check StochasticMatrix.kolmogorov_cycle_sufficiency
#print axioms StochasticMatrix.kolmogorov_cycle_necessity
#print axioms StochasticMatrix.kolmogorov_cycle_sufficiency

end MathlibExtTest.Probability.KolmogorovCycleSufficiency
