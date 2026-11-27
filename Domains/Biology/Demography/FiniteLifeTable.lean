/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Conditional survival from a finite life table

Outcome `i < n` records death at the right endpoint of `(i, i + 1]`. The last outcome
records survival through date `n`; its representative date `n + 1` is a marker, not a
prediction of death at that age. All survival events are indexed by dates in the table.
-/

@[expose] public section

namespace Domains.Biology.Demography

/-- A life table through natural age `n` consists of real survivor counts `l₀ ≥ ⋯ ≥ lₙ ≥ 0`
with `l₀ > 0`. Counts need not be integral, successive counts can agree, and `n` may be zero. -/
structure FiniteLifeTable (n : ℕ) where
  /-- The number of survivors at each age from zero through `n`. -/
  survivors : Fin (n + 1) → ℝ
  /-- Survivor counts never increase with age. -/
  antitone : Antitone survivors
  /-- The terminal count is nonnegative. -/
  final_nonneg : 0 ≤ survivors (Fin.last n)
  /-- The initial count, used to normalize the law, is positive. -/
  initial_pos : 0 < survivors 0

namespace FiniteLifeTable

open MeasureTheory

variable {n : ℕ} (L : FiniteLifeTable n)

/-- In a finite table of real survivor counts `l₀ ≥ ⋯ ≥ lₙ ≥ 0` with `l₀ > 0`, the count
assigned to outcome `j < n` is the drop `lⱼ - lⱼ₊₁`; the count assigned to the last outcome
is the residual `lₙ`. These are counts before normalization by `l₀`. -/
def count : Fin (n + 1) → ℝ :=
  Fin.lastCases (L.survivors (Fin.last n)) (fun i ↦ L.survivors i.castSucc - L.survivors i.succ)

private theorem count_nonneg (i : Fin (n + 1)) : 0 ≤ L.count i := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa [count] using L.final_nonneg
  · simpa [count] using sub_nonneg.mpr (L.antitone (Fin.castSucc_le_succ j))

private theorem sum_count : ∑ i, L.count i = L.survivors 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [count, Fin.lastCases_castSucc, Fin.lastCases_last, Finset.sum_sub_distrib]
  linarith only [(Fin.sum_univ_castSucc L.survivors).symm.trans (Fin.sum_univ_succ L.survivors)]

/-- For real counts `l₀ ≥ ⋯ ≥ lₙ ≥ 0` with `l₀ > 0`, the finite probability law has one
outcome of mass `(lᵢ - lᵢ₊₁) / l₀` for death at date `i + 1` in each interval `(i, i + 1]`,
and a last outcome of mass `lₙ / l₀` for survival past `n`. If `n = 0` only this last outcome
remains. It does not specify a lifetime distribution beyond the table. -/
noncomputable def law : PMF (Fin (n + 1)) :=
  PMF.ofFintype (fun i ↦ ENNReal.ofReal (L.count i / L.survivors 0)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (L.count_nonneg i) L.initial_pos.le),
      ← Finset.sum_div, L.sum_count, div_self L.initial_pos.ne', ENNReal.ofReal_one])

/-- In a table of real counts `l₀ ≥ ⋯ ≥ lₙ ≥ 0` with `l₀ > 0`, the probability of the
single death outcome in `(j, j + 1]`, for `j < n`, is `(lⱼ - lⱼ₊₁) / l₀`. -/
theorem law_death (j : Fin n) :
    (L.law j.castSucc).toReal = (L.survivors j.castSucc - L.survivors j.succ) / L.survivors 0 := by
  simpa only [law, PMF.ofFintype_apply, count, Fin.lastCases_castSucc] using
    ENNReal.toReal_ofReal (div_nonneg (L.count_nonneg j.castSucc) L.initial_pos.le)

/-- In a table of real counts `l₀ ≥ ⋯ ≥ lₙ ≥ 0` with `l₀ > 0`, the last outcome, survival
strictly past `n` rather than death at `n`, has probability `lₙ / l₀`. -/
theorem law_residual : (L.law (Fin.last n)).toReal = L.survivors (Fin.last n) / L.survivors 0 := by
  simpa only [law, PMF.ofFintype_apply, count, Fin.lastCases_last] using
    ENNReal.toReal_ofReal (div_nonneg (L.count_nonneg (Fin.last n)) L.initial_pos.le)

/-- For a table ending at `n`, strict survival at age `x ≤ n` means the outcome's representative
date `i + 1` is strictly greater than `x`. In particular, death at `x` is excluded and the last
outcome is included, even at `x = n`. No survival event beyond the horizon is defined. -/
def survives (x : Fin (n + 1)) : Set (Fin (n + 1)) := {i | x.val < i.val + 1}

/-- For real survivor counts `l₀ ≥ ⋯ ≥ lₙ ≥ 0` with `l₀ > 0`, the life-table probability
of strict survival past any age `x ≤ n` is `lₓ / l₀`, including zero when `lₓ = 0`. -/
theorem prob_survives (x : Fin (n + 1)) : L.law.toMeasure.real (survives x) =
    L.survivors x / L.survivors 0 := by
  induction x using Fin.induction with
  | zero =>
    have h : survives (0 : Fin (n + 1)) = Set.univ := by ext i; simp [survives]
    simp [h, L.initial_pos.ne']
  | succ j ih =>
    have hsplit : survives j.castSucc = {j.castSucc} ∪ survives j.succ := by
      ext i
      simp only [survives, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff,
        Fin.val_castSucc, Fin.val_succ]
      omega
    have hd : Disjoint ({j.castSucc} : Set _) (survives j.succ) := by simp [survives]
    rw [hsplit, measureReal_union hd (Set.to_countable _).measurableSet, measureReal_def,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), L.law_death, sub_div] at ih
    linarith

/-- Let `l₀ ≥ ⋯ ≥ lₙ ≥ 0` be real counts with `l₀ > 0`. Under the law assigning each
interval `(j, j + 1]` mass `(lⱼ - lⱼ₊₁) / l₀` and survival beyond `n` mass `lₙ / l₀`,
the conditional probability of strict survival past `x + k` given strict survival past `x`
is `lₓ₊ₖ / lₓ` whenever `x + k ≤ n` and `lₓ > 0`. Both ages and the lag are natural numbers. -/
theorem cond_survives (x k : ℕ) (h : x + k ≤ n) (hx : 0 < L.survivors ⟨x, by omega⟩) :
    (ProbabilityTheory.cond L.law.toMeasure (survives ⟨x, by omega⟩)).real
        (survives ⟨x + k, by omega⟩) =
      L.survivors ⟨x + k, by omega⟩ / L.survivors ⟨x, by omega⟩ := by
  let a : Fin (n + 1) := ⟨x, by omega⟩
  let b : Fin (n + 1) := ⟨x + k, by omega⟩
  have hba : survives b ⊆ survives a := fun _ hi ↦ lt_of_le_of_lt (Nat.le_add_right x k) hi
  rw [measureReal_def, ProbabilityTheory.cond_apply (Set.to_countable (survives a)).measurableSet,
    Set.inter_eq_right.mpr hba, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (L.law.toMeasure.real (survives a))⁻¹ * L.law.toMeasure.real (survives b) = _
  rw [L.prob_survives, L.prob_survives]
  change (L.survivors a / L.survivors 0)⁻¹ * (L.survivors b / L.survivors 0) =
    L.survivors b / L.survivors a
  field_simp [L.initial_pos.ne', show L.survivors a ≠ 0 from hx.ne']

end FiniteLifeTable
end Domains.Biology.Demography
