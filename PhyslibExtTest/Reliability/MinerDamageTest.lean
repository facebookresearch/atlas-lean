/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Reliability.MinerDamage
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Reliability.MinerDamage`

Counts `(1, 3)` over lives `(4, 6)` give damage `3 / 4`; three records with a
half cycle aggregate to the same damage class-wise and record-wise (`23 / 24`).
Doubling only the counts gives `3 / 2`, with no cap at `1`. Controls drop each
nonnegativity, ordering, positivity and zero-life premise, and pavement-shaped
records split damage by season.
-/

@[expose] public section

namespace PhyslibExtTest.Reliability.MinerDamageTest

open _root_.Reliability

variable {ι κ : Type*}

#print axioms Reliability.minerDamage_cycleClassCounts
#print axioms Reliability.minerDamage_unit_change
#print axioms Reliability.minerDamage_nonneg_and_eq_zero_iff
#print axioms Reliability.bareSum_at_zero_life_misreports
#print axioms Reliability.minerDamage_mono


private lemma lives46_pos : ∀ i, (0 : ℝ) < (![4, 6] : Fin 2 → ℝ) i
    := by intro i; fin_cases i <;> norm_num

-- Definitional readings
example (n N : ι → ℝ) [Fintype ι] (hN : ∀ i, 0 < N i) : minerDamage n N hN = ∑ i, n i / N i := rfl
example [Fintype κ] [DecidableEq ι] (g : κ → ι) (r : κ → ℝ) (i : ι) :
    cycleClassCounts g r i = ∑ k ∈ Finset.univ.filter (fun k => g k = i), r k := rfl
-- Proof irrelevance of the guard
example [Fintype ι] (n N : ι → ℝ) (h1 h2 : ∀ i, 0 < N i) : minerDamage n N h1 = minerDamage n N h2
    := rfl

-- Witness: nonzero witness below 1: counts (1,3), lives (4,6), D = 3/4
example : minerDamage (![1, 3] : Fin 2 → ℝ) (![4, 6] : Fin 2 → ℝ) lives46_pos = 3 / 4 := by
  simp only [minerDamage, Fin.sum_univ_two]; norm_num

-- Witness: records Fin 3, counts (1, 2, 3/2), classes (0,1,0), lives (4,6)
example : cycleClassCounts (![0, 1, 0] : Fin 3 → Fin 2) (![1, 2, 3/2] : Fin 3 → ℝ) 0 = 5 / 2 := by
  simp [cycleClassCounts, Finset.sum_filter, Fin.sum_univ_three]; norm_num
example : cycleClassCounts (![0, 1, 0] : Fin 3 → Fin 2) (![1, 2, 3/2] : Fin 3 → ℝ) 1 = 2 := by
  simp [cycleClassCounts, Finset.sum_filter, Fin.sum_univ_three]
example : minerDamage (![1, 2, 3/2] : Fin 3 → ℝ)
    (fun k => (![4, 6] : Fin 2 → ℝ) ((![0, 1, 0] : Fin 3 → Fin 2) k))
    (fun _k => lives46_pos _) = 23 / 24 := by
  simp [minerDamage, Fin.sum_univ_three]; norm_num
example : minerDamage (cycleClassCounts (![0, 1, 0] : Fin 3 → Fin 2) (![1, 2, 3/2] : Fin 3 → ℝ))
    (![4, 6] : Fin 2 → ℝ) lives46_pos = 23 / 24 := by
  rw [(minerDamage_cycleClassCounts _ (by intro k; fin_cases k <;> norm_num) lives46_pos).2.2]
  simp [minerDamage, Fin.sum_univ_three]; norm_num

-- Witness: counts doubled: D = 3/2 > 1 (no cap); counts and lives doubled: 3/4
example : minerDamage (fun i => 2 * (![1, 3] : Fin 2 → ℝ) i) (![4, 6] : Fin 2 → ℝ)
    lives46_pos = 3 / 2
    := by
  simp only [minerDamage, Fin.sum_univ_two]; norm_num
example : minerDamage (fun i => 2 * (![1, 3] : Fin 2 → ℝ) i) (fun i => 2 * (![4, 6] : Fin 2 → ℝ) i)
    (fun i => mul_pos two_pos (lives46_pos i)) = 3 / 4 := by
  simp only [minerDamage, Fin.sum_univ_two]; norm_num

-- Witness: zero cycles: D = 0
example : minerDamage (![0, 0] : Fin 2 → ℝ) (![4, 6] : Fin 2 → ℝ) lives46_pos = 0 := by
  simp [minerDamage, Fin.sum_univ_two]

-- Witness: strict instance of T5: (2,3) ≥ (1,3), lives (2,6) ≤ (4,6): 3/4 < 3/2
example : minerDamage (![1, 3] : Fin 2 → ℝ) (![4, 6] : Fin 2 → ℝ) lives46_pos = 3 / 4 ∧
    minerDamage (![2, 3] : Fin 2 → ℝ) (![2, 6] : Fin 2 → ℝ)
      (by intro i; fin_cases i <;> norm_num) = 3 / 2 := by
  constructor <;> simp only [minerDamage, Fin.sum_univ_two] <;> norm_num

-- Empty spectrum: empty spectrum: D = 0
example (n N : Fin 0 → ℝ) (hN : ∀ i, 0 < N i) : minerDamage n N hN = 0 := by
  simp [minerDamage]

-- Consumers can use the unit and monotonicity results with their own guard proofs
example [Fintype ι] {c : ℝ} (hc : 0 < c) (n : ι → ℝ) {N : ι → ℝ} (hN : ∀ i, 0 < N i)
    (h' : ∀ i, 0 < c * N i) :
    minerDamage (fun i => c * n i) (fun i => c * N i) h' = minerDamage n N hN :=
  (minerDamage_unit_change hc n hN).1
example [Fintype ι] {n n' N : ι → ℝ} (hn : ∀ i, 0 ≤ n i) (hnn' : ∀ i, n i ≤ n' i)
    (hN : ∀ i, 0 < N i) : minerDamage n N hN ≤ minerDamage n' N hN :=
  minerDamage_mono hn hnn' hN (fun _ => le_rfl)
example [Fintype ι] {n N N' : ι → ℝ} (hn : ∀ i, 0 ≤ n i) (hN : ∀ i, 0 < N i)
    (hN' : ∀ i, 0 < N' i) (hNN' : ∀ i, N' i ≤ N i) : minerDamage n N hN ≤ minerDamage n N' hN' :=
  minerDamage_mono hn (fun _ => le_rfl) hN' hNN'

-- Control: `hr` needed for conjunct 1: one record with count -1 gives class count -1
example : ¬ ∀ r : Fin 1 → ℝ, ∀ i, 0 ≤ cycleClassCounts (fun _ => (0 : Fin 1)) r i := by
  intro h
  have := h (fun _ => -1) 0
  simp [cycleClassCounts] at this
  norm_num at this

-- Control: `hn` needed for (D = 0 → no cycles): counts (1,-1), lives (1,1)
example : minerDamage (![1, -1] : Fin 2 → ℝ) (![1, 1] : Fin 2 → ℝ)
      (by intro i; fin_cases i <;> norm_num) = 0 ∧ ¬ ∀ i, (![1, -1] : Fin 2 → ℝ) i = 0 := by
  refine ⟨by simp [minerDamage, Fin.sum_univ_two], fun h => by simpa using h 0⟩
-- Control: `hn` needed for 0 ≤ D: count -1, life 2 gives -1/2
example : minerDamage (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => 2) (fun _ => two_pos) = -1 / 2 := by
  norm_num [minerDamage]

-- Control: `hj` needed: lives (4,6), count at class 0 moved 1 -> 5 changes the bare sum 3/4 -> 7/4
example : (∑ i, Function.update (![1, 3] : Fin 2 → ℝ) 0 5 i / (![4, 6] : Fin 2 → ℝ) i) = 7 / 4 ∧
    (∑ i, (![1, 3] : Fin 2 → ℝ) i / (![4, 6] : Fin 2 → ℝ) i) = 3 / 4 := by
  constructor <;> simp [Fin.sum_univ_two, Function.update_apply] <;> norm_num

-- Zero life: the guarded sum cannot be formed; the bare sum misreports
example : ¬ ∀ i : Fin 2, (0 : ℝ) < (![0, 6] : Fin 2 → ℝ) i := fun h => by simpa using h 0
example : (∑ i, (![5, 3] : Fin 2 → ℝ) i / (![0, 6] : Fin 2 → ℝ) i) = 1 / 2 ∧
    (∑ i, (![0, 3] : Fin 2 → ℝ) i / (![0, 6] : Fin 2 → ℝ) i) = 1 / 2 := by
  constructor <;> simp [Fin.sum_univ_two] <;> norm_num
example : (∑ i, (![5, 0] : Fin 2 → ℝ) i / (![0, 6] : Fin 2 → ℝ) i) = 0 ∧
    ¬ ∀ i, (![5, 0] : Fin 2 → ℝ) i = 0 := by
  refine ⟨by simp [Fin.sum_univ_two], fun h => by simpa using h 0⟩

-- Control: `hn` needed: n = n' = -1, N = 2, N' = 1 gives -1/2 > -1
example : ¬ (minerDamage (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => 2) (fun _ => two_pos) ≤
    minerDamage (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => 1) (fun _ => one_pos)) := by
  norm_num [minerDamage]
-- Control: `hnn'` needed: n = 1, n' = 0, N = N' = 1
example : ¬ (minerDamage (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) (fun _ => one_pos) ≤
    minerDamage (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1) (fun _ => one_pos)) := by
  simp [minerDamage]
-- Control: `hNN'` needed: N = 1, N' = 2, n = n' = 1 gives 1 > 1/2
example : ¬ (minerDamage (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) (fun _ => one_pos) ≤
    minerDamage (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 2) (fun _ => two_pos)) := by
  simp [minerDamage]; norm_num

-- Control: at c = 0 the bare-sum analogue of conjunct 1 fails (the hc guard is not cosmetic)
example : (∑ _i : Fin 1, ((0 : ℝ) * 1) / (0 * 1)) ≠ ∑ _i : Fin 1, (1 : ℝ) / 1 := by simp

-- Integration: reordering records leaves class counts unchanged
example [Fintype κ] [DecidableEq ι] (g : κ → ι) (r : κ → ℝ) (σ : κ ≃ κ) :
    cycleClassCounts (g ∘ σ) (r ∘ σ) = cycleClassCounts g r := by
  funext i
  simp only [cycleClassCounts, Finset.sum_filter, Function.comp_apply]
  exact Equiv.sum_comp σ (fun k => if g k = i then r k else 0)

-- Integration: block additivity in the counts
example [Fintype ι] (n₁ n₂ N : ι → ℝ) (hN : ∀ i, 0 < N i) :
    minerDamage (n₁ + n₂) N hN = minerDamage n₁ N hN + minerDamage n₂ N hN := by
  simp only [minerDamage, Pi.add_apply, add_div, Finset.sum_add_distrib]

-- Integration: merging classes of equal life (lives (4,6,4) on Fin 3 merged to (4,6) on Fin 2)
example (n : Fin 3 → ℝ) (hn : ∀ k, 0 ≤ n k) :
    minerDamage (cycleClassCounts (![0, 1, 0] : Fin 3 → Fin 2) n) (![4, 6] : Fin 2 → ℝ)
      lives46_pos =
      minerDamage n (![4, 6, 4] : Fin 3 → ℝ) (by intro k; fin_cases k <;> norm_num) := by
  rw [(minerDamage_cycleClassCounts _ hn lives46_pos).2.2]
  simp only [minerDamage, Fin.sum_univ_three]
  simp

-- Integration: pavement-shaped records (axle group × season), D split by season
example {A S : Type*} [Fintype A] [Fintype S] [DecidableEq A] (r : A × S → ℝ)
    (hr : ∀ k, 0 ≤ r k) (N : A → ℝ) (hN : ∀ a, 0 < N a) :
    minerDamage (cycleClassCounts Prod.fst r) N hN = ∑ s, minerDamage (fun a => r (a, s)) N hN := by
  rw [(minerDamage_cycleClassCounts Prod.fst hr hN).2.2]
  simp only [minerDamage]
  exact Fintype.sum_prod_type_right _

end PhyslibExtTest.Reliability.MinerDamageTest
