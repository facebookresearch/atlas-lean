/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Computability.AkraBazzi.RecurrenceFamilies

/-!
# Constant-shift transfer checks
-/

open Filter Asymptotics Finset Real
open scoped Topology

open AkraBazziRecurrence

#check @AkraBazziRecurrence.shift

variable {α : Type*} [Fintype α] [Nonempty α]
variable {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}

noncomputable example (R : AkraBazziRecurrence T g a b r)
    (hT : ∀ n < R.n₀, 0 < T n + 2)
    (hg : ∀ x ≥ 0, 0 ≤ g x + 2 * (1 - ∑ i, a i))
    (hgpoly : AkraBazziRecurrence.GrowsPolynomially (fun x => g x + 2 * (1 - ∑ i, a i))) :
    AkraBazziRecurrence (fun n => T n + 2) (fun x => g x + 2 * (1 - ∑ i, a i)) a b r :=
  R.shift 2 hT hg hgpoly

example (R : AkraBazziRecurrence T g a b r) (c : ℝ)
    (hf' : 0 ≤ᶠ[atTop] g) (hg' : 0 ≤ᶠ[atTop] fun _ : ℝ => c * (1 - ∑ i, a i)) :
    AkraBazziRecurrence.GrowsPolynomially (fun x => g x + c * (1 - ∑ i, a i)) :=
  AkraBazziRecurrence.GrowsPolynomially.add R.g_grows_poly growsPolynomially_const hf' hg'

#check @AkraBazziRecurrence.ofFloorCeilFamily

noncomputable example {T : ℕ → ℝ} {g : ℝ → ℝ} {a d : Fin 2 → ℝ} {n₀ : ℕ}
    (ha : ∀ i, 0 < a i) (hd : ∀ i, 1 < d i) (hn₀ : 0 < n₀)
    (hcut : ∀ i, d i / (d i - 1) ≤ (n₀ : ℝ))
    (hgrow : AkraBazziRecurrence.GrowsPolynomially g)
    (hg0 : ∀ x ≥ 0, 0 ≤ g x)
    (hbase : ∀ n < n₀, 0 < T n)
    (hrec : ∀ n, n₀ ≤ n →
      T n = (∑ i, a i * T ⌊(n : ℝ) / d i⌋₊)
        + (∑ i, a i * T ⌈(n : ℝ) / d i⌉₊) + g n) :
    AkraBazziRecurrence T g (Sum.elim a a)
      (Sum.elim (fun i => (d i)⁻¹) (fun i => (d i)⁻¹))
      (Sum.elim (fun i n => ⌊(n : ℝ) / d i⌋₊) (fun i n => ⌈(n : ℝ) / d i⌉₊)) :=
  AkraBazziRecurrence.ofFloorCeilFamily n₀ ha hd hn₀ hcut hgrow hg0 hbase hrec

/-! ## Boundary checks -/

/-- **One-branch cost.** Well-founded iteration of `r` below `N`, charging `g` per step. -/
private noncomputable def oneBranchCost (g : ℝ → ℝ) (r : ℕ → ℕ) (N : ℕ)
    (shrink : ∀ n, N ≤ n → r n < n) (n : ℕ) : ℝ :=
  if _hn : n < N then 1 else oneBranchCost g r N shrink (r n) + g n
termination_by n
decreasing_by
  apply shrink
  omega

/-- **Base unfolding.** Below `N` the cost is `1`. -/
private lemma oneBranchCost_base (g : ℝ → ℝ) (r : ℕ → ℕ) (N : ℕ)
    (shrink : ∀ n, N ≤ n → r n < n) (n : ℕ) (hn : n < N) :
    oneBranchCost g r N shrink n = 1 := by
  rw [oneBranchCost, dite_eq_left hn]

/-- **Step unfolding.** At or above `N` the cost adds `g` to the child cost. -/
private lemma oneBranchCost_step (g : ℝ → ℝ) (r : ℕ → ℕ) (N : ℕ)
    (shrink : ∀ n, N ≤ n → r n < n) (n : ℕ) (hn : N ≤ n) :
    oneBranchCost g r N shrink n = oneBranchCost g r N shrink (r n) + g n := by
  rw [oneBranchCost, dite_eq_right (not_lt_of_ge hn)]

/-- **No zero recurrence.** A zero solution contradicts positivity below `n₀`. -/
private theorem no_zero_recurrence {T : ℕ → ℝ} (hT : T = 0)
    (R : AkraBazziRecurrence T (0 : ℝ → ℝ) a b r) : False := by
  have h0 := R.T_gt_zero' 0 R.n₀_gt_zero
  simp only [hT, Pi.zero_apply, lt_irrefl] at h0

/-- **Half-step logarithmic growth.** Unit toll with halving is `Θ` of `log`. -/
private theorem half_step_theta_log :
    oneBranchCost (fun _ => 1) (fun n => ⌊(n : ℝ) / 2⌋₊) 1 (fun n hn => by
      apply (Nat.floor_lt (div_nonneg (Nat.cast_nonneg n) (by norm_num))).2
      exact div_lt_self (by exact_mod_cast hn) (by norm_num))
      =Θ[atTop] (fun n : ℕ => log n) := by
  have shrinkWit : ∀ (n : ℕ), 1 ≤ n → (fun n => ⌊(n : ℝ) / 2⌋₊) n < n := by
    intro n hn
    apply (Nat.floor_lt (div_nonneg (Nat.cast_nonneg n) (by norm_num))).2
    exact div_lt_self (by exact_mod_cast hn) (by norm_num)
  have hg0 : ∀ x ≥ (0 : ℝ), 0 ≤ (fun _ : ℝ => (1 : ℝ)) x := fun _ _ => zero_le_one
  have hg : (fun _ : ℝ => (1 : ℝ)) =Θ[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
    simpa only [rpow_zero] using isTheta_rfl
  have hbase : ∀ n < 1,
      0 < oneBranchCost (fun _ : ℝ => (1 : ℝ)) (fun n => ⌊(n : ℝ) / 2⌋₊) 1
        shrinkWit n := by
    intro n hn
    have h := oneBranchCost_base (fun _ : ℝ => (1 : ℝ)) (fun n => ⌊(n : ℝ) / 2⌋₊)
      1 shrinkWit n hn
    rw [h]
    exact zero_lt_one
  have hrec : ∀ n, 1 ≤ n →
      oneBranchCost (fun _ : ℝ => (1 : ℝ)) (fun n => ⌊(n : ℝ) / 2⌋₊) 1
          shrinkWit n
        = 1 * oneBranchCost (fun _ : ℝ => (1 : ℝ)) (fun n => ⌊(n : ℝ) / 2⌋₊) 1
            shrinkWit ⌊(n : ℝ) / 2⌋₊ + (1 : ℝ) := by
    intro n hn
    have h := oneBranchCost_step (fun _ : ℝ => (1 : ℝ)) (fun n => ⌊(n : ℝ) / 2⌋₊)
      1 shrinkWit n hn
    simpa only [one_mul] using h
  have R := AkraBazziRecurrence.ofFloor (a := 1) (b := 2) (c := 0) 1 (by norm_num)
    (by norm_num) (by decide) hg0 hg hbase hrec
  simpa only [rpow_zero, one_mul] using R.master_eq (by norm_num) (by norm_num) hg
    (by simp)
