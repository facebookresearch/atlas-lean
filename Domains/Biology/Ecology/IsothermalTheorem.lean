/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

/-!
# The isothermal theorem

The absorption equations on an irreducible doubly stochastic graph determine the Moran
fixation probability for a uniformly placed single mutant.

Sources: E. Lieberman, C. Hauert and M. A. Nowak, "Evolutionary dynamics on graphs", Nature 433
(2005) 312–316, p. 313 and eq. (1); P. Keller and M. Uğurlu, arXiv:2403.12598; K. Kaveh,
N. L. Komarova and M. Kohandel, R. Soc. Open Sci. (2015), arXiv:1411.4556.
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.IsothermalTheoremWanted

open Finset

/-- Fitness of vertex `i` when the mutants occupy `S`: `r` for a mutant, `1` for a resident. -/
def fitness {N : ℕ} (r : ℝ) (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  if i ∈ S then r else 1

/-- Total fitness `∑_i f_i` of the population when the mutants occupy `S`. -/
def totalFitness {N : ℕ} (r : ℝ) (S : Finset (Fin N)) : ℝ :=
  ∑ i, fitness r S i

/-- The mutant set after the individual at `i` places its offspring on vertex `j`. -/
def replace {N : ℕ} (S : Finset (Fin N)) (i j : Fin N) : Finset (Fin N) :=
  if i ∈ S then insert j S else S.erase j

/-- `φ` solves the **absorption equations** of the Moran process on the graph `W` with mutant
fitness `r`: `φ ∅ = 0`, `φ univ = 1`, and for every other mutant set `S`,
`φ(S) = ∑_{i,j} (f_i / ∑_k f_k) w_ij φ(S after i replaces j)`. -/
def IsFixationFunction {N : ℕ} (r : ℝ) (W : Matrix (Fin N) (Fin N) ℝ)
    (φ : Finset (Fin N) → ℝ) : Prop :=
  φ ∅ = 0 ∧ φ univ = 1 ∧ ∀ S : Finset (Fin N), S ≠ ∅ → S ≠ univ →
    φ S = ∑ i, ∑ j, fitness r S i / totalFitness r S * W i j * φ (replace S i j)

/-- The **Moran fixation probability** `ρ₁ = (1 - 1/r) / (1 - 1/r^N)` of a single mutant of
fitness `r` in a well-mixed population of size `N`. The formula is the fixation probability for
`r > 0`, `r ≠ 1` and `N ≥ 1`. The definition is total: at `r = 1` numerator and denominator
vanish and Lean's convention `0 / 0 = 0` gives `0`, not the neutral fixation probability `1/N`
(which is the limit as `r → 1`). -/
noncomputable def moranFixation (r : ℝ) (N : ℕ) : ℝ :=
  (1 - r⁻¹) / (1 - r⁻¹ ^ N)

private theorem fitness_pos {N : ℕ} (r : ℝ) (hr : 0 < r)
    (S : Finset (Fin N)) (i : Fin N) : 0 < fitness r S i := by
  unfold fitness
  split_ifs <;> positivity

private theorem totalFitness_pos {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (S : Finset (Fin N)) : 0 < totalFitness r S := by
  unfold totalFitness
  exact sum_pos' (fun i _ => (fitness_pos r hr S i).le)
    ⟨⟨0, hN⟩, mem_univ _, fitness_pos r hr S _⟩

private theorem transition_sum {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (W : Matrix (Fin N) (Fin N) ℝ) (hrow : ∀ i, ∑ j, W i j = 1)
    (S : Finset (Fin N)) :
    (∑ i, ∑ j, fitness r S i / totalFitness r S * W i j) = 1 := by
  simp_rw [← mul_sum, hrow, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul, ← totalFitness, mul_inv_cancel₀ (totalFitness_pos hN r hr S).ne']

private theorem power_replace {N : ℕ} (r : ℝ) (hr : 0 < r)
    (S : Finset (Fin N)) (i j : Fin N) :
    fitness r S i * (r⁻¹ ^ (replace S i j).card - r⁻¹ ^ S.card) =
      r⁻¹ ^ S.card * (r - 1) * ((if j ∈ S then 1 else 0) - (if i ∈ S then 1 else 0)) := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [fitness, replace, hi, hj]
  · simp only [fitness, replace, hi, hj, ite_true, ite_false, card_insert_of_notMem hj,
      pow_succ, zero_sub]
    linear_combination (r⁻¹ ^ S.card) * (mul_inv_cancel₀ hr.ne')
  · simp only [fitness, replace, hi, hj, ite_true, ite_false, one_mul, sub_zero, mul_one]
    have hc : S.card = (S.erase j).card + 1 := (card_erase_add_one hj).symm
    rw [hc, pow_succ]
    linear_combination -(r⁻¹ ^ (S.erase j).card) * (mul_inv_cancel₀ hr.ne')
  · simp [fitness, replace, hi, hj]

private theorem power_harmonic {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (W : Matrix (Fin N) (Fin N) ℝ) (hrow : ∀ i, ∑ j, W i j = 1)
    (hcol : ∀ j, ∑ i, W i j = 1) (S : Finset (Fin N)) :
    (∑ i, ∑ j, fitness r S i / totalFitness r S * W i j *
      r⁻¹ ^ (replace S i j).card) = r⁻¹ ^ S.card := by
  change Fin N → Fin N → ℝ at W
  have hbal : (∑ i, ∑ j, W i j *
      ((if j ∈ S then 1 else 0) - (if i ∈ S then 1 else 0))) = 0 := by
    simp_rw [mul_sub, sum_sub_distrib]
    rw [sum_comm (f := fun i j => W i j * (if j ∈ S then 1 else 0))]
    simp_rw [← sum_mul, hcol, one_mul]
    simp_rw [hrow, one_mul]
    exact sub_self _
  have hz : (∑ i, ∑ j, fitness r S i / totalFitness r S * W i j *
      (r⁻¹ ^ (replace S i j).card - r⁻¹ ^ S.card)) = 0 := by
    calc
      _ = ∑ i, ∑ j, (r⁻¹ ^ S.card * (r - 1) / totalFitness r S) *
          (W i j * ((if j ∈ S then 1 else 0) - (if i ∈ S then 1 else 0))) := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        linear_combination (W i j / totalFitness r S) * (power_replace r hr S i j)
      _ = 0 := by simp_rw [← mul_sum, hbal, mul_zero]
  have hc : (∑ i, ∑ j, fitness r S i / totalFitness r S * W i j *
      r⁻¹ ^ S.card) = r⁻¹ ^ S.card := by
    simp_rw [← sum_mul]
    rw [transition_sum hN r hr W hrow S, one_mul]
  simp_rw [mul_sub, sum_sub_distrib] at hz
  linarith

private theorem formula_fixation {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≠ 1) (W : Matrix (Fin N) (Fin N) ℝ)
    (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1) :
    IsFixationFunction r W (fun S => (1 - r⁻¹ ^ S.card) / (1 - r⁻¹ ^ N)) := by
  change Fin N → Fin N → ℝ at W
  have hd : 1 - r⁻¹ ^ N ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hp : r⁻¹ ^ N = 1 := h.symm
    rw [pow_eq_one_iff_of_nonneg (inv_nonneg.mpr hr.le) hN.ne', inv_eq_one] at hp
    exact hr1 hp
  refine ⟨by simp, ?_, fun S _ _ => ?_⟩
  · simp only [card_univ, Fintype.card_fin]
    exact div_self hd
  · have hsum := transition_sum hN r hr W hrow S
    have hpow := power_harmonic hN r hr W hrow hcol S
    have he : (∑ i, ∑ j, fitness r S i / totalFitness r S * W i j *
        ((1 - r⁻¹ ^ (replace S i j).card) / (1 - r⁻¹ ^ N))) =
        ((∑ i, ∑ j, fitness r S i / totalFitness r S * W i j) -
          (∑ i, ∑ j, fitness r S i / totalFitness r S * W i j *
            r⁻¹ ^ (replace S i j).card)) / (1 - r⁻¹ ^ N) := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, ← sum_mul]
      congr 1
      simp_rw [mul_sub, mul_one, sum_sub_distrib]
    rw [he, hsum, hpow]

private theorem outgoing {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (hW : ∀ i j, 0 ≤ W i j) (hirr : ∀ i j, ∃ k : ℕ, 0 < (W ^ k) i j)
    (S : Finset (Fin N)) (hS : S ≠ ∅) (hU : S ≠ univ) :
    ∃ i ∈ S, ∃ j, j ∉ S ∧ 0 < W i j := by
  classical
  by_contra! h
  have hz (i : Fin N) (hi : i ∈ S) (j : Fin N) (hj : j ∉ S) : W i j = 0 :=
    le_antisymm (h i hi j hj) (hW i j)
  have hp (k : ℕ) : ∀ i ∈ S, ∀ j, j ∉ S → (W ^ k) i j = 0 := by
    induction k with
    | zero =>
      intro i hi j hj
      have hij : i ≠ j := by rintro rfl; exact hj hi
      simp [hij]
    | succ k ih =>
      intro i hi j hj
      rw [pow_succ, Matrix.mul_apply]
      apply sum_eq_zero
      intro a _
      by_cases ha : a ∈ S
      · rw [hz a ha j hj, mul_zero]
      · rw [ih i hi a ha, zero_mul]
  obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hS
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra! hall
    exact hU (eq_univ_of_forall hall)
  obtain ⟨k, hk⟩ := hirr i j
  rw [hp k i hi j hj] at hk
  exact lt_irrefl _ hk

private theorem harmonic_nonpos {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) (hirr : ∀ i j, ∃ k : ℕ, 0 < (W ^ k) i j)
    (f : Finset (Fin N) → ℝ) (h0 : f ∅ = 0) (hU : f univ = 0)
    (hf : ∀ S : Finset (Fin N), S ≠ ∅ → S ≠ univ →
      f S = ∑ i, ∑ j, fitness r S i / totalFitness r S * W i j * f (replace S i j)) :
    ∀ S, f S ≤ 0 := by
  classical
  obtain ⟨A, _, hA⟩ := exists_max_image (univ : Finset (Finset (Fin N))) f univ_nonempty
  let K := (univ : Finset (Finset (Fin N))).filter (fun S => f S = f A)
  have hK : K.Nonempty := ⟨A, by simp [K]⟩
  obtain ⟨B, hB, hcard⟩ := exists_max_image K Finset.card hK
  have heq : f B = f A := (mem_filter.mp hB).2
  have hmax (S : Finset (Fin N)) : f S ≤ f B := by simpa only [heq] using hA S (mem_univ S)
  have hle : f B ≤ 0 := by
    by_contra! hpos
    have hB0 : B ≠ ∅ := by intro h; rw [h, h0] at hpos; exact lt_irrefl _ hpos
    have hBU : B ≠ univ := by intro h; rw [h, hU] at hpos; exact lt_irrefl _ hpos
    let p (i j : Fin N) := fitness r B i / totalFitness r B * W i j
    have hp (i j : Fin N) : 0 ≤ p i j :=
      mul_nonneg (div_nonneg (fitness_pos r hr B i).le (totalFitness_pos hN r hr B).le) (hW i j)
    have hs : (∑ i, ∑ j, p i j) = 1 := transition_sum hN r hr W hrow B
    have hh : f B = ∑ i, ∑ j, p i j * f (replace B i j) := hf B hB0 hBU
    have hn (i j : Fin N) : 0 ≤ p i j * (f B - f (replace B i j)) :=
      mul_nonneg (hp i j) (sub_nonneg.mpr (hmax _))
    have hz : (∑ i, ∑ j, p i j * (f B - f (replace B i j))) = 0 := by
      simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
      rw [hs, one_mul, ← hh, sub_self]
    obtain ⟨i, hi, j, hj, hij⟩ := outgoing W hW hirr B hB0 hBU
    have hzi : (∑ j, p i j * (f B - f (replace B i j))) = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg (fun j _ => hn i j))).mp hz i (mem_univ i)
    have hzij : p i j * (f B - f (replace B i j)) = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp hzi j (mem_univ j)
    have hpij : 0 < p i j :=
      mul_pos (div_pos (fitness_pos r hr B i) (totalFitness_pos hN r hr B)) hij
    have he : f (insert j B) = f B := by
      have hd := (mul_eq_zero.mp hzij).resolve_left hpij.ne'
      simpa [replace, hi] using (sub_eq_zero.mp hd).symm
    have hm : insert j B ∈ K := by simp [K, he, heq]
    have hc := hcard (insert j B) hm
    rw [card_insert_of_notMem hj] at hc
    omega
  intro S
  exact (hmax S).trans hle

private theorem fixation_le {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) (hirr : ∀ i j, ∃ k : ℕ, 0 < (W ^ k) i j)
    (φ ψ : Finset (Fin N) → ℝ) (hφ : IsFixationFunction r W φ)
    (hψ : IsFixationFunction r W ψ) (S : Finset (Fin N)) : φ S ≤ ψ S := by
  have h := harmonic_nonpos hN r hr W hW hrow hirr (fun S => φ S - ψ S)
    (by rw [hφ.1, hψ.1, sub_self]) (by rw [hφ.2.1, hψ.2.1, sub_self])
    (fun S h0 hU => by
      rw [hφ.2.2 S h0 hU, hψ.2.2 S h0 hU]
      simp_rw [mul_sub, sum_sub_distrib]) S
  exact sub_nonpos.mp h

/-- **Isothermal theorem, "if" direction** (Lieberman, Hauert and Nowak 2005). Let `N > 0`,
`r > 0`, `r ≠ 1`, and let `W` be a real `N × N` matrix with nonnegative entries, every row sum
`1` (stochastic) and every column sum `1` (all temperatures `T_j = 1`: doubly stochastic), that
is irreducible (for all `i, j` some power `W^k` has `(W^k)_{ij} > 0`). Then for every `φ` solving
the absorption equations of the Moran process on `W` with fitness `r`, the fixation probability
of a single mutant at a uniformly random vertex, `(∑_v φ {v}) / N`, equals
`(1 - 1/r) / (1 - 1/r^N)`.

Sources: Lieberman, Hauert and Nowak (2005), p. 313; Keller and Uğurlu, arXiv:2403.12598. -/
public theorem average_fixation_eq_moranFixation {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≠ 1) (W : Matrix (Fin N) (Fin N) ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1)
    (hirr : ∀ i j, ∃ k : ℕ, 0 < (W ^ k) i j)
    (φ : Finset (Fin N) → ℝ) (hφ : IsFixationFunction r W φ) :
    (∑ v, φ {v}) / N = moranFixation r N := by
  let ψ : Finset (Fin N) → ℝ := fun S => (1 - r⁻¹ ^ S.card) / (1 - r⁻¹ ^ N)
  have hψ : IsFixationFunction r W ψ := formula_fixation hN r hr hr1 W hrow hcol
  have hv (v : Fin N) : φ {v} = moranFixation r N := by
    have he := le_antisymm (fixation_le hN r hr W hW hrow hirr φ ψ hφ hψ {v})
      (fixation_le hN r hr W hW hrow hirr ψ φ hψ hφ {v})
    simpa only [ψ, card_singleton, pow_one, moranFixation] using he
  simp_rw [hv, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')

end WantedExt.Biology.Ecology.IsothermalTheoremWanted
