/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The stationary law of a finite birth–death chain -/

open Finset Matrix

namespace ProbabilityTheory

/-- For a stationary vector, the total weighted rate across a cut in each direction is equal. -/
private theorem cut_flux {ι : Type*} [Fintype ι] {Q : Matrix ι ι ℝ} {π : ι → ℝ}
    (hQ : IsRateMatrix Q) (hπ : π ᵥ* Q = 0) (p : ι → Prop) [DecidablePred p] :
    (∑ i ∈ univ.filter p, ∑ j ∈ univ.filter (fun j => ¬p j), π i * Q i j) =
      ∑ i ∈ univ.filter p, ∑ j ∈ univ.filter (fun j => ¬p j), π j * Q j i := by
  let s := univ.filter p
  let u := univ.filter (fun i => ¬p i)
  have hrow (i : ι) : (∑ j ∈ s, π i * Q i j) + (∑ j ∈ u, π i * Q i j) = 0 := by
    dsimp [s, u]
    rw [sum_filter_add_sum_filter_not, ← mul_sum, hQ.sum_row i, mul_zero]
  have hcol (j : ι) : (∑ i ∈ s, π i * Q i j) + (∑ i ∈ u, π i * Q i j) = 0 := by
    dsimp [s, u]
    rw [sum_filter_add_sum_filter_not]
    exact congrFun hπ j
  have ha : (∑ i ∈ s, ∑ j ∈ s, π i * Q i j) + (∑ i ∈ s, ∑ j ∈ u, π i * Q i j) = 0 := by
    rw [← sum_add_distrib]
    simp only [hrow, sum_const_zero]
  have hb : (∑ j ∈ s, ∑ i ∈ s, π i * Q i j) + (∑ j ∈ s, ∑ i ∈ u, π i * Q i j) = 0 := by
    rw [← sum_add_distrib]
    simp only [hcol, sum_const_zero]
  rw [sum_comm (s := s) (t := s) (f := fun i j => π i * Q i j)] at ha
  change (∑ i ∈ s, ∑ j ∈ u, π i * Q i j) = ∑ i ∈ s, ∑ j ∈ u, π j * Q j i
  linarith only [ha, hb]

private theorem crossing_terms {K : ℕ} {Q : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ}
    (hband : ∀ i j, i ≠ j → i.val + 1 ≠ j.val → j.val + 1 ≠ i.val → Q i j = 0)
    (k : Fin K) {i j : Fin (K + 1)} (hi : i.val ≤ k.val) (hj : k.val < j.val)
    (hne : ¬ (i = k.castSucc ∧ j = k.succ)) : Q i j = 0 ∧ Q j i = 0 := by
  have hij : i ≠ j := by
    intro h
    rw [h] at hi
    omega
  have hback : j.val + 1 ≠ i.val := by omega
  have hforw : i.val + 1 ≠ j.val := by
    intro h
    apply hne
    constructor <;> apply Fin.ext <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
  exact ⟨hband i j hij hforw hback, hband j i hij.symm hback hforw⟩

private theorem sum_crossing {K : ℕ} (k : Fin K) (f : Fin (K + 1) → Fin (K + 1) → ℝ)
    (hf : ∀ i j, i.val ≤ k.val → k.val < j.val →
      ¬ (i = k.castSucc ∧ j = k.succ) → f i j = 0) :
    ∑ i ∈ univ.filter (fun i : Fin (K + 1) => i.val ≤ k.val),
      ∑ j ∈ univ.filter (fun j : Fin (K + 1) => ¬j.val ≤ k.val), f i j =
        f k.castSucc k.succ := by
  have hleft : k.castSucc ∈ univ.filter (fun i : Fin (K + 1) => i.val ≤ k.val) := by simp
  have hright : k.succ ∈ univ.filter (fun j : Fin (K + 1) => ¬j.val ≤ k.val) := by simp
  rw [sum_eq_single_of_mem k.castSucc hleft, sum_eq_single_of_mem k.succ hright]
  · intro j hj hne
    have hj' := Nat.lt_of_not_ge (mem_filter.mp hj).2
    exact hf _ _ (by simp) hj' (fun h => hne h.2)
  · intro i hi hne
    apply sum_eq_zero
    intro j hj
    exact hf _ _ (mem_filter.mp hi).2 (Nat.lt_of_not_ge (mem_filter.mp hj).2)
      (fun h => hne h.1)

private theorem adjacent_balance_of_stationary {K : ℕ}
    {Q : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ} {π : Fin (K + 1) → ℝ}
    (hQ : IsRateMatrix Q)
    (hband : ∀ i j, i ≠ j → i.val + 1 ≠ j.val → j.val + 1 ≠ i.val → Q i j = 0)
    (hπ : π ᵥ* Q = 0) (k : Fin K) :
    π k.castSucc * Q k.castSucc k.succ = π k.succ * Q k.succ k.castSucc := by
  have h := cut_flux hQ hπ (fun i => i.val ≤ k.val)
  rw [sum_crossing k (fun i j => π i * Q i j) (fun _ _ hi hj hn => by
    rw [(crossing_terms hband k hi hj hn).1, mul_zero]),
    sum_crossing k (fun i j => π j * Q j i) (fun _ _ hi hj hn => by
      rw [(crossing_terms hband k hi hj hn).2, mul_zero])] at h
  exact h

/-- The unnormalized weight at state `i`: multiply the ratio of the upward rate to the
reverse downward rate over the edges below `i`. The weight at state zero is one. -/
@[expose] public noncomputable def finiteBirthDeathWeight {K : ℕ}
    (Q : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ) (i : Fin (K + 1)) : ℝ :=
  ∏ k ∈ univ.filter (fun k : Fin K => k.val < i.val), Q k.castSucc k.succ / Q k.succ k.castSucc

private theorem finiteBirthDeathWeight_zero {K : ℕ}
    (Q : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ) : finiteBirthDeathWeight Q 0 = 1 := by
  simp [finiteBirthDeathWeight]

private theorem finiteBirthDeathWeight_succ {K : ℕ}
    (Q : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ) (k : Fin K) :
    finiteBirthDeathWeight Q k.succ =
      finiteBirthDeathWeight Q k.castSucc * (Q k.castSucc k.succ / Q k.succ k.castSucc) := by
  have hfilter : univ.filter (fun j : Fin K => j.val < k.succ.val) =
      insert k (univ.filter (fun j : Fin K => j.val < k.castSucc.val)) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.val_succ, Fin.val_castSucc]
    constructor
    · intro h
      by_cases he : j.val = k.val
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | h) <;> omega
  unfold finiteBirthDeathWeight
  rw [hfilter, prod_insert (by simp), mul_comm]

/-- **Stationary law of a finite birth–death chain.** Let `Q` be a rate matrix on
`{0, …, K}`, with jumps only between neighbors and strictly positive downward rates.
Put `w₀ = 1` and `wₙ = ∏ i < n, Q i (i + 1) / Q (i + 1) i`. The normalized weights
`πₙ = wₙ / ∑ᵢ wᵢ` give the unique probability vector satisfying `π Q = 0`. They are in
detailed balance and invariant under the transition semigroup. If an upward rate at `k`
vanishes, both the weights and the probabilities vanish strictly above `k`.

See K. Sigman, *Continuous-Time Markov Chains*, §1.13, item 2, for the balance equations
and product formula. -/
public theorem finite_birth_death_stationary_law {K : ℕ}
    {Q : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ} (hQ : IsRateMatrix Q)
    (hband : ∀ i j, i ≠ j → i.val + 1 ≠ j.val → j.val + 1 ≠ i.val → Q i j = 0)
    (hdeath : ∀ k : Fin K, 0 < Q k.succ k.castSucc) :
    let w := finiteBirthDeathWeight Q
    let π := fun i => w i / ∑ j, w j
    IsDetailedBalance π Q ∧ (∀ t, π ᵥ* ctmcTransition Q t = π) ∧
      (∀ ρ : Fin (K + 1) → ℝ, ((∀ i, 0 ≤ ρ i) ∧ (∑ i, ρ i) = 1 ∧ ρ ᵥ* Q = 0) ↔ ρ = π) ∧
      (∀ k : Fin K, Q k.castSucc k.succ = 0 →
        ∀ i : Fin (K + 1), k.val < i.val → w i = 0 ∧ π i = 0) := by
  intro w π
  have hstep (k : Fin K) : w k.succ =
      w k.castSucc * (Q k.castSucc k.succ / Q k.succ k.castSucc) :=
    finiteBirthDeathWeight_succ Q k
  have hzero : w 0 = 1 := finiteBirthDeathWeight_zero Q
  have hnonneg (i : Fin (K + 1)) : 0 ≤ w i := by
    apply prod_nonneg
    intro k _
    refine div_nonneg (hQ.nonneg_of_ne ?_) (hdeath k).le
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have htotal : 0 < ∑ i, w i := by
    have hlo := single_le_sum (fun i (_ : i ∈ univ) => hnonneg i) (mem_univ 0)
    rw [hzero] at hlo
    exact zero_lt_one.trans_le hlo
  have hwb (k : Fin K) : w k.castSucc * Q k.castSucc k.succ =
      w k.succ * Q k.succ k.castSucc := by
    rw [hstep, mul_assoc, div_mul_cancel₀ _ (ne_of_gt (hdeath k))]
  have hpb (k : Fin K) : π k.castSucc * Q k.castSucc k.succ =
      π k.succ * Q k.succ k.castSucc := by
    change (w k.castSucc / _) * _ = (w k.succ / _) * _
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, hwb]
  have hadj (i j : Fin (K + 1)) (h : i.val + 1 = j.val) : π i * Q i j = π j * Q j i := by
    let k : Fin K := ⟨i.val, by have hj := j.isLt; omega⟩
    have hi : k.castSucc = i := Fin.ext rfl
    have hj : k.succ = j := Fin.ext h
    simpa only [hi, hj] using hpb k
  have hdb : IsDetailedBalance π Q := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    by_cases hf : i.val + 1 = j.val
    · exact hadj i j hf
    by_cases hb : j.val + 1 = i.val
    · exact (hadj j i hb).symm
    rw [hband i j hij hf hb, hband j i (fun h => hij h.symm) hb hf, mul_zero, mul_zero]
  refine ⟨hdb, hdb.vecMul_ctmcTransition hQ.sum_row, ?_, ?_⟩
  · intro ρ
    constructor
    · rintro ⟨_, hsum, hρ⟩
      have hprop (i : Fin (K + 1)) : ρ i = w i * ρ 0 := by
        induction i using Fin.induction with
        | zero => rw [hzero, one_mul]
        | succ k ih =>
          apply mul_right_cancel₀ (ne_of_gt (hdeath k))
          calc
            ρ k.succ * Q k.succ k.castSucc = ρ k.castSucc * Q k.castSucc k.succ :=
              (adjacent_balance_of_stationary hQ hband hρ k).symm
            _ = (w k.castSucc * Q k.castSucc k.succ) * ρ 0 := by rw [ih, mul_right_comm]
            _ = (w k.succ * ρ 0) * Q k.succ k.castSucc := by rw [hwb]; ring
      have hs : (∑ i, w i) * ρ 0 = 1 := by
        rw [sum_mul, ← hsum]
        exact sum_congr rfl fun i _ => (hprop i).symm
      have hρ0 : ρ 0 = 1 / ∑ i, w i :=
        (eq_div_iff (ne_of_gt htotal)).2 (by rw [mul_comm, hs])
      funext i
      change ρ i = w i / ∑ j, w j
      rw [hprop i, hρ0, mul_one_div]
    · rintro rfl
      refine ⟨fun i => div_nonneg (hnonneg i) htotal.le, ?_, hdb.vecMul_eq_zero hQ.sum_row⟩
      change (∑ i, w i / ∑ j, w j) = 1
      rw [← sum_div, div_self (ne_of_gt htotal)]
  · intro k hk i hi
    have hwi : w i = 0 := by
      apply prod_eq_zero (i := k) (by simp [hi])
      rw [hk, zero_div]
    exact ⟨hwi, by change w i / _ = 0; rw [hwi, zero_div]⟩

end ProbabilityTheory
