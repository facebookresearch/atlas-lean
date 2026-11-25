/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.TetranacciSequence
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The Brocard–Ramanujan equation has no Tetranacci solutions

This module proves that $m! + 1$ is never the square of a Tetranacci number.
The proof bounds the $2$-adic valuation of $Q_n^2 - 1$ by lifting the
$5$-step shift of the two-sided Tetranacci sequence, and combines this with the
growth of the sequence and the $2$-adic valuation of factorials to reduce to a
finite check.
-/

namespace MetaMathlibExt

namespace brocardRamanujan_not_tetranacci

open Matrix

/-- Backward half of the two-sided Tetranacci sequence. -/
private def tetranacciBackward : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => -1
  | 3 => 0
  | m + 4 =>
      tetranacciBackward m - tetranacciBackward (m + 1) - tetranacciBackward (m + 2) -
        tetranacciBackward (m + 3)

/-- The two-sided Tetranacci sequence, extended to negative indices by the
recurrence solved for its lowest term. -/
private def tetranacciInt : ℤ → ℤ
  | .ofNat n => (tetranacci n : ℤ)
  | .negSucc m => tetranacciBackward (m + 1)

private theorem tetranacciInt_nat (n : ℕ) :
    tetranacciInt (n : ℤ) = (tetranacci n : ℤ) := rfl

private theorem tetranacciInt_add_four (n : ℤ) :
    tetranacciInt (n + 4) =
      tetranacciInt (n + 3) + tetranacciInt (n + 2) + tetranacciInt (n + 1) +
        tetranacciInt n := by
  cases n with
  | ofNat n =>
      change (tetranacci (n + 4) : ℤ) =
        (tetranacci (n + 3) : ℤ) + (tetranacci (n + 2) : ℤ) + (tetranacci (n + 1) : ℤ) +
          (tetranacci n : ℤ)
      have h : tetranacci (n + 4) =
          tetranacci (n + 3) + tetranacci (n + 2) + tetranacci (n + 1) + tetranacci n := rfl
      rw [h]; push_cast; ring
  | negSucc n =>
      rcases n with _ | _ | _ | _ | n
      · rfl
      · rfl
      · rfl
      · rfl
      · change tetranacciBackward (n + 1) =
          tetranacciBackward (n + 2) + tetranacciBackward (n + 3) +
            tetranacciBackward (n + 4) + tetranacciBackward (n + 5)
        have hrec : tetranacciBackward (n + 5) =
            tetranacciBackward (n + 1) - tetranacciBackward (n + 2) -
              tetranacciBackward (n + 3) - tetranacciBackward (n + 4) := by
          rw [show n + 5 = (n + 1) + 4 by omega, tetranacciBackward]
        rw [hrec]
        ring

private abbrev Mat := Matrix (Fin 4) (Fin 4) ℤ

private def companion : Mat := !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 1, 1, 1]

private def state (n : ℤ) : Fin 4 → ℤ :=
  ![tetranacciInt n, tetranacciInt (n + 1), tetranacciInt (n + 2), tetranacciInt (n + 3)]

private theorem state_step (n : ℤ) : state (n + 1) = companion *ᵥ state n := by
  ext i
  fin_cases i
  · simp [companion, state, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · simp [companion, state, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      show n + 1 + 1 = n + 2 by omega]
  · simp [companion, state, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      show n + 1 + 2 = n + 3 by omega]
  · simp [companion, state, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      show n + 1 + 1 = n + 2 by omega, show n + 1 + 2 = n + 3 by omega,
      show n + 1 + 3 = n + 4 by omega, tetranacciInt_add_four]; ring

private theorem state_shift (n : ℤ) (d : ℕ) :
    state (n + d) = companion ^ d *ᵥ state n := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.cast_succ, ← add_assoc, state_step, ih, Matrix.mulVec_mulVec, pow_succ']

/-- The first-order part of the $5$-step shift. -/
private def slopeMatrix : Mat :=
  !![0, 1, 1, 1; 1, 1, 2, 2; 2, 3, 3, 4; 4, 6, 7, 7]

/-- The first-order part of the $10$-step shift. -/
private def slopeMatrixOne : Mat :=
  !![7, 11, 13, 14; 14, 21, 25, 27; 27, 41, 48, 52; 52, 79, 93, 100]

/-- The first-order part of the $20$-step shift. -/
private def slopeMatrixTwo : Mat :=
  !![2571, 3905, 4597, 4956; 4956, 7527, 8861, 9553; 9553, 14509, 17080, 18414;
    18414, 27967, 32923, 35494]

private theorem companion_pow_five :
    companion ^ 5 = 1 + (2 : ℤ) • slopeMatrix := by decide

private theorem companion_pow_five_two :
    (companion ^ 5) ^ 2 = 1 + (4 : ℤ) • slopeMatrixOne := by decide

private theorem companion_pow_five_four :
    (companion ^ 5) ^ 4 = 1 + (8 : ℤ) • slopeMatrixTwo := by decide

/-- Squaring a shift of the form $1 + 2d \bullet B$. -/
private theorem shift_sq (d : ℤ) (B : Mat) :
    (1 + (2 * d) • B) ^ 2 = 1 + (4 * d) • (B + d • (B * B)) := by
  calc (1 + (2 * d) • B) ^ 2
      = 1 + (2 * d) • B + ((2 * d) • B + ((2 * d) * (2 * d)) • (B * B)) := by
        simp only [sq, add_mul, mul_add, one_mul, mul_one, smul_mul, Matrix.mul_smul,
          smul_smul]
    _ = 1 + (4 * d) • B + ((4 * d) * d) • (B * B) := by
        have hX : ((2 : ℤ) * d) • B + ((2 : ℤ) * d) • B = (4 * d) • B := by
          rw [← add_smul]; congr 1; ring
        have hc : (2 * d) * (2 * d) = (4 * d) * d := by ring
        have key : (1 : Mat) + ((2 : ℤ) * d) • B + (((2 : ℤ) * d) • B + ((4 * d) * d) • (B * B))
            = 1 + (((2 : ℤ) * d) • B + ((2 : ℤ) * d) • B) + ((4 * d) * d) • (B * B) := by
          abel
        rw [hc, key, hX]
    _ = 1 + (4 * d) • (B + d • (B * B)) := by rw [smul_add, smul_smul, add_assoc]

/-- The $2^k$-fold $5$-step shift, for $k \ge 2$, is $1$ plus a multiple of
$2^{k+1}$ whose entries agree with `slopeMatrixTwo` modulo $4$. -/
private theorem companion_pow_two_pow (k : ℕ) (hk : 2 ≤ k) :
    ∃ B : Mat, (companion ^ 5) ^ (2 ^ k) = 1 + (2 : ℤ) ^ (k + 1) • B ∧
      ∀ i j, (B i j) % 4 = (slopeMatrixTwo i j) % 4 := by
  induction k, hk using Nat.le_induction with
  | base =>
      refine ⟨slopeMatrixTwo, ?_, ?_⟩
      · rw [show (2 : ℤ) ^ (2 + 1) = (8 : ℤ) by norm_num,
          show (2 : ℕ) ^ 2 = 4 by norm_num, companion_pow_five_four]
      · intro i j; rfl
  | succ k hk ih =>
      obtain ⟨B, hB, hB4⟩ := ih
      refine ⟨B + (2 : ℤ) ^ k • (B * B), ?_, ?_⟩
      · have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
        rw [hpow, pow_mul, hB]
        have hscalar : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := by rw [pow_succ]; ring
        rw [hscalar, shift_sq]
        have hsc : (4 : ℤ) * (2 : ℤ) ^ k = (2 : ℤ) ^ (k + 1 + 1) := by
          rw [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num, ← pow_add]
          congr 1; omega
        rw [hsc]
      · intro i j
        have hdvd : (4 : ℤ) ∣ ((B + (2 : ℤ) ^ k • (B * B)) i j - B i j) := by
          have h : (B + (2 : ℤ) ^ k • (B * B)) i j - B i j =
              (2 : ℤ) ^ k * (B * B) i j := by
            rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left]
          rw [h]
          have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ k := by
            rw [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
            exact pow_dvd_pow _ hk
          exact dvd_mul_of_dvd_left h4 _
        have hdvd' : (4 : ℤ) ∣ B i j - (B + (2 : ℤ) ^ k • (B * B)) i j := by
          rw [← neg_sub]
          exact dvd_neg.mpr hdvd
        have hmod : (B + (2 : ℤ) ^ k • (B * B)) i j ≡ B i j [ZMOD 4] :=
          Int.modEq_iff_dvd.mpr hdvd'
        exact hmod.trans (hB4 i j)

/-- The first component of the slope matrix applied to a state. -/
private def beta (B : Mat) (n : ℤ) : ℤ := (B *ᵥ state n) 0

private theorem state_shift_five_pow (k : ℕ) (B : Mat)
    (hB : (companion ^ 5) ^ (2 ^ k) = 1 + (2 : ℤ) ^ (k + 1) • B) (n : ℤ) :
    state (n + 5 * (2 : ℤ) ^ k) = state n + (2 : ℤ) ^ (k + 1) • (B *ᵥ state n) := by
  have h : state (n + (5 * 2 ^ k : ℕ)) = (companion ^ 5) ^ (2 ^ k) *ᵥ state n := by
    rw [state_shift, pow_mul]
  rw [hB, add_mulVec, one_mulVec, smul_mulVec] at h
  have hcast : (n : ℤ) + ((5 * 2 ^ k : ℕ) : ℤ) = n + 5 * (2 : ℤ) ^ k := by
    push_cast; ring
  rw [hcast] at h
  exact h

private theorem lifted_step (k : ℕ) (_hk : 1 ≤ k) (B : Mat)
    (hB : (companion ^ 5) ^ (2 ^ k) = 1 + (2 : ℤ) ^ (k + 1) • B) (n : ℤ) :
    tetranacciInt (n + 5 * (2 : ℤ) ^ k) =
      tetranacciInt n + (2 : ℤ) ^ (k + 1) * beta B n := by
  have h := state_shift_five_pow k B hB n
  have h0 := congrFun h 0
  simp only [state, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
  exact h0

private theorem beta_step (k : ℕ) (hk : 1 ≤ k) (B : Mat)
    (hB : (companion ^ 5) ^ (2 ^ k) = 1 + (2 : ℤ) ^ (k + 1) • B) (n : ℤ) :
    ∃ w : ℤ, beta B (n + 5 * (2 : ℤ) ^ k) = beta B n + 4 * w := by
  have h := state_shift_five_pow k B hB n
  have hbeta : beta B (n + 5 * (2 : ℤ) ^ k) =
      beta B n + (2 : ℤ) ^ (k + 1) * (B *ᵥ (B *ᵥ state n)) 0 := by
    change (B *ᵥ state (n + 5 * (2 : ℤ) ^ k)) 0 =
      (B *ᵥ state n) 0 + (2 : ℤ) ^ (k + 1) * (B *ᵥ (B *ᵥ state n)) 0
    rw [h, Matrix.mulVec_add, Matrix.mulVec_smul]
    simp [Pi.add_apply]
  rw [hbeta]
  have hc : (4 : ℤ) ∣ (2 : ℤ) ^ (k + 1) := by
    rw [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
    exact pow_dvd_pow _ (by omega)
  obtain ⟨c0, hc0⟩ := hc
  refine ⟨c0 * (B *ᵥ (B *ᵥ state n)) 0, ?_⟩
  rw [hc0]; ring

private theorem beta_cong (k : ℕ) (hk : 1 ≤ k) (B : Mat)
    (hB : (companion ^ 5) ^ (2 ^ k) = 1 + (2 : ℤ) ^ (k + 1) • B) (a : ℤ) (s : ℕ) :
    ∃ w : ℤ, beta B (a + (5 * (2 : ℤ) ^ k) * s) = beta B a + 4 * w := by
  induction s with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ := beta_step k hk B hB (a + (5 * (2 : ℤ) ^ k) * s)
      refine ⟨w + w', ?_⟩
      have harg : a + (5 * (2 : ℤ) ^ k) * ((s + 1 : ℕ) : ℤ) =
          (a + (5 * (2 : ℤ) ^ k) * s) + 5 * (2 : ℤ) ^ k := by
        push_cast; ring
      rw [harg, hw', hw]
      ring

private theorem lifted_multiple (k : ℕ) (hk : 1 ≤ k) (B : Mat)
    (hB : (companion ^ 5) ^ (2 ^ k) = 1 + (2 : ℤ) ^ (k + 1) • B) (a : ℤ) (s : ℕ) :
    ∃ z : ℤ, tetranacciInt (a + (5 * (2 : ℤ) ^ k) * s) - tetranacciInt a =
      (2 : ℤ) ^ (k + 1) * ((s : ℤ) * beta B a + 4 * z) := by
  induction s with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨w, hw⟩ := beta_cong k hk B hB a s
      refine ⟨z + w, ?_⟩
      have harg : a + (5 * (2 : ℤ) ^ k) * ((s + 1 : ℕ) : ℤ) =
          (a + (5 * (2 : ℤ) ^ k) * s) + 5 * (2 : ℤ) ^ k := by
        push_cast; ring
      have hstep := lifted_step k hk B hB (a + (5 * (2 : ℤ) ^ k) * s)
      rw [harg, hstep, hw, sub_eq_iff_eq_add.mp hz]
      push_cast; ring

/-- Two slope matrices agreeing modulo $4$ give the same `beta` modulo $4$. -/
private theorem beta_mod_four_of_congr (B B' : Mat) (n : ℤ)
    (h : ∀ i j, (B i j) % 4 = (B' i j) % 4) :
    (beta B n) % 4 = (beta B' n) % 4 := by
  change ((B *ᵥ state n) 0) % 4 = ((B' *ᵥ state n) 0) % 4
  have hdvd : (4 : ℤ) ∣ (B *ᵥ state n) 0 - (B' *ᵥ state n) 0 := by
    have e1 : (B *ᵥ state n) 0 = ∑ j, B 0 j * state n j := rfl
    have e2 : (B' *ᵥ state n) 0 = ∑ j, B' 0 j * state n j := rfl
    rw [e1, e2, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro j _
    rw [← sub_mul]
    have hj : (4 : ℤ) ∣ B 0 j - B' 0 j := by
      have hmod : B 0 j ≡ B' 0 j [ZMOD 4] := h 0 j
      have h' := Int.modEq_iff_dvd.mp hmod
      rw [← neg_sub]
      exact dvd_neg.mpr h'
    exact dvd_mul_of_dvd_left hj _
  exact Int.modEq_iff_dvd.mpr (by rw [← neg_sub]; exact dvd_neg.mpr hdvd)

/-- At the centres $-1$ and $4$, the $10$-step slope is odd. -/
private theorem beta_one_odd (a : ℤ) (ha : a = -1 ∨ a = 4) :
    (beta slopeMatrixOne a) % 2 = 1 := by
  rcases ha with rfl | rfl <;> decide

/-- At the six centres, the $20$-step slope is not divisible by $4$. -/
private theorem beta_two_mod_four (a : ℤ)
    (ha : a = -12 ∨ a = -7 ∨ a = -2 ∨ a = -1 ∨ a = 3 ∨ a = 4) :
    (beta slopeMatrixTwo a) % 4 = 1 ∨ (beta slopeMatrixTwo a) % 4 = 2 ∨
      (beta slopeMatrixTwo a) % 4 = 3 := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- An odd multiple of a number not divisible by $4$, plus a multiple of $4$,
is not divisible by $4$. -/
private theorem four_not_dvd_mul_add (s : ℕ) (hs : ¬ (2 : ℕ) ∣ s) (β : ℤ)
    (hβ : β % 4 ≠ 0) (z : ℤ) : ((s : ℤ) * β + 4 * z) % 4 ≠ 0 := by
  have hs4 : s % 4 = 1 ∨ s % 4 = 3 := by omega
  have hβ4 : β % 4 = 1 ∨ β % 4 = 2 ∨ β % 4 = 3 := by omega
  have e2 : ((s : ℤ) * β) % 4 ≠ 0 := by
    have hs4z : (s : ℤ) % 4 = ((s % 4 : ℕ) : ℤ) := by
      rw [Int.natCast_mod]; norm_num
    rcases hs4 with h1 | h1 <;> rcases hβ4 with h2 | h2 | h2 <;>
      rw [Int.mul_emod, hs4z, h1, h2] <;> norm_num
  intro hcon
  omega

/-- From a lifted $2$-adic expansion of $Q \mp 1$, the $2$-adic valuation of
$Q^2 - 1$ is at most $k + 3$. -/
private theorem factorization_bound_from_lift
    (Q : ℕ) (hQ : 2 ≤ Q) (qc : ℤ) (hqc : qc = 1 ∨ qc = -1)
    (k : ℕ) (hk : 1 ≤ k) (w : ℤ) (hw4 : w % 4 ≠ 0)
    (hw : (Q : ℤ) - qc = (2 : ℤ) ^ (k + 1) * w) :
    (Q ^ 2 - 1).factorization 2 ≤ k + 3 := by
  have hQz : (2 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hQ
  have hqc2 : qc ^ 2 = 1 := by rcases hqc with rfl | rfl <;> norm_num
  have hu0 : 0 < (Q : ℤ) - qc := by rcases hqc with rfl | rfl <;> omega
  have hv0 : 0 < (Q : ℤ) + qc := by rcases hqc with rfl | rfl <;> omega
  set U : ℕ := ((Q : ℤ) - qc).natAbs with hU_def
  set V : ℕ := ((Q : ℤ) + qc).natAbs with hV_def
  have hU0 : U ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hu0)
  have hV0 : V ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hv0)
  have hcast : ((Q ^ 2 - 1 : ℕ) : ℤ) = (Q : ℤ) ^ 2 - 1 := by
    have h1 : (1 : ℕ) ≤ Q ^ 2 := Nat.one_le_pow 2 Q (by omega)
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  have huv : (Q : ℤ) ^ 2 - 1 = ((Q : ℤ) - qc) * ((Q : ℤ) + qc) := by
    linear_combination hqc2
  have hUV : ((U * V : ℕ) : ℤ) = ((Q : ℤ) - qc) * ((Q : ℤ) + qc) := by
    have eU : ((U : ℕ) : ℤ) = (Q : ℤ) - qc := by
      rw [hU_def]; exact Int.natAbs_of_nonneg (le_of_lt hu0)
    have eV : ((V : ℕ) : ℤ) = (Q : ℤ) + qc := by
      rw [hV_def]; exact Int.natAbs_of_nonneg (le_of_lt hv0)
    rw [Nat.cast_mul, eU, eV]
  have hQUV : Q ^ 2 - 1 = U * V := by
    apply Nat.cast_injective (R := ℤ)
    rw [hcast, huv, ← hUV]
  have hfac : (Q ^ 2 - 1).factorization 2 =
      U.factorization 2 + V.factorization 2 := by
    rw [hQUV, Nat.factorization_mul hU0 hV0, Finsupp.add_apply]
  have hVle : V.factorization 2 ≤ 1 := by
    by_contra hcon
    have hcon : 1 < V.factorization 2 := not_le.mp hcon
    have hdvd : (2 : ℕ) ^ 2 ∣ V := by
      rw [Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 2) hV0]
      exact hcon
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hdvd
    have hv4 : ((Q : ℤ) + qc) % 4 = 2 := by
      have hu4 : ((Q : ℤ) - qc) % 4 = 0 := by
        apply Int.emod_eq_zero_of_dvd
        rw [hw]
        have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ (k + 1) := by
          rw [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
          exact pow_dvd_pow _ (by omega)
        exact dvd_mul_of_dvd_left h4 _
      rcases hqc with rfl | rfl <;> omega
    have h4v : (4 : ℤ) ∣ (Q : ℤ) + qc := by
      have h : (4 : ℤ) ∣ ((V : ℕ) : ℤ) := by exact_mod_cast hdvd
      rw [hV_def] at h
      exact Int.dvd_natAbs.mp h
    rw [Int.emod_eq_zero_of_dvd h4v] at hv4
    norm_num at hv4
  have hUle : U.factorization 2 ≤ k + 2 := by
    by_contra hcon
    have hcon : k + 2 < U.factorization 2 := not_le.mp hcon
    have hdvd : (2 : ℕ) ^ (k + 3) ∣ U := by
      rw [Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 2) hU0]
      omega
    have hUeq : U = 2 ^ (k + 1) * w.natAbs := by
      have h2 : ((2 : ℤ).natAbs) = 2 := rfl
      rw [hU_def, hw, Int.natAbs_mul, Int.natAbs_pow, h2]
    rw [hUeq] at hdvd
    have hpow : (2 : ℕ) ^ (k + 3) = 2 ^ (k + 1) * 4 := by
      rw [show k + 3 = (k + 1) + 2 by omega, pow_add]; norm_num
    rw [hpow, Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num : 0 < 2) _)] at hdvd
    have h4w : (4 : ℤ) ∣ w := by
      have h : (4 : ℤ) ∣ ((w.natAbs : ℕ) : ℤ) := by exact_mod_cast hdvd
      exact Int.dvd_natAbs.mp h
    rw [Int.emod_eq_zero_of_dvd h4w] at hw4
    exact hw4 rfl
  rw [hfac]; omega

private theorem tetranacci_rec (k : ℕ) :
    tetranacci (k + 4) =
      tetranacci (k + 3) + tetranacci (k + 2) + tetranacci (k + 1) + tetranacci k := rfl

private theorem tetranacci_le_succ : ∀ n, tetranacci n ≤ tetranacci (n + 1) := by
  have key : ∀ n, tetranacci n ≤ tetranacci (n + 1) ∧ tetranacci (n + 1) ≤ tetranacci (n + 2) ∧
      tetranacci (n + 2) ≤ tetranacci (n + 3) ∧ tetranacci (n + 3) ≤ tetranacci (n + 4) := by
    intro n
    induction n with
    | zero => exact ⟨by decide, by decide, by decide, by decide⟩
    | succ n ih =>
        obtain ⟨h1, h2, h3, h4⟩ := ih
        refine ⟨h2, h3, h4, ?_⟩
        have hrec := tetranacci_rec (n + 1)
        rw [show n + 1 + 4 = n + 5 by omega, show n + 1 + 3 = n + 4 by omega,
          show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega] at hrec
        rw [show n + 1 + 3 = n + 4 by omega, show n + 1 + 4 = n + 5 by omega, hrec]
        omega
  exact fun n => (key n).1

private theorem tetranacci_mono {a b : ℕ} (h : a ≤ b) : tetranacci a ≤ tetranacci b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (tetranacci_le_succ n)

private theorem tetranacci_four_mul (n : ℕ) :
    4 * tetranacci n ≤ tetranacci (n + 4) := by
  rw [tetranacci_rec n]
  have h1 := tetranacci_mono (show n ≤ n + 1 by omega)
  have h2 := tetranacci_mono (show n ≤ n + 2 by omega)
  have h3 := tetranacci_mono (show n ≤ n + 3 by omega)
  omega

private theorem tetranacci_ge_pow (k : ℕ) :
    2 ^ (2 * k + 3) ≤ tetranacci (8 + 4 * k) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have h1 : tetranacci (8 + 4 * (k + 1)) = tetranacci ((8 + 4 * k) + 4) := by
        rw [show 8 + 4 * (k + 1) = (8 + 4 * k) + 4 by omega]
      have h2 := tetranacci_four_mul (8 + 4 * k)
      have h3 : (2 : ℕ) ^ (2 * (k + 1) + 3) = 4 * 2 ^ (2 * k + 3) := by
        rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by omega, pow_add,
          show (2 : ℕ) ^ 2 = 4 by norm_num]; ring
      rw [h1, h3]
      omega

private theorem tetranacci_sq_ge (n : ℕ) (hn : 8 ≤ n) :
    (2 : ℕ) ^ (n - 5) ≤ tetranacci n ^ 2 := by
  obtain ⟨k, r, hr, hnr⟩ : ∃ k r, r < 4 ∧ n = 8 + 4 * k + r :=
    ⟨(n - 8) / 4, (n - 8) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have hmono : tetranacci (8 + 4 * k) ≤ tetranacci n := tetranacci_mono (by omega)
  have hge := tetranacci_ge_pow k
  have hexp : (2 : ℕ) ^ (n - 5) ≤ (2 : ℕ) ^ (4 * k + 6) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : (2 : ℕ) ^ (4 * k + 6) ≤ tetranacci n ^ 2 := by
    have h1 : (2 : ℕ) ^ (4 * k + 6) = (2 ^ (2 * k + 3)) ^ 2 := by
      rw [← pow_mul]; congr 1; omega
    rw [h1]
    exact Nat.pow_le_pow_left (le_trans hge hmono) 2
  exact le_trans hexp hsq

private theorem factorial_le_self_pow (m : ℕ) : Nat.factorial m ≤ m ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : m ^ m ≤ (m + 1) ^ m := Nat.pow_le_pow_left (Nat.le_succ m) m
      rw [Nat.factorial_succ, pow_succ, mul_comm ((m + 1) ^ m) (m + 1)]
      exact Nat.mul_le_mul (le_refl _) (le_trans ih h1)

private theorem factorial_le_pow_sq (m : ℕ) : Nat.factorial m ≤ (2 : ℕ) ^ (m * m) := by
  calc Nat.factorial m ≤ m ^ m := factorial_le_self_pow m
    _ ≤ (2 ^ m) ^ m := Nat.pow_le_pow_left (by have := Nat.lt_two_pow_self (n := m); omega) m
    _ = (2 : ℕ) ^ (m * m) := by rw [← pow_mul]

private theorem tetranacci_index_le (m n : ℕ) (h : tetranacci n ^ 2 = Nat.factorial m + 1) :
    n ≤ m * m + 6 := by
  by_cases hn : 8 ≤ n
  · have hsq := tetranacci_sq_ge n hn
    have hfact := factorial_le_pow_sq m
    have hle : (2 : ℕ) ^ (n - 5) ≤ (2 : ℕ) ^ (m * m + 1) := by
      calc (2 : ℕ) ^ (n - 5) ≤ tetranacci n ^ 2 := hsq
        _ = Nat.factorial m + 1 := h
        _ ≤ (2 : ℕ) ^ (m * m) + 1 := by omega
        _ ≤ (2 : ℕ) ^ (m * m + 1) := by
            have hpos : (0 : ℕ) < (2 : ℕ) ^ (m * m) := by positivity
            have hpow : (2 : ℕ) ^ (m * m + 1) = 2 * (2 : ℕ) ^ (m * m) := by rw [pow_succ']
            omega
    have hle' : n - 5 ≤ m * m + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  · by_cases hm0 : m = 0
    · subst hm0
      simp only [Nat.factorial_zero] at h
      have h2 := congrArg Nat.sqrt h
      rw [Nat.sqrt_eq'] at h2
      norm_num at h2
      rw [h2] at h
      norm_num at h
    · have hm1 : 1 ≤ m * m := by
        have h1m : 1 ≤ m := by omega
        calc (1 : ℕ) = 1 * 1 := by norm_num
          _ ≤ m * m := Nat.mul_le_mul h1m h1m
      omega

/-- If $2^m$ divides $2^k \cdot s$ with $s$ odd, then $m \le k$. -/
private theorem pow_exponent_ge_of_dvd (D k s : ℕ) (hD : D = 2 ^ k * s)
    (hs : ¬ (2 : ℕ) ∣ s) (m : ℕ) (hdvd : 2 ^ m ∣ D) : m ≤ k := by
  by_contra hcon
  have hklt : k < m := not_le.mp hcon
  have h2 : (2 : ℕ) ^ m ∣ (2 : ℕ) ^ k * s := by rw [← hD]; exact hdvd
  rw [show m = k + (m - k) by omega, pow_add] at h2
  have h3 : (2 : ℕ) ^ (m - k) ∣ s :=
    (Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num : 0 < 2) _)).mp h2
  have h2s : (2 : ℕ) ∣ s :=
    dvd_trans (dvd_pow_self 2 (by omega : m - k ≠ 0)) h3
  exact hs h2s

/-- Write a positive integer difference as $2^k \cdot s$ with $s$ odd, keeping a
divisibility lower bound on $k$. -/
private theorem obtain_pow_data (t : ℕ) (a : ℤ) (ha : 1 ≤ (t : ℤ) - a) (m : ℕ)
    (hdvd : (2 : ℤ) ^ m ∣ (t : ℤ) - a) :
    ∃ k s : ℕ, (t : ℤ) - a = (2 : ℤ) ^ k * (s : ℤ) ∧ ¬ (2 : ℕ) ∣ s ∧ m ≤ k := by
  have hD : (((t : ℤ) - a).toNat : ℤ) = (t : ℤ) - a :=
    Int.toNat_of_nonneg (by omega)
  have hD0 : ((t : ℤ) - a).toNat ≠ 0 := by
    intro h
    rw [h] at hD
    simp at hD
    omega
  obtain ⟨k, s, hs, hDseq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hD0 2 (by norm_num)
  have hdvdD : (2 : ℕ) ^ m ∣ ((t : ℤ) - a).toNat := by
    have h' : (2 : ℤ) ^ m ∣ (((t : ℤ) - a).toNat : ℤ) := by rw [hD]; exact hdvd
    exact_mod_cast h'
  refine ⟨k, s, ?_, hs, pow_exponent_ge_of_dvd _ k s hDseq hs m hdvdD⟩
  rw [← hD, hDseq]
  push_cast; ring

/-- The slope matrix for a $2^k$-fold $5$-step shift with $k \ge 2$, at one of
the six centres. -/
private theorem obtain_slope_ge_two (k : ℕ) (hk : 2 ≤ k) (center : ℤ)
    (hcenter : center = -12 ∨ center = -7 ∨ center = -2 ∨ center = -1 ∨
      center = 3 ∨ center = 4) :
    ∃ B : Mat, (companion ^ 5) ^ (2 ^ k) = 1 + (2 : ℤ) ^ (k + 1) • B ∧
      (beta B center) % 4 ≠ 0 := by
  obtain ⟨B, hB, hB4⟩ := companion_pow_two_pow k hk
  refine ⟨B, hB, ?_⟩
  rw [beta_mod_four_of_congr B slopeMatrixTwo center hB4]
  rcases beta_two_mod_four center hcenter with h | h | h <;> omega

/-- The slope matrix for the $10$-step shift, at the centres $-1$ and $4$. -/
private theorem obtain_slope_one (center : ℤ) (hcenter : center = -1 ∨ center = 4) :
    ∃ B : Mat, (companion ^ 5) ^ (2 ^ 1) = 1 + (2 : ℤ) ^ (1 + 1) • B ∧
      (beta B center) % 4 ≠ 0 := by
  refine ⟨slopeMatrixOne, ?_, ?_⟩
  · rw [show (2 : ℕ) ^ 1 = 2 by norm_num, show (2 : ℤ) ^ (1 + 1) = 4 by norm_num]
    exact companion_pow_five_two
  · have h := beta_one_odd center hcenter
    omega

/-- From a lifted expansion at a centre, the $2$-adic valuation of
$Q_n^2 - 1$ and the size of $2^k$ relative to $t$. -/
private theorem factorization_bound_case
    (n : ℕ) (r t : ℕ) (a : ℤ) (center : ℤ) (qc : ℤ)
    (hnr : n = 5 * t + r) (hcenter : center = 5 * a + (r : ℤ))
    (hqc : tetranacciInt center = qc) (hqc1 : qc = 1 ∨ qc = -1)
    (_ht : 1 ≤ t) (ha3 : -3 ≤ a) (ha0 : a ≤ 0)
    (k s : ℕ) (hds : (t : ℤ) - a = (2 : ℤ) ^ k * (s : ℤ)) (hk : 1 ≤ k)
    (hs : ¬ (2 : ℕ) ∣ s)
    (B : Mat) (hB : (companion ^ 5) ^ (2 ^ k) = 1 + (2 : ℤ) ^ (k + 1) • B)
    (hβ : (beta B center) % 4 ≠ 0) (hQ : 2 ≤ tetranacci n) :
    (tetranacci n ^ 2 - 1).factorization 2 ≤ k + 3 ∧ (2 : ℕ) ^ k ≤ t + 3 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := lifted_multiple k hk B hB center s
    have hnarg : center + (5 * (2 : ℤ) ^ k) * (s : ℤ) = (n : ℤ) := by
      have e : (n : ℤ) = 5 * (t : ℤ) + (r : ℤ) := by exact_mod_cast hnr
      rw [hcenter]
      linear_combination -5 * hds - e
    rw [hnarg, hqc, tetranacciInt_nat] at hz
    have hw4 := four_not_dvd_mul_add s hs (beta B center) hβ z
    exact factorization_bound_from_lift (tetranacci n) hQ qc hqc1 k hk _ hw4 hz
  · have hspos : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · exfalso
        rw [h0] at hds
        simp at hds
        omega
      · exact hpos
    have h1 : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ k * (s : ℤ) := by
      have hle := mul_le_mul_of_nonneg_left
        (show (1 : ℤ) ≤ (s : ℤ) by exact_mod_cast hspos)
        (pow_nonneg (show (0 : ℤ) ≤ (2 : ℤ) by norm_num) k)
      simpa using hle
    rw [← hds] at h1
    have h2 : ((2 : ℕ) ^ k : ℤ) ≤ ((t + 3 : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast h2

private theorem tetranacciInt_add_five_mod_two (n : ℤ) :
    tetranacciInt (n + 5) % 2 = tetranacciInt n % 2 := by
  have h := state_shift n 5
  rw [companion_pow_five, add_mulVec, one_mulVec, smul_mulVec] at h
  have h0 := congrFun h 0
  simp only [state, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_ofNat] at h0
  omega

private theorem tetranacciInt_mod_two_periodic (r : ℤ) (t : ℕ) :
    tetranacciInt (r + 5 * (t : ℤ)) % 2 = tetranacciInt r % 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show r + 5 * ((t + 1 : ℕ) : ℤ) = (r + 5 * (t : ℤ)) + 5 by push_cast; ring,
        tetranacciInt_add_five_mod_two]
      exact ih

private theorem tetranacci_mod_two_of_residue (n : ℕ) (r : ℕ) (hr : n % 5 = r)
    (hr0 : tetranacci r = 0) : tetranacci n % 2 = 0 := by
  have hdiv : n = r + 5 * (n / 5) := by
    have h := Nat.div_add_mod n 5; omega
  have hper := tetranacciInt_mod_two_periodic ((r : ℤ)) (n / 5)
  have e : ((tetranacci n : ℕ) : ℤ) % 2 = 0 := by
    rw [← tetranacciInt_nat]
    have harg : (n : ℤ) = (r : ℤ) + 5 * ((n / 5 : ℕ) : ℤ) := by exact_mod_cast hdiv
    rw [harg, hper, tetranacciInt_nat, hr0]
    norm_num
  have e2 : ((tetranacci n % 2 : ℕ) : ℤ) = 0 := by
    rw [Int.natCast_mod]; exact e
  exact Nat.cast_eq_zero.mp e2

private theorem pow_factorization_le (n : ℕ) (hn : 5 ≤ n) :
    (2 : ℕ) ^ (tetranacci n ^ 2 - 1).factorization 2 ≤ 8 * (n + 12) := by
  have hQ : 2 ≤ tetranacci n := by
    have h5 : tetranacci 5 = 2 := rfl
    have hmono := tetranacci_mono hn
    omega
  obtain ⟨k, t, hfact, h2k, htn⟩ :
      ∃ k t : ℕ, (tetranacci n ^ 2 - 1).factorization 2 ≤ k + 3 ∧
        (2 : ℕ) ^ k ≤ t + 3 ∧ t ≤ n := by
    by_cases hr3 : n % 5 = 3
    · have hnr : n = 5 * (n / 5) + 3 := by
        have h := Nat.div_add_mod n 5; omega
      have ht : 1 ≤ n / 5 := by omega
      have hmod : ((n / 5 : ℕ) : ℤ) % 4 = 0 ∨ ((n / 5 : ℕ) : ℤ) % 4 = 1 ∨
          ((n / 5 : ℕ) : ℤ) % 4 = 2 ∨ ((n / 5 : ℕ) : ℤ) % 4 = 3 := by omega
      rcases hmod with hmod | hmod | hmod | hmod
      · obtain ⟨k, s, hds, hs, hk⟩ := obtain_pow_data (n / 5) 0 (by omega) 2 (by omega)
        obtain ⟨B, hB, hβ⟩ := obtain_slope_ge_two k hk 3 (by decide)
        obtain ⟨hfact, h2k⟩ := factorization_bound_case n 3 (n / 5) 0 3 1 hnr (by norm_num)
          (by decide) (Or.inl rfl) ht (by norm_num) (by norm_num) k s hds (by omega) hs B hB hβ hQ
        exact ⟨k, n / 5, hfact, h2k, Nat.div_le_self n 5⟩
      · obtain ⟨k, s, hds, hs, hk⟩ := obtain_pow_data (n / 5) (-3) (by omega) 2 (by omega)
        obtain ⟨B, hB, hβ⟩ := obtain_slope_ge_two k hk (-12) (by decide)
        obtain ⟨hfact, h2k⟩ := factorization_bound_case n 3 (n / 5) (-3) (-12) (-1) hnr
          (by norm_num) (by decide) (Or.inr rfl) ht (by norm_num) (by norm_num) k s hds
          (by omega) hs B hB hβ hQ
        exact ⟨k, n / 5, hfact, h2k, Nat.div_le_self n 5⟩
      · obtain ⟨k, s, hds, hs, hk⟩ := obtain_pow_data (n / 5) (-2) (by omega) 2 (by omega)
        obtain ⟨B, hB, hβ⟩ := obtain_slope_ge_two k hk (-7) (by decide)
        obtain ⟨hfact, h2k⟩ := factorization_bound_case n 3 (n / 5) (-2) (-7) 1 hnr (by norm_num)
          (by decide) (Or.inl rfl) ht (by norm_num) (by norm_num) k s hds (by omega) hs B hB hβ hQ
        exact ⟨k, n / 5, hfact, h2k, Nat.div_le_self n 5⟩
      · obtain ⟨k, s, hds, hs, hk⟩ := obtain_pow_data (n / 5) (-1) (by omega) 2 (by omega)
        obtain ⟨B, hB, hβ⟩ := obtain_slope_ge_two k hk (-2) (by decide)
        obtain ⟨hfact, h2k⟩ := factorization_bound_case n 3 (n / 5) (-1) (-2) (-1) hnr
          (by norm_num) (by decide) (Or.inr rfl) ht (by norm_num) (by norm_num) k s hds
          (by omega) hs B hB hβ hQ
        exact ⟨k, n / 5, hfact, h2k, Nat.div_le_self n 5⟩
    · by_cases hr4 : n % 5 = 4
      · have hnr : n = 5 * (n / 5) + 4 := by
          have h := Nat.div_add_mod n 5; omega
        have ht : 1 ≤ n / 5 := by omega
        have hmod : ((n / 5 : ℕ) : ℤ) % 2 = 0 ∨ ((n / 5 : ℕ) : ℤ) % 2 = 1 := by omega
        rcases hmod with hmod | hmod
        · obtain ⟨k, s, hds, hs, hk⟩ := obtain_pow_data (n / 5) 0 (by omega) 1 (by omega)
          by_cases hk2 : 2 ≤ k
          · obtain ⟨B, hB, hβ⟩ := obtain_slope_ge_two k hk2 4 (by decide)
            obtain ⟨hfact, h2k⟩ := factorization_bound_case n 4 (n / 5) 0 4 1 hnr (by norm_num)
              (by decide) (Or.inl rfl) ht (by norm_num) (by norm_num) k s hds hk hs B hB hβ hQ
            exact ⟨k, n / 5, hfact, h2k, Nat.div_le_self n 5⟩
          · have hk1 : k = 1 := by omega
            subst hk1
            obtain ⟨B, hB, hβ⟩ := obtain_slope_one 4 (Or.inr rfl)
            obtain ⟨hfact, h2k⟩ := factorization_bound_case n 4 (n / 5) 0 4 1 hnr (by norm_num)
              (by decide) (Or.inl rfl) ht (by norm_num) (by norm_num) 1 s hds (by norm_num) hs
              B hB hβ hQ
            exact ⟨1, n / 5, hfact, h2k, Nat.div_le_self n 5⟩
        · obtain ⟨k, s, hds, hs, hk⟩ := obtain_pow_data (n / 5) (-1) (by omega) 1 (by omega)
          by_cases hk2 : 2 ≤ k
          · obtain ⟨B, hB, hβ⟩ := obtain_slope_ge_two k hk2 (-1) (by decide)
            obtain ⟨hfact, h2k⟩ := factorization_bound_case n 4 (n / 5) (-1) (-1) 1 hnr
              (by norm_num) (by decide) (Or.inl rfl) ht (by norm_num) (by norm_num) k s hds hk
              hs B hB hβ hQ
            exact ⟨k, n / 5, hfact, h2k, Nat.div_le_self n 5⟩
          · have hk1 : k = 1 := by omega
            subst hk1
            obtain ⟨B, hB, hβ⟩ := obtain_slope_one (-1) (Or.inl rfl)
            obtain ⟨hfact, h2k⟩ := factorization_bound_case n 4 (n / 5) (-1) (-1) 1 hnr
              (by norm_num) (by decide) (Or.inl rfl) ht (by norm_num) (by norm_num) 1 s hds
              (by norm_num) hs B hB hβ hQ
            exact ⟨1, n / 5, hfact, h2k, Nat.div_le_self n 5⟩
      · have hfact0 : (tetranacci n ^ 2 - 1).factorization 2 = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hdvd
          have hr : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 := by omega
          have hmod2 : (tetranacci n ^ 2 - 1) % 2 = 1 := by
            have h1 : tetranacci n % 2 = 0 := by
              rcases hr with hr | hr | hr
              · exact tetranacci_mod_two_of_residue n 0 hr rfl
              · exact tetranacci_mod_two_of_residue n 1 hr rfl
              · exact tetranacci_mod_two_of_residue n 2 hr rfl
            have h2 : (tetranacci n ^ 2) % 2 = 0 := by
              rw [Nat.pow_mod]; simp [h1]
            have h3 : 1 ≤ tetranacci n ^ 2 := Nat.one_le_pow 2 _ (by omega)
            omega
          omega
        exact ⟨0, n / 5, by omega, by omega, Nat.div_le_self n 5⟩
  have hpowle : (2 : ℕ) ^ ((tetranacci n ^ 2 - 1).factorization 2) ≤ (2 : ℕ) ^ (k + 3) :=
    Nat.pow_le_pow_right (by norm_num) hfact
  have h3 : (2 : ℕ) ^ (k + 3) = 8 * (2 : ℕ) ^ k := by rw [pow_add]; ring
  omega

private theorem two_pow_dvd_factorial (m : ℕ) : (2 : ℕ) ^ (m / 2) ∣ Nat.factorial m := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m ih1 _ih2 =>
      have hdiv : (m + 2) / 2 = m / 2 + 1 := by omega
      rw [hdiv, pow_succ]
      have hfact : Nat.factorial (m + 2) = ((m + 2) * (m + 1)) * Nat.factorial m := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; ring
      rw [hfact]
      have heven : (2 : ℕ) ∣ (m + 2) * (m + 1) := by
        have h := even_iff_two_dvd.mp (Nat.even_mul_succ_self (m + 1))
        rwa [mul_comm] at h
      have hd := Nat.mul_dvd_mul ih1 heven
      have heq : Nat.factorial m * ((m + 2) * (m + 1)) = ((m + 2) * (m + 1)) * Nat.factorial m := by
        ring
      rwa [heq] at hd

private theorem eight_sq_bound (x : ℕ) (hx : 28 ≤ x) :
    8 * (x + 2) ^ 2 + 144 ≤ 2 * (8 * x ^ 2 + 144) := by
  have hX28 : (28 : ℕ) * x ≤ x ^ 2 := by
    rw [pow_two, mul_comm (28 : ℕ) x]
    exact Nat.mul_le_mul (le_refl _) hx
  have hsq : (x + 2) ^ 2 = x ^ 2 + 4 * x + 4 := by ring
  rw [hsq]; omega

private theorem lt_twenty_eight_of_pow_le (m : ℕ)
    (h : (2 : ℕ) ^ (m / 2) ≤ 8 * m ^ 2 + 144) : m < 28 := by
  by_contra hcon
  have h28 : 28 ≤ m := not_lt.mp hcon
  have key : ∀ k, (2 : ℕ) ^ ((28 + 2 * k) / 2) > 8 * (28 + 2 * k) ^ 2 + 144 ∧
      (2 : ℕ) ^ ((29 + 2 * k) / 2) > 8 * (29 + 2 * k) ^ 2 + 144 := by
    intro k
    induction k with
    | zero => constructor <;> norm_num
    | succ k ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have e1 : (28 + 2 * (k + 1)) / 2 = (28 + 2 * k) / 2 + 1 := by omega
        have e2 : (29 + 2 * (k + 1)) / 2 = (29 + 2 * k) / 2 + 1 := by omega
        refine ⟨?_, ?_⟩
        · rw [e1, pow_succ, show 28 + 2 * (k + 1) = (28 + 2 * k) + 2 by omega]
          have hX := eight_sq_bound (28 + 2 * k) (by omega)
          have hlt : 2 * (2 : ℕ) ^ ((28 + 2 * k) / 2) > 2 * (8 * (28 + 2 * k) ^ 2 + 144) :=
            Nat.mul_lt_mul_of_pos_left ih1 (by norm_num)
          omega
        · rw [e2, pow_succ, show 29 + 2 * (k + 1) = (29 + 2 * k) + 2 by omega]
          have hX := eight_sq_bound (29 + 2 * k) (by omega)
          have hlt : 2 * (2 : ℕ) ^ ((29 + 2 * k) / 2) > 2 * (8 * (29 + 2 * k) ^ 2 + 144) :=
            Nat.mul_lt_mul_of_pos_left ih2 (by norm_num)
          omega
  obtain ⟨k, hk⟩ : ∃ k, m = 28 + 2 * k ∨ m = 29 + 2 * k := ⟨(m - 28) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have hkey := (key k).1
    omega
  · have hkey := (key k).2
    omega

private theorem tetranacci_ne_five_eleven_seventy_one (n : ℕ) :
    tetranacci n ≠ 5 ∧ tetranacci n ≠ 11 ∧ tetranacci n ≠ 71 := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hn : n < 7
    · interval_cases n <;> decide
    · have h7 : tetranacci 7 = 8 := rfl
      have hmono := tetranacci_mono (show 7 ≤ n by omega)
      omega
  · by_cases hn : n < 8
    · interval_cases n <;> decide
    · have h8 : tetranacci 8 = 15 := rfl
      have hmono := tetranacci_mono (show 8 ≤ n by omega)
      omega
  · by_cases hn : n < 11
    · interval_cases n <;> decide
    · have h11 : tetranacci 11 = 108 := rfl
      have hmono := tetranacci_mono (show 11 ≤ n by omega)
      omega

private theorem not_isSquare_of_sqrt (N : ℕ)
    (hne : Nat.sqrt N * Nat.sqrt N ≠ N) : ¬ IsSquare N := by
  rintro ⟨k, hk⟩
  have hsqrt : Nat.sqrt N = k := by
    rw [hk, ← pow_two]; exact Nat.sqrt_eq' k
  rw [hsqrt] at hne
  exact hne hk.symm

private theorem factorial_add_one_not_tetranacci_square_of_lt (m : ℕ) (hm : m < 28) (n : ℕ) :
    Nat.factorial m + 1 ≠ tetranacci n ^ 2 := by
  intro h
  by_cases hm' : m = 4 ∨ m = 5 ∨ m = 7
  · rcases hm' with rfl | rfl | rfl
    · have hQ : tetranacci n = 5 := by
        have h2 := congrArg Nat.sqrt h
        rw [Nat.sqrt_eq'] at h2
        norm_num at h2
        exact h2.symm
      exact (tetranacci_ne_five_eleven_seventy_one n).1 hQ
    · have hQ : tetranacci n = 11 := by
        have h2 := congrArg Nat.sqrt h
        rw [Nat.sqrt_eq'] at h2
        norm_num at h2
        exact h2.symm
      exact (tetranacci_ne_five_eleven_seventy_one n).2.1 hQ
    · have hQ : tetranacci n = 71 := by
        have h2 := congrArg Nat.sqrt h
        rw [Nat.sqrt_eq'] at h2
        norm_num at h2
        exact h2.symm
      exact (tetranacci_ne_five_eleven_seventy_one n).2.2 hQ
  · have hnsq : ¬ IsSquare (Nat.factorial m + 1) := by
      interval_cases m <;>
        first
          | exact (hm' (Or.inl rfl)).elim
          | exact (hm' (Or.inr (Or.inl rfl))).elim
          | exact (hm' (Or.inr (Or.inr rfl))).elim
          | (refine not_isSquare_of_sqrt _ ?_; norm_num)
    exact hnsq ⟨tetranacci n, by rw [h, pow_two]⟩

end brocardRamanujan_not_tetranacci

/--
**The Brocard–Ramanujan equation has no Tetranacci solutions.** Let $(Q_n)_{n \ge 0}$ be the
Tetranacci sequence, given by $Q_0 = Q_1 = Q_2 = 0$, $Q_3 = 1$ and
$Q_{n+4} = Q_{n+3} + Q_{n+2} + Q_{n+1} + Q_n$ for $n \ge 0$. For all natural numbers $m$ and $n$,
$m! + 1 \ne Q_n^2$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci
Numbers*, INTEGERS 24 (2024), Article A92, Theorem 2.
-/
public theorem brocardRamanujan_not_tetranacci :
    ∀ m n : ℕ, Nat.factorial m + 1 ≠ tetranacci n ^ 2 := by
  intro m n h
  by_cases hn : n < 5
  · have hQ : tetranacci n ≤ 1 := by interval_cases n <;> decide
    have hpos : 1 ≤ Nat.factorial m := Nat.factorial_pos m
    have hle : tetranacci n ^ 2 ≤ 1 := by
      calc tetranacci n ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hQ 2
        _ = 1 := by norm_num
    omega
  · have hge : 5 ≤ n := by omega
    have hdvd : (2 : ℕ) ^ (m / 2) ∣ Nat.factorial m :=
      brocardRamanujan_not_tetranacci.two_pow_dvd_factorial m
    have hfact_eq : Nat.factorial m = tetranacci n ^ 2 - 1 := by
      have h1 : 1 ≤ tetranacci n ^ 2 := by
        have h5 : tetranacci 5 = 2 := rfl
        have hmono := brocardRamanujan_not_tetranacci.tetranacci_mono hge
        have h2 : (2 : ℕ) ≤ tetranacci n := by omega
        calc (1 : ℕ) ≤ 2 ^ 2 := by norm_num
          _ ≤ tetranacci n ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    have hle_fact : m / 2 ≤ (tetranacci n ^ 2 - 1).factorization 2 := by
      rw [← hfact_eq]
      exact (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 2)
        (Nat.factorial_pos m).ne').mp hdvd
    have hpow : (2 : ℕ) ^ (m / 2) ≤
        (2 : ℕ) ^ ((tetranacci n ^ 2 - 1).factorization 2) :=
      Nat.pow_le_pow_right (by norm_num) hle_fact
    have hup := brocardRamanujan_not_tetranacci.pow_factorization_le n hge
    have hindex := brocardRamanujan_not_tetranacci.tetranacci_index_le m n h.symm
    have hm2 : m * m = m ^ 2 := (pow_two m).symm
    have hbound : (2 : ℕ) ^ (m / 2) ≤ 8 * m ^ 2 + 144 := by omega
    have hm28 : m < 28 :=
      brocardRamanujan_not_tetranacci.lt_twenty_eight_of_pow_le m hbound
    exact brocardRamanujan_not_tetranacci.factorial_add_one_not_tetranacci_square_of_lt
      m hm28 n h

end MetaMathlibExt
