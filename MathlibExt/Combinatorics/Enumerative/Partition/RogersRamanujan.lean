/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Instances.Rat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.GaussianBinomial

@[expose] public section

section

namespace MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

/-! ## Gaussian binomial infrastructure -/

/-- In `ℚ⟦X⟧`, if `constantCoeff Q = 0` then `constantCoeff (qPochFin Q m) = 1`. -/
private theorem rrQPoch_constantCoeff (Q : PowerSeries ℚ)
    (hQ : PowerSeries.constantCoeff Q = 0) (m : ℕ) :
    PowerSeries.constantCoeff (qPochFin Q m) = 1 := by
  unfold qPochFin
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i _
  rw [map_sub, map_one, map_pow]
  rw [hQ]
  simp

private theorem rrQPoch_constantCoeff_ne_zero (Q : PowerSeries ℚ)
    (hQ : PowerSeries.constantCoeff Q = 0) (m : ℕ) :
    PowerSeries.constantCoeff (qPochFin Q m) ≠ 0 := by
  rw [rrQPoch_constantCoeff Q hQ m]
  exact one_ne_zero

private theorem rrQPoch_ne_zero (Q : PowerSeries ℚ)
    (hQ : PowerSeries.constantCoeff Q = 0) (m : ℕ) :
    qPochFin Q m ≠ 0 := by
  intro hcon
  have hcc := congrArg PowerSeries.constantCoeff hcon
  rw [rrQPoch_constantCoeff Q hQ m] at hcc
  simp at hcc

private theorem rrQPoch_mul_inv (Q : PowerSeries ℚ)
    (hQ : PowerSeries.constantCoeff Q = 0) (m : ℕ) :
    qPochFin Q m * (qPochFin Q m)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (rrQPoch_constantCoeff_ne_zero Q hQ m)

private theorem rrQPoch_inv_mul (Q : PowerSeries ℚ)
    (hQ : PowerSeries.constantCoeff Q = 0) (m : ℕ) :
    (qPochFin Q m)⁻¹ * qPochFin Q m = 1 :=
  PowerSeries.inv_mul_cancel _ (rrQPoch_constantCoeff_ne_zero Q hQ m)

/-- Inverse form: for `k ≤ M`,
`gaussBinom Q M k = qPochFin Q M * (qPochFin Q k)⁻¹ * (qPochFin Q (M-k))⁻¹`. -/
private theorem rrQBinom_eq_rrQPoch_mul_inv (Q : PowerSeries ℚ)
    (hQ : PowerSeries.constantCoeff Q = 0) (M k : ℕ) (h : k ≤ M) :
    gaussBinom Q M k
      = qPochFin Q M * (qPochFin Q k)⁻¹ * (qPochFin Q (M - k))⁻¹ := by
  have hprod := gaussBinom_mul_qPochFin_mul_qPochFin Q M k h
  have hk := rrQPoch_ne_zero Q hQ k
  have hMk := rrQPoch_ne_zero Q hQ (M - k)
  have key : gaussBinom Q M k * (qPochFin Q k * qPochFin Q (M - k))
      = (qPochFin Q M * (qPochFin Q k)⁻¹ * (qPochFin Q (M - k))⁻¹)
        * (qPochFin Q k * qPochFin Q (M - k)) := by
    have hexp : gaussBinom Q M k * (qPochFin Q k * qPochFin Q (M - k))
        = gaussBinom Q M k * qPochFin Q k * qPochFin Q (M - k) := by
      ring
    rw [hexp, hprod]
    have h1 : qPochFin Q M * (qPochFin Q k)⁻¹ * (qPochFin Q (M - k))⁻¹
          * (qPochFin Q k * qPochFin Q (M - k)) = qPochFin Q M := by
      calc qPochFin Q M * (qPochFin Q k)⁻¹ * (qPochFin Q (M - k))⁻¹
              * (qPochFin Q k * qPochFin Q (M - k))
            = qPochFin Q M * ((qPochFin Q k)⁻¹ * qPochFin Q k)
              * ((qPochFin Q (M - k))⁻¹ * qPochFin Q (M - k)) := by
            ring
          _ = qPochFin Q M := by
            rw [rrQPoch_inv_mul Q hQ k, rrQPoch_inv_mul Q hQ (M - k)]
            simp
    rw [h1]
  have hW : qPochFin Q k * qPochFin Q (M - k) ≠ 0 := mul_ne_zero hk hMk
  exact mul_right_cancel₀ hW key

/-- Symmetry in `ℚ⟦X⟧`: `gaussBinom Q M k = gaussBinom Q M (M - k)` for `k ≤ M`. -/
private theorem rrQBinom_symm (Q : PowerSeries ℚ)
    (hQ : PowerSeries.constantCoeff Q = 0) (M k : ℕ) (h : k ≤ M) :
    gaussBinom Q M k = gaussBinom Q M (M - k) := by
  rw [rrQBinom_eq_rrQPoch_mul_inv Q hQ M k h,
    rrQBinom_eq_rrQPoch_mul_inv Q hQ M (M - k) (Nat.sub_le M k)]
  have hkM : M - (M - k) = k := Nat.sub_sub_self h
  rw [hkM]
  ring

/-- Second Pascal rule in `ℚ⟦X⟧`: `gaussBinom Q (M+1) (k+1)`
`= gaussBinom Q M (k+1) + Q^(M-k) * gaussBinom Q M k`. -/
private theorem rrQBinom_succ_succ' (Q : PowerSeries ℚ)
    (hQ : PowerSeries.constantCoeff Q = 0) (M k : ℕ) :
    gaussBinom Q (M + 1) (k + 1)
      = gaussBinom Q M (k + 1) + Q ^ (M - k) * gaussBinom Q M k := by
  by_cases hle : k ≤ M
  · by_cases hkM : k = M
    · rw [hkM, gaussBinom_succ_succ,
        gaussBinom_eq_zero_of_lt Q M (M + 1) (Nat.lt_succ_self M),
        gaussBinom_self]
      simp
    · have h1 : k + 1 ≤ M := by omega
      -- use symmetry to reduce to first Pascal
      have hsym1 : gaussBinom Q (M + 1) (k + 1)
          = gaussBinom Q (M + 1) (M - k) := by
        have : M + 1 - (k + 1) = M - k := by omega
        rw [rrQBinom_symm Q hQ (M + 1) (k + 1) (by omega : k + 1 ≤ M + 1)]
        rw [this]
      have hMk : M - k = (M - k - 1) + 1 := by omega
      conv_lhs => rw [hsym1, hMk]
      rw [gaussBinom_succ_succ]
      have hsym2 : gaussBinom Q M (M - k - 1)
          = gaussBinom Q M (k + 1) := by
        have hle2 : M - k - 1 ≤ M := Nat.sub_le M (k + 1)
        have hback : M - (M - k - 1) = k + 1 := by omega
        rw [rrQBinom_symm Q hQ M (M - k - 1) hle2, hback]
      have hsym3 : gaussBinom Q M (M - k)
          = gaussBinom Q M k := by
        exact (rrQBinom_symm Q hQ M k hle).symm
      have hMk1 : M - k - 1 + 1 = M - k := by omega
      rw [hMk1, hsym2, hsym3]
  · have hlt : M < k := by omega
    have h0a : gaussBinom Q (M + 1) (k + 1) = 0 :=
      gaussBinom_eq_zero_of_lt Q (M + 1) (k + 1) (by omega)
    have h0b : gaussBinom Q M (k + 1) = 0 :=
      gaussBinom_eq_zero_of_lt Q M (k + 1) (by omega)
    have h0c : gaussBinom Q M k = 0 :=
      gaussBinom_eq_zero_of_lt Q M k hlt
    rw [h0a, h0b, h0c, mul_zero, add_zero]

/-! ## homogeneous Rothe identity, helpers -/

/-- Triangular addition: `C(k) + k = C(k+1)`. -/
private theorem rrChoose_add (k : ℕ) : k.choose 2 + k = (k + 1).choose 2 := by
  have h := Nat.choose_succ_succ' k 1
  rw [Nat.choose_one_right] at h
  have h2 : (1 : ℕ) + 1 = 2 := rfl
  rw [h2] at h
  omega

/-- Scaling the `x` argument by `Q` shifts the triangular exponent. -/
private theorem rrRothe_scale_term {R : Type*} [CommRing R] (Q x y : R)
    (m k : ℕ) :
    Q ^ (k.choose 2) * gaussBinom Q m k * (x * Q) ^ k * y ^ (m - k)
      = Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m - k) := by
  have hQQ : Q ^ (k.choose 2) * Q ^ k = Q ^ ((k + 1).choose 2) := by
    rw [← pow_add, rrChoose_add k]
  calc Q ^ (k.choose 2) * gaussBinom Q m k * (x * Q) ^ k * y ^ (m - k)
      = (Q ^ (k.choose 2) * Q ^ k)
        * (gaussBinom Q m k * x ^ k * y ^ (m - k)) := by
          rw [mul_pow]
          ring
    _ = Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m - k) := by
          rw [hQQ]
          ring

/-- One-step expansion of the `summand at k+1` using the Pascal rule. -/
private theorem rrRothe_succ_term {R : Type*} [CommRing R] (Q x y : R)
    (m k : ℕ) :
    Q ^ ((k + 1).choose 2) * gaussBinom Q (m + 1) (k + 1) * x ^ (k + 1)
        * y ^ (m + 1 - (k + 1))
      = x * (Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m - k))
        + Q ^ ((k + 1 + 1).choose 2) * gaussBinom Q m (k + 1) * x ^ (k + 1)
          * y ^ (m - k) := by
  have hsub : m + 1 - (k + 1) = m - k := by omega
  rw [hsub, gaussBinom_succ_succ]
  have hQQ2 : Q ^ ((k + 1).choose 2) * Q ^ (k + 1)
      = Q ^ ((k + 1 + 1).choose 2) := by
    rw [← pow_add]
    congr 1
    have h := rrChoose_add (k + 1)
    omega
  rw [pow_succ' x k, ← hQQ2]
  ring

/-- Homogeneous Rothe identity (finite q-binomial theorem). -/
private theorem rrRothe {R : Type*} [CommRing R] (Q x y : R) (m : ℕ) :
    ∏ i ∈ Finset.range m, (y + x * Q ^ i)
      = ∑ j ∈ Finset.range (m + 1),
        Q ^ (j.choose 2) * gaussBinom Q m j * x ^ j * y ^ (m - j) := by
  induction m generalizing x with
  | zero =>
      rw [Finset.prod_range_zero]
      have hc0 : (0 : ℕ).choose 2 = 0 := by decide
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      simp [hc0]
  | succ m ih =>
      set S : R := ∑ k ∈ Finset.range (m + 1),
        Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m - k) with hS
      set TT : R := ∑ k ∈ Finset.range (m + 1),
        Q ^ ((k + 1 + 1).choose 2) * gaussBinom Q m (k + 1) * x ^ (k + 1)
          * y ^ (m - k) with hT
      have hLHS : ∏ i ∈ Finset.range (m + 1), (y + x * Q ^ i)
          = S * (y + x) := by
        rw [Finset.prod_range_succ']
        have h0 : y + x * Q ^ 0 = y + x := by simp
        have hprod : (∏ k ∈ Finset.range m, (y + x * Q ^ (k + 1)))
            = ∑ k ∈ Finset.range (m + 1),
              Q ^ (k.choose 2) * gaussBinom Q m k * (x * Q) ^ k
                * y ^ (m - k) := by
          rw [← ih (x * Q)]
          apply Finset.prod_congr rfl
          intro j _
          rw [pow_succ']
          ring
        rw [h0, hprod]
        have hsum : (∑ k ∈ Finset.range (m + 1),
            Q ^ (k.choose 2) * gaussBinom Q m k * (x * Q) ^ k * y ^ (m - k))
            = S :=
          Finset.sum_congr rfl (fun k _ => rrRothe_scale_term Q x y m k)
        rw [hsum]
      have hRHS : ∑ k ∈ Finset.range (m + 1 + 1),
            Q ^ (k.choose 2) * gaussBinom Q (m + 1) k * x ^ k * y ^ (m + 1 - k)
          = (x * S + TT) + y ^ (m + 1) := by
        rw [Finset.sum_range_succ']
        have h0 : Q ^ ((0 : ℕ).choose 2) * gaussBinom Q (m + 1) 0 * x ^ (0 : ℕ)
            * y ^ (m + 1 - 0) = y ^ (m + 1) := by
          have hc0 : (0 : ℕ).choose 2 = 0 := by decide
          rw [hc0, gaussBinom_zero_right]
          simp
        have hrest : (∑ k ∈ Finset.range (m + 1),
            Q ^ ((k + 1).choose 2) * gaussBinom Q (m + 1) (k + 1) * x ^ (k + 1)
              * y ^ (m + 1 - (k + 1))) = x * S + TT := by
          have hcongr : (∑ k ∈ Finset.range (m + 1),
              Q ^ ((k + 1).choose 2) * gaussBinom Q (m + 1) (k + 1) * x ^ (k + 1)
                * y ^ (m + 1 - (k + 1)))
              = ∑ k ∈ Finset.range (m + 1),
                (x * (Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k
                  * y ^ (m - k))
                  + Q ^ ((k + 1 + 1).choose 2) * gaussBinom Q m (k + 1)
                    * x ^ (k + 1) * y ^ (m - k)) :=
            Finset.sum_congr rfl (fun k _ => rrRothe_succ_term Q x y m k)
          rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, ← hS, ← hT]
        rw [hrest, h0]
      have hTRel : TT + y ^ (m + 1) = y * S := by
        have hU1 := Finset.sum_range_succ
          (fun k => Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k
            * y ^ (m + 1 - k)) (m + 1)
        have hYS : (∑ k ∈ Finset.range (m + 1),
            Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m + 1 - k))
            = y * S := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hkle : k ≤ m := by
            have hlt : k < m + 1 := Finset.mem_range.mp hk
            omega
          have hsub : m + 1 - k = (m - k) + 1 := by omega
          rw [hsub, pow_succ]
          ring
        have hM1 : Q ^ ((m + 1 + 1).choose 2) * gaussBinom Q m (m + 1)
            * x ^ (m + 1) * y ^ (m + 1 - (m + 1)) = 0 := by
          rw [gaussBinom_eq_zero_of_lt Q m (m + 1) (Nat.lt_succ_self m)]
          simp
        rw [hYS, hM1, add_zero] at hU1
        have hU2 := Finset.sum_range_succ'
          (fun k => Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k
            * y ^ (m + 1 - k)) (m + 1)
        have hTT : (∑ k ∈ Finset.range (m + 1),
            Q ^ ((k + 1 + 1).choose 2) * gaussBinom Q m (k + 1) * x ^ (k + 1)
              * y ^ (m + 1 - (k + 1))) = TT := by
          apply Finset.sum_congr rfl
          intro k _
          have hsub : m + 1 - (k + 1) = m - k := by omega
          rw [hsub]
        have h00 : Q ^ ((0 + 1).choose 2) * gaussBinom Q m 0 * x ^ (0 : ℕ)
            * y ^ (m + 1 - 0) = y ^ (m + 1) := by
          have hc1 : (0 + 1 : ℕ).choose 2 = 0 := by decide
          rw [hc1, gaussBinom_zero_right]
          simp
        rw [hTT, h00] at hU2
        linear_combination hU1 - hU2
      calc ∏ i ∈ Finset.range (m + 1), (y + x * Q ^ i)
          = S * (y + x) := hLHS
        _ = (x * S + TT) + y ^ (m + 1) := by linear_combination -hTRel
        _ = ∑ k ∈ Finset.range (m + 1 + 1),
              Q ^ (k.choose 2) * gaussBinom Q (m + 1) k * x ^ k
                * y ^ (m + 1 - k) :=
            hRHS.symm

/-- Fold a sum over `range (2n+1)` around `n`. -/
private theorem rrSum_fold (M : Type*) [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n + 1), f j
      = f n + ∑ r ∈ Finset.range n, (f (n + (r + 1)) + f (n - (r + 1))) := by
  have h2n : 2 * n + 1 = n + (n + 1) := by omega
  rw [h2n, Finset.sum_range_add]
  have hlow : ∑ i ∈ Finset.range n, f i
      = ∑ r ∈ Finset.range n, f (n - (r + 1)) := by
    have h := Finset.sum_range_reflect (fun r => f (n - (r + 1))) n
    rw [← h]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    congr 1
    omega
  have hhigh : ∑ i ∈ Finset.range (n + 1), f (n + i)
      = f n + ∑ r ∈ Finset.range n, f (n + (r + 1)) := by
    rw [Finset.sum_range_succ', Nat.add_zero]
    ac_rfl
  rw [hlow, hhigh, Finset.sum_add_distrib]
  ac_rfl

/-! ## truncation lemmas -/

/-- `X^c` has zero constant coefficient for `c ≥ 1`. -/
private theorem rrXpow_constCoeff (c : ℕ) (hc : 1 ≤ c) :
    PowerSeries.constantCoeff (PowerSeries.X ^ c : PowerSeries ℚ) = 0 := by
  rw [map_pow, PowerSeries.constantCoeff_X]
  exact zero_pow (by omega : c ≠ 0)

/-- If `X^s ∣ f` and `X^t ∣ g - 1` then `X^(s+t) ∣ f * g - f`. -/
private theorem rrDvd_mul_sub (s t : ℕ) (f g : PowerSeries ℚ)
    (hf : PowerSeries.X ^ s ∣ f) (hg : PowerSeries.X ^ t ∣ g - 1) :
    PowerSeries.X ^ (s + t) ∣ f * g - f := by
  have heq : f * g - f = f * (g - 1) := by ring
  rw [heq, pow_add]
  exact mul_dvd_mul hf hg

/-- A tail product of `(1 - X^(e + c·t))` factors is `1` mod `X^e`. -/
private theorem rrXpow_dvd_tail_prod_sub_one (c e K : ℕ) :
    PowerSeries.X ^ e ∣ ((∏ t ∈ Finset.range K,
      (1 - PowerSeries.X ^ (e + c * t) : PowerSeries ℚ)) - 1) := by
  induction K with
  | zero =>
      rw [Finset.prod_range_zero, sub_self]
      exact dvd_zero _
  | succ K ih =>
      rw [Finset.prod_range_succ]
      have hexp : ∀ A t : PowerSeries ℚ, A * (1 - t) - 1
          = (A - 1) - A * t := by
        intro A t
        ring
      rw [hexp]
      have hpow : (PowerSeries.X : PowerSeries ℚ) ^ (e + c * K)
          = PowerSeries.X ^ e * PowerSeries.X ^ (c * K) := by
        rw [← pow_add]
      rw [hpow]
      have hdiv : PowerSeries.X ^ e
          ∣ (∏ t ∈ Finset.range K,
              (1 - PowerSeries.X ^ (e + c * t) : PowerSeries ℚ))
            * (PowerSeries.X ^ e * PowerSeries.X ^ (c * K)) := by
        have hrw : (∏ t ∈ Finset.range K,
                (1 - PowerSeries.X ^ (e + c * t) : PowerSeries ℚ))
              * (PowerSeries.X ^ e * PowerSeries.X ^ (c * K))
            = ((∏ t ∈ Finset.range K,
                (1 - PowerSeries.X ^ (e + c * t) : PowerSeries ℚ))
              * PowerSeries.X ^ (c * K)) * PowerSeries.X ^ e := by
          ring
        rw [hrw]
        exact dvd_mul_left _ _
      exact dvd_sub ih hdiv

/-- Stability of finite q-Pochhammers, one-sided version. -/
private theorem rrXpow_dvd_qPoch_sub_of_le (c a K : ℕ) :
    PowerSeries.X ^ (c * (a + 1))
      ∣ qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
        - qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) (a + K) := by
  have hsplit : qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) (a + K)
      = qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
        * ∏ t ∈ Finset.range K,
          (1 - (PowerSeries.X ^ c : PowerSeries ℚ) ^ (a + 1 + t)) := by
    unfold qPochFin
    rw [Finset.prod_range_add]
    congr 1
    apply Finset.prod_congr rfl
    intro t _
    have he : (a + t) + 1 = a + 1 + t := by omega
    rw [he]
  have hdecomp : qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
        - qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
          * ∏ t ∈ Finset.range K,
            (1 - (PowerSeries.X ^ c : PowerSeries ℚ) ^ (a + 1 + t))
      = qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
        * (1 - ∏ t ∈ Finset.range K,
          (1 - (PowerSeries.X ^ c : PowerSeries ℚ) ^ (a + 1 + t))) := by
    ring
  have htail : (∏ t ∈ Finset.range K,
        (1 - (PowerSeries.X ^ c : PowerSeries ℚ) ^ (a + 1 + t)))
        = ∏ t ∈ Finset.range K,
          (1 - PowerSeries.X ^ (c * (a + 1) + c * t)) := by
    apply Finset.prod_congr rfl
    intro t _
    have he : (PowerSeries.X ^ c : PowerSeries ℚ) ^ (a + 1 + t)
        = PowerSeries.X ^ (c * (a + 1) + c * t) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [he]
  rw [hsplit, hdecomp, htail]
  have h1 : (PowerSeries.X : PowerSeries ℚ) ^ 0
      ∣ qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a := by
    rw [pow_zero]
    exact one_dvd _
  have h2 : (PowerSeries.X : PowerSeries ℚ) ^ (c * (a + 1))
      ∣ 1 - ∏ t ∈ Finset.range K,
        (1 - PowerSeries.X ^ (c * (a + 1) + c * t)) := by
    have h := rrXpow_dvd_tail_prod_sub_one c (c * (a + 1)) K
    exact (by simpa only [neg_sub] using dvd_neg.mpr h)
  have hmul := mul_dvd_mul h1 h2
  rw [pow_zero, one_mul] at hmul
  exact hmul

/-- Stability of finite q-Pochhammers: `X^(c·(min a b + 1))` divides the difference. -/
private theorem rrXpow_dvd_qPoch_sub (c a b : ℕ) :
    PowerSeries.X ^ (c * (min a b + 1))
      ∣ qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
        - qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) b := by
  rcases le_total a b with h | h
  · obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le h
    have hmin : min a (a + K) = a := Nat.min_eq_left (Nat.le_add_right a K)
    rw [hmin]
    exact rrXpow_dvd_qPoch_sub_of_le c a K
  · obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le h
    have hmin : min (b + K) b = b := Nat.min_eq_right (Nat.le_add_right b K)
    rw [hmin]
    have hmain := rrXpow_dvd_qPoch_sub_of_le c b K
    have hneg : qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) (b + K)
          - qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) b
        = -(qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) b
          - qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) (b + K)) := by
      ring
    rw [hneg]
    exact dvd_neg.mpr hmain

/-- Stability of the normalized ratio: `X^(c·(min a b + 1))` divides the ratio minus one. -/
private theorem rrXpow_dvd_qPoch_mul_inv_sub_one (c a b : ℕ) (hc : 1 ≤ c) :
    PowerSeries.X ^ (c * (min a b + 1))
      ∣ qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
        * (qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) b)⁻¹ - 1 := by
  have hQ : PowerSeries.constantCoeff (PowerSeries.X ^ c : PowerSeries ℚ) = 0 :=
    rrXpow_constCoeff c hc
  have hmain := rrXpow_dvd_qPoch_sub c a b
  have hcancel : qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
        * (qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) b)⁻¹ - 1
      = (qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) a
        - qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) b)
        * (qPochFin (PowerSeries.X ^ c : PowerSeries ℚ) b)⁻¹ := by
    rw [sub_mul, rrQPoch_mul_inv _ hQ b]
  rw [hcancel]
  exact dvd_mul_of_dvd_left hmain _

/-! ## key q-Chu–Vandermonde lemma -/

/-- Per-term identity for the Bailey-chain induction step. -/
private theorem rrChuVander_term {R : Type*} [CommRing R] (Q : R) (M a i : ℕ)
    (hi : i ≤ M) :
    Q ^ ((i + 1) ^ 2 + a * (i + 1)) * gaussBinom Q (M + 1) (i + 1)
      * ∏ t ∈ Finset.range (M + 1 - (i + 1)), (1 - Q ^ (a + (i + 1) + 1 + t))
    = (Q ^ (i ^ 2 + (a + 1) * i) * gaussBinom Q M i
        * ∏ t ∈ Finset.range (M - i), (1 - Q ^ ((a + 1) + i + 1 + t)))
      + ((Q ^ ((i + 1) ^ 2 + (a + 1) * (i + 1)) * gaussBinom Q M (i + 1)
          * ∏ t ∈ Finset.range (M + 1 - (i + 1)), (1 - Q ^ (a + (i + 1) + 1 + t)))
        - (Q ^ (i ^ 2 + (a + 1) * i) * gaussBinom Q M i
          * ∏ t ∈ Finset.range (M + 1 - i), (1 - Q ^ (a + i + 1 + t)))) := by
  have hQ1 : (∏ t ∈ Finset.range (M + 1 - (i + 1)),
        (1 - Q ^ (a + (i + 1) + 1 + t)))
      = ∏ t ∈ Finset.range (M - i), (1 - Q ^ ((a + 1) + i + 1 + t)) := by
    have hr : M + 1 - (i + 1) = M - i := by omega
    rw [hr]
    apply Finset.prod_congr rfl
    intro t _
    have hexp : a + (i + 1) + 1 + t = (a + 1) + i + 1 + t := by omega
    rw [hexp]
  have hQ0 : (∏ t ∈ Finset.range (M + 1 - i), (1 - Q ^ (a + i + 1 + t)))
      = (∏ t ∈ Finset.range (M - i), (1 - Q ^ ((a + 1) + i + 1 + t)))
        * (1 - Q ^ (a + i + 1)) := by
    have hr : M + 1 - i = (M - i) + 1 := by omega
    rw [hr, Finset.prod_range_succ']
    congr 1
    apply Finset.prod_congr rfl
    intro t _
    have hexp : a + i + 1 + (t + 1) = (a + 1) + i + 1 + t := by omega
    rw [hexp]
  have hG : gaussBinom Q (M + 1) (i + 1)
      = gaussBinom Q M i + Q ^ (i + 1) * gaussBinom Q M (i + 1) :=
    gaussBinom_succ_succ Q M i
  have e1 : (i + 1) ^ 2 + a * (i + 1) = (i ^ 2 + (a + 1) * i) + (a + i + 1) := by
    ring
  have e2 : (i + 1) ^ 2 + (a + 1) * (i + 1)
      = ((i + 1) ^ 2 + a * (i + 1)) + (i + 1) := by
    ring
  have qE1 : Q ^ ((i + 1) ^ 2 + a * (i + 1))
      = Q ^ (i ^ 2 + (a + 1) * i) * Q ^ (a + i + 1) := by
    rw [← pow_add, e1]
  have qE1' : Q ^ ((i + 1) ^ 2 + (a + 1) * (i + 1))
      = Q ^ ((i + 1) ^ 2 + a * (i + 1)) * Q ^ (i + 1) := by
    rw [← pow_add, e2]
  rw [hG, hQ1, hQ0, qE1', qE1]
  ring

/-- Key q-Chu–Vandermonde-type sum: `S(M, a) = 1` for all `M`, `a`. -/
private theorem rrChuVander {R : Type*} [CommRing R] (Q : R) (M a : ℕ) :
    (∑ i ∈ Finset.range (M + 1),
      Q ^ (i ^ 2 + a * i) * gaussBinom Q M i
        * ∏ t ∈ Finset.range (M - i), (1 - Q ^ (a + i + 1 + t))) = 1 := by
  induction M generalizing a with
  | zero =>
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      have e0 : (0 : ℕ) ^ 2 + a * 0 = 0 := by ring
      rw [e0]
      simp
  | succ M ih =>
      rw [Finset.sum_range_succ']
      have hR : (∑ i ∈ Finset.range (M + 1),
            Q ^ ((i + 1) ^ 2 + a * (i + 1)) * gaussBinom Q (M + 1) (i + 1)
              * ∏ t ∈ Finset.range (M + 1 - (i + 1)),
                (1 - Q ^ (a + (i + 1) + 1 + t)))
          = (∑ i ∈ Finset.range (M + 1),
              Q ^ (i ^ 2 + (a + 1) * i) * gaussBinom Q M i
                * ∏ t ∈ Finset.range (M - i), (1 - Q ^ ((a + 1) + i + 1 + t)))
            + ∑ i ∈ Finset.range (M + 1),
              ((Q ^ ((i + 1) ^ 2 + (a + 1) * (i + 1)) * gaussBinom Q M (i + 1)
                * ∏ t ∈ Finset.range (M + 1 - (i + 1)),
                  (1 - Q ^ (a + (i + 1) + 1 + t)))
              - (Q ^ (i ^ 2 + (a + 1) * i) * gaussBinom Q M i
                * ∏ t ∈ Finset.range (M + 1 - i), (1 - Q ^ (a + i + 1 + t)))) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl
          (fun i hi => rrChuVander_term Q M a i (by
            have hlt : i < M + 1 := Finset.mem_range.mp hi
            omega))
      have hB : (∑ i ∈ Finset.range (M + 1),
            ((Q ^ ((i + 1) ^ 2 + (a + 1) * (i + 1)) * gaussBinom Q M (i + 1)
              * ∏ t ∈ Finset.range (M + 1 - (i + 1)),
                (1 - Q ^ (a + (i + 1) + 1 + t)))
            - (Q ^ (i ^ 2 + (a + 1) * i) * gaussBinom Q M i
              * ∏ t ∈ Finset.range (M + 1 - i), (1 - Q ^ (a + i + 1 + t)))))
          = (Q ^ ((M + 1) ^ 2 + (a + 1) * (M + 1)) * gaussBinom Q M (M + 1)
              * ∏ t ∈ Finset.range (M + 1 - (M + 1)),
                (1 - Q ^ (a + (M + 1) + 1 + t)))
            - (Q ^ ((0 : ℕ) ^ 2 + (a + 1) * 0) * gaussBinom Q M 0
              * ∏ t ∈ Finset.range (M + 1 - 0), (1 - Q ^ (a + 0 + 1 + t))) :=
        Finset.sum_range_sub
          (fun k => Q ^ (k ^ 2 + (a + 1) * k) * gaussBinom Q M k
            * ∏ t ∈ Finset.range (M + 1 - k), (1 - Q ^ (a + k + 1 + t))) (M + 1)
      have hTop : Q ^ ((M + 1) ^ 2 + (a + 1) * (M + 1)) * gaussBinom Q M (M + 1)
          * ∏ t ∈ Finset.range (M + 1 - (M + 1)),
            (1 - Q ^ (a + (M + 1) + 1 + t)) = 0 := by
        rw [gaussBinom_eq_zero_of_lt Q M (M + 1) (Nat.lt_succ_self M)]
        simp
      have hBot : Q ^ ((0 : ℕ) ^ 2 + (a + 1) * 0) * gaussBinom Q M 0
          * ∏ t ∈ Finset.range (M + 1 - 0), (1 - Q ^ (a + 0 + 1 + t))
          = Q ^ ((0 : ℕ) ^ 2 + a * 0) * gaussBinom Q (M + 1) 0
            * ∏ t ∈ Finset.range (M + 1 - 0), (1 - Q ^ (a + 0 + 1 + t)) := by
        have e0 : (0 : ℕ) ^ 2 + (a + 1) * 0 = (0 : ℕ) ^ 2 + a * 0 := by omega
        rw [gaussBinom_zero_right, gaussBinom_zero_right, e0]
      have hS := ih (a + 1)
      rw [hR, hB, hTop, hBot, hS]
      ring

/-! ## Bailey kernel notation and unit facts -/

/-- `P(m)`: the finite q-Pochhammer at `Q = X`. -/
private noncomputable def rrP (m : ℕ) : PowerSeries ℚ := qPochFin PowerSeries.X m

/-- `ip(m)`: the inverse of `P(m)`. -/
private noncomputable def rrIp (m : ℕ) : PowerSeries ℚ := (rrP m)⁻¹

/-- `P5(m)`: the finite q-Pochhammer at `Q = X^5`. -/
private noncomputable def rrP5 (m : ℕ) : PowerSeries ℚ := qPochFin (PowerSeries.X ^ 5) m

/-- `ip5(m)`: the inverse of `P5(m)`. -/
private noncomputable def rrIp5 (m : ℕ) : PowerSeries ℚ := (rrP5 m)⁻¹

private theorem rrP_mul_ip (m : ℕ) : rrP m * rrIp m = 1 := by
  simp only [rrP, rrIp]
  exact rrQPoch_mul_inv _ PowerSeries.constantCoeff_X m

private theorem rrIp_mul_P (m : ℕ) : rrIp m * rrP m = 1 := by
  simp only [rrP, rrIp]
  exact rrQPoch_inv_mul _ PowerSeries.constantCoeff_X m

private theorem rrP5_mul_ip5 (m : ℕ) : rrP5 m * rrIp5 m = 1 := by
  simp only [rrP5, rrIp5]
  exact rrQPoch_mul_inv _ (rrXpow_constCoeff 5 (by omega)) m

private theorem rrIp5_mul_P5 (m : ℕ) : rrIp5 m * rrP5 m = 1 := by
  simp only [rrP5, rrIp5]
  exact rrQPoch_inv_mul _ (rrXpow_constCoeff 5 (by omega)) m

/-- Splitting a q-Pochhammer at an interior point. -/
private theorem rrP_mul_tail (n m : ℕ) :
    rrP n * (∏ t ∈ Finset.range m, (1 - PowerSeries.X ^ ((n + t) + 1)))
      = rrP (n + m) := by
  simp only [rrP, qPochFin]
  rw [← Finset.prod_range_add]

/-- Splitting a `q^5`-Pochhammer at an interior point. -/
private theorem rrP5_mul_tail (n m : ℕ) :
    rrP5 n * (∏ t ∈ Finset.range m,
      (1 - (PowerSeries.X ^ 5 : PowerSeries ℚ) ^ ((n + t) + 1)))
      = rrP5 (n + m) := by
  simp only [rrP5, qPochFin]
  rw [← Finset.prod_range_add]

/-- Bailey lemma kernel at `a = 1`, rational form. -/
private theorem rrBailey_kernel (r M : ℕ) :
    (∑ i ∈ Finset.range (M + 1),
      PowerSeries.X ^ ((r + i) ^ 2) * rrIp (M - i) * rrIp i * rrIp (2 * r + i))
    = PowerSeries.X ^ (r ^ 2) * rrIp M * rrIp (M + 2 * r) := by
  have hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℚ) = 0 :=
    PowerSeries.constantCoeff_X
  have hG : ∀ i ∈ Finset.range (M + 1),
      gaussBinom (PowerSeries.X : PowerSeries ℚ) M i
        = rrP M * rrIp i * rrIp (M - i) := by
    intro i hi
    have hiM : i ≤ M := by
      have hlt : i < M + 1 := Finset.mem_range.mp hi
      omega
    have h := rrQBinom_eq_rrQPoch_mul_inv _ hX M i hiM
    simp only [rrP, rrIp]
    exact h
  have hPi : ∀ i ∈ Finset.range (M + 1),
      (∏ t ∈ Finset.range (M - i), (1 - PowerSeries.X ^ (2 * r + i + 1 + t)))
      = rrP (M + 2 * r) * rrIp (2 * r + i) := by
    intro i hi
    have hiM : i ≤ M := by
      have hlt : i < M + 1 := Finset.mem_range.mp hi
      omega
    have hM : (2 * r + i) + (M - i) = M + 2 * r := by omega
    have hsplit := rrP_mul_tail (2 * r + i) (M - i)
    rw [hM] at hsplit
    have hbody : (∏ t ∈ Finset.range (M - i),
          (1 - (PowerSeries.X : PowerSeries ℚ) ^ (((2 * r + i) + t) + 1)))
        = ∏ t ∈ Finset.range (M - i),
          (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * r + i + 1 + t)) := by
      apply Finset.prod_congr rfl
      intro t _
      have hexp : ((2 * r + i) + t) + 1 = 2 * r + i + 1 + t := by omega
      rw [hexp]
    rw [hbody] at hsplit
    have hcancel : rrIp (2 * r + i) * rrP (2 * r + i) = 1 := rrIp_mul_P _
    have e2 : (∏ t ∈ Finset.range (M - i),
          (1 - PowerSeries.X ^ (2 * r + i + 1 + t)))
        = rrIp (2 * r + i) * rrP (M + 2 * r) := by
      have hmul : rrIp (2 * r + i) * (rrP (2 * r + i)
          * ∏ t ∈ Finset.range (M - i), (1 - PowerSeries.X ^ (2 * r + i + 1 + t)))
          = ∏ t ∈ Finset.range (M - i),
            (1 - PowerSeries.X ^ (2 * r + i + 1 + t)) := by
        rw [← mul_assoc, hcancel, one_mul]
      rw [← hmul, hsplit]
    rw [e2]
    exact mul_comm _ _
  have hper : ∀ i ∈ Finset.range (M + 1),
      (PowerSeries.X ^ (i ^ 2 + (2 * r) * i) * gaussBinom PowerSeries.X M i
        * ∏ t ∈ Finset.range (M - i), (1 - PowerSeries.X ^ ((2 * r) + i + 1 + t)))
        * PowerSeries.X ^ (r ^ 2)
      = (PowerSeries.X ^ ((r + i) ^ 2) * rrIp (M - i) * rrIp i * rrIp (2 * r + i))
        * (rrP M * rrP (M + 2 * r)) := by
    intro i hi
    rw [hG i hi, hPi i hi]
    have hexp : (r + i) ^ 2 = r ^ 2 + (i ^ 2 + 2 * r * i) := by ring
    have qsplit : (PowerSeries.X : PowerSeries ℚ) ^ ((r + i) ^ 2)
        = (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2)
          * (PowerSeries.X : PowerSeries ℚ) ^ (i ^ 2 + 2 * r * i) := by
      rw [← pow_add, hexp]
    rw [qsplit]
    ring
  have hC0 : (∑ i ∈ Finset.range (M + 1),
        PowerSeries.X ^ (i ^ 2 + (2 * r) * i) * gaussBinom PowerSeries.X M i
          * ∏ t ∈ Finset.range (M - i),
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ ((2 * r) + i + 1 + t))) = 1 :=
    rrChuVander (PowerSeries.X : PowerSeries ℚ) M (2 * r)
  have h2 : (∑ i ∈ Finset.range (M + 1),
        (PowerSeries.X ^ ((r + i) ^ 2) * rrIp (M - i) * rrIp i * rrIp (2 * r + i))
          * (rrP M * rrP (M + 2 * r)))
      = (∑ i ∈ Finset.range (M + 1),
        (PowerSeries.X ^ (i ^ 2 + (2 * r) * i) * gaussBinom PowerSeries.X M i
          * ∏ t ∈ Finset.range (M - i),
            (1 - PowerSeries.X ^ ((2 * r) + i + 1 + t)))
          * PowerSeries.X ^ (r ^ 2)) :=
    Finset.sum_congr rfl (fun i hi => (hper i hi).symm)
  have hfin : (∑ i ∈ Finset.range (M + 1),
        PowerSeries.X ^ ((r + i) ^ 2) * rrIp (M - i) * rrIp i * rrIp (2 * r + i))
        * (rrP M * rrP (M + 2 * r)) = PowerSeries.X ^ (r ^ 2) := by
    rw [Finset.sum_mul, h2, ← Finset.sum_mul, hC0, one_mul]
  have hKK : (rrP M * rrP (M + 2 * r)) * (rrIp M * rrIp (M + 2 * r)) = 1 := by
    calc (rrP M * rrP (M + 2 * r)) * (rrIp M * rrIp (M + 2 * r))
        = (rrP M * rrIp M) * (rrP (M + 2 * r) * rrIp (M + 2 * r)) := by
          ring
      _ = 1 := by
          rw [rrP_mul_ip, rrP_mul_ip, mul_one]
  have e1 : (∑ i ∈ Finset.range (M + 1),
        PowerSeries.X ^ ((r + i) ^ 2) * rrIp (M - i) * rrIp i * rrIp (2 * r + i))
      = (∑ i ∈ Finset.range (M + 1),
          PowerSeries.X ^ ((r + i) ^ 2) * rrIp (M - i) * rrIp i
            * rrIp (2 * r + i))
        * ((rrP M * rrP (M + 2 * r)) * (rrIp M * rrIp (M + 2 * r))) := by
    rw [hKK, mul_one]
  have e2 : (∑ i ∈ Finset.range (M + 1),
        PowerSeries.X ^ ((r + i) ^ 2) * rrIp (M - i) * rrIp i
          * rrIp (2 * r + i))
        * ((rrP M * rrP (M + 2 * r)) * (rrIp M * rrIp (M + 2 * r)))
      = PowerSeries.X ^ (r ^ 2) * rrIp M * rrIp (M + 2 * r) := by
    linear_combination hfin * (rrIp M * rrIp (M + 2 * r))
  exact e1.trans e2

/-! ## Shared notation for the Bailey chain and products -/

/-- Folded Jacobi-triple-product summand. -/
private noncomputable def rrEps (c b r : ℕ) : PowerSeries ℚ :=
  if r = 0 then 1
  else (-1 : PowerSeries ℚ) ^ r
    * ((PowerSeries.X : PowerSeries ℚ) ^ (c * (r.choose 2) + b * r)
      + (PowerSeries.X : PowerSeries ℚ) ^ (c * (r.choose 2) + (c - b) * r))

/-- Unit summand `u(r) = ε(1, 0, r)`. -/
private noncomputable def rrU (r : ℕ) : PowerSeries ℚ := rrEps 1 0 r

/-- Theta summand `θ(r) = ε(5, 2, r)`. -/
private noncomputable def rrTheta (r : ℕ) : PowerSeries ℚ := rrEps 5 2 r

/-- Partial theta sum `T(n)`. -/
private noncomputable def rrT (n : ℕ) : PowerSeries ℚ :=
  ∑ r ∈ Finset.range (n + 1), rrTheta r

/-- Finite product side `Π5(n)`. -/
private noncomputable def rrPi5 (n : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ Finset.range n,
    ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 2))
      * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 3))
      * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 5)))

/-- Good residues `1, 4 mod 5`. -/
private def rrGood (m : ℕ) : Prop := m % 5 = 1 ∨ m % 5 = 4

private instance : DecidablePred rrGood := fun m =>
  inferInstanceAs (Decidable (m % 5 = 1 ∨ m % 5 = 4))

/-- Finite Euler factor `E(n)`. -/
private noncomputable def rrE (n : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ Finset.range (5 * n),
    (if rrGood (i + 1) then 1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1) else 1)

/-- Gap-2 condition on a finset. -/
private def rrGap2 (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a < b → a + 2 ≤ b

private noncomputable instance : DecidablePred rrGap2 := fun _ => Classical.propDecidable _

/-- Left card `A(N)`, literally the Wanted left card. -/
private def rrA (N : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition N =>
    p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b)).card

/-- Right card `B(N)`, literally the Wanted right card. -/
private def rrB (N : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition N =>
    ∀ m ∈ p.parts, m % 5 = 1 ∨ m % 5 = 4)).card

/-- Left generating series `FA`. -/
private noncomputable def rrFA : PowerSeries ℚ :=
  PowerSeries.mk fun N => ((rrA N : ℕ) : ℚ)

/-- Right generating series `FB`. -/
private noncomputable def rrFB : PowerSeries ℚ :=
  PowerSeries.mk fun N => ((rrB N : ℕ) : ℚ)

/-! ## Bailey step -/

/-- Bailey lemma step at `a = 1`, finite form. -/
private theorem rrBailey_step (α β : ℕ → PowerSeries ℚ)
    (h : ∀ n, β n
      = ∑ r ∈ Finset.range (n + 1), α r * rrIp (n - r) * rrIp (n + r))
    (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * β j * rrIp (n - j)
      = ∑ r ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * α r * rrIp (n - r)
          * rrIp (n + r) := by
  have hexpand : ∀ j ∈ Finset.range (n + 1),
      (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * β j * rrIp (n - j)
        = ∑ r ∈ Finset.range (j + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
            * (α r * rrIp (j - r) * rrIp (j + r)) * rrIp (n - j) := by
    intro j _
    rw [h j, Finset.mul_sum, Finset.sum_mul]
  have hLHS : (∑ j ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * β j * rrIp (n - j))
      = ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (j + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
          * (α r * rrIp (j - r) * rrIp (j + r)) * rrIp (n - j) :=
    Finset.sum_congr rfl hexpand
  have hmem : ∀ j r, (j ∈ Finset.range (n + 1) ∧ r ∈ Finset.range (j + 1))
      ↔ (j ∈ Finset.Ico r (n + 1) ∧ r ∈ Finset.range (n + 1)) := by
    intro j r
    simp only [Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hj, hr⟩
      exact ⟨⟨by omega, hj⟩, by omega⟩
    · rintro ⟨⟨hrj, hj⟩, _⟩
      exact ⟨hj, by omega⟩
  have hswap : (∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (j + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
          * (α r * rrIp (j - r) * rrIp (j + r)) * rrIp (n - j))
      = ∑ r ∈ Finset.range (n + 1), ∑ j ∈ Finset.Ico r (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
          * (α r * rrIp (j - r) * rrIp (j + r)) * rrIp (n - j) :=
    Finset.sum_comm' hmem
  have hIco : ∀ r ∈ Finset.range (n + 1),
      (∑ j ∈ Finset.Ico r (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
          * (α r * rrIp (j - r) * rrIp (j + r)) * rrIp (n - j))
      = ∑ i ∈ Finset.range (n + 1 - r),
        (PowerSeries.X : PowerSeries ℚ) ^ ((r + i) ^ 2)
          * (α r * rrIp ((r + i) - r) * rrIp ((r + i) + r))
          * rrIp (n - (r + i)) := by
    intro r _
    exact Finset.sum_Ico_eq_sum_range
      (fun j => (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
        * (α r * rrIp (j - r) * rrIp (j + r)) * rrIp (n - j)) r (n + 1)
  have hinner : ∀ r ∈ Finset.range (n + 1),
      (∑ i ∈ Finset.range (n + 1 - r),
        (PowerSeries.X : PowerSeries ℚ) ^ ((r + i) ^ 2)
          * (α r * rrIp ((r + i) - r) * rrIp ((r + i) + r))
          * rrIp (n - (r + i)))
      = (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * α r * rrIp (n - r)
        * rrIp (n + r) := by
    intro r hr
    have hrle : r ≤ n := by
      have hlt : r < n + 1 := Finset.mem_range.mp hr
      omega
    have hM : n + 1 - r = (n - r) + 1 := by omega
    rw [hM]
    have hker := rrBailey_kernel r (n - r)
    have hnr : (n - r) + 2 * r = n + r := by omega
    rw [hnr] at hker
    have hfactor : ∀ i ∈ Finset.range ((n - r) + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ ((r + i) ^ 2)
          * (α r * rrIp ((r + i) - r) * rrIp ((r + i) + r))
          * rrIp (n - (r + i))
        = α r * (((PowerSeries.X : PowerSeries ℚ) ^ ((r + i) ^ 2)
          * rrIp ((n - r) - i) * rrIp i * rrIp (2 * r + i))) := by
      intro i hi
      have hilt : i ≤ n - r := by
        have hlt : i < (n - r) + 1 := Finset.mem_range.mp hi
        omega
      have h1 : (r + i) - r = i := by omega
      have h2 : (r + i) + r = 2 * r + i := by omega
      have h3 : n - (r + i) = (n - r) - i := by omega
      rw [h1, h2, h3]
      ring
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
    calc α r * (∑ i ∈ Finset.range ((n - r) + 1),
            (PowerSeries.X : PowerSeries ℚ) ^ ((r + i) ^ 2)
              * rrIp ((n - r) - i) * rrIp i * rrIp (2 * r + i))
        = α r * ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrIp (n - r)
          * rrIp (n + r)) := by rw [hker]
      _ = (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * α r * rrIp (n - r)
          * rrIp (n + r) := by ring
  rw [hLHS, hswap]
  rw [Finset.sum_congr rfl hIco]
  exact Finset.sum_congr rfl hinner

/-! ## folded finite Jacobi triple product, helpers -/

/-- Addition formula for triangular numbers. -/
private theorem rrChoose_add_mul (a s : ℕ) :
    (a + s).choose 2 = a.choose 2 + a * s + s.choose 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
      have h1 : a + (s + 1) = (a + s) + 1 := by omega
      rw [h1, ← rrChoose_add (a + s), ih, ← rrChoose_add s]
      ring

/-- Twice triangular plus identity equals square. -/
private theorem rrTwo_choose_add_self (r : ℕ) : 2 * (r.choose 2) + r = r * r := by
  induction r with
  | zero => simp
  | succ s ih =>
      rw [← rrChoose_add s]
      have h2 : 2 * (s.choose 2 + s) + (s + 1)
          = (2 * s.choose 2 + s) + (2 * s + 1) := by
        ring
      rw [h2, ih]
      ring

/-- Plus exponent identity for the folded sum. -/
private theorem rrExp_plus (c b n r : ℕ) (h : r ≤ n) :
    c * ((n + r).choose 2) + b * (n + r) + c * n * (n - r)
      = (b * n + c * (n.choose 2) + c * n * n)
        + (c * (r.choose 2) + b * r) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h
  have hnsub : r + a - r = a := Nat.add_sub_cancel_left r a
  rw [hnsub]
  have h1 : ((r + a) + r).choose 2
      = (r + a).choose 2 + (r + a) * r + r.choose 2 :=
    rrChoose_add_mul (r + a) r
  have h2 : (r + a).choose 2 = r.choose 2 + r * a + a.choose 2 :=
    rrChoose_add_mul r a
  rw [h1, h2]
  ring

/-- Minus exponent identity for the folded sum. -/
private theorem rrExp_minus (c b n r : ℕ) (hle : r ≤ n) (hbc : b ≤ c) :
    c * ((n - r).choose 2) + b * (n - r) + c * n * (n + r)
      = (b * n + c * (n.choose 2) + c * n * n)
        + (c * (r.choose 2) + (c - b) * r) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbc
  have hnsub : r + a - r = a := Nat.add_sub_cancel_left r a
  have hcb : b + d - b = d := Nat.add_sub_cancel_left b d
  have h1 : (r + a).choose 2 = r.choose 2 + r * a + a.choose 2 :=
    rrChoose_add_mul r a
  have e1 : (b + d) * (r + a) * (r + a + r)
      = (b + d) * (r + a) * (r + a) + (b + d) * (r * r + a * r) := by
    ring
  have hr : r * r = 2 * (r.choose 2) + r :=
    (rrTwo_choose_add_self r).symm
  rw [hnsub, hcb, h1, e1, hr]
  ring

/-- Sum of `range` equals triangular number. -/
private theorem rrSum_range_id_eq_choose (n : ℕ) :
    ∑ i ∈ Finset.range n, i = n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, rrChoose_add n]

/-- `(-X^b)^j` splits into sign and `X`-power. -/
private theorem rrNegXpow (b j : ℕ) :
    (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ j
      = (-1 : PowerSeries ℚ) ^ j * (PowerSeries.X : PowerSeries ℚ) ^ (b * j) := by
  rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]

/-- Sign identity for the reflected index: `(-1)^(n-s) = (-1)^n * (-1)^s`. -/
private theorem rrNegOnePow_sub (s n : ℕ) (hs : s ≤ n) :
    (-1 : PowerSeries ℚ) ^ (n - s)
      = (-1 : PowerSeries ℚ) ^ n * (-1 : PowerSeries ℚ) ^ s := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hs
  have hsub : s + a - s = a := Nat.add_sub_cancel_left s a
  have hsq : (-1 : PowerSeries ℚ) ^ s * (-1 : PowerSeries ℚ) ^ s = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨s, rfl⟩
  have key : (-1 : PowerSeries ℚ) ^ s * (-1 : PowerSeries ℚ) ^ a
        * (-1 : PowerSeries ℚ) ^ s
      = (-1 : PowerSeries ℚ) ^ a := by
    have hrr : (-1 : PowerSeries ℚ) ^ s * (-1 : PowerSeries ℚ) ^ a
          * (-1 : PowerSeries ℚ) ^ s
        = (-1 : PowerSeries ℚ) ^ a
          * ((-1 : PowerSeries ℚ) ^ s * (-1 : PowerSeries ℚ) ^ s) := by
      ring
    rw [hrr, hsq, mul_one]
  rw [hsub, pow_add]
  exact key.symm

/-- Center term of the folded Rothe sum. -/
private theorem rrFold_center (b d n : ℕ) :
    (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n.choose 2)
      * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) n
      * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ n
      * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (2 * n - n)
    = ((-1 : PowerSeries ℚ) ^ n
        * (PowerSeries.X : PowerSeries ℚ)
          ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n))
      * (rrEps (b + d) b 0
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + 0)) := by
  have h2n : 2 * n - n = n := by omega
  have hQ : (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n.choose 2)
      = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (n.choose 2)) := by
    rw [← pow_mul]
  have hy : ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ n
      = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * n) := by
    rw [← pow_mul]
  have heps0 : rrEps (b + d) b 0 = 1 := by simp [rrEps]
  have hfac : (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n.choose 2)
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) n
        * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ n
        * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (2 * n - n)
      = (-1 : PowerSeries ℚ) ^ n
        * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (n.choose 2))
          * (PowerSeries.X : PowerSeries ℚ) ^ (b * n)
          * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * n))
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) n := by
    rw [h2n, rrNegXpow b n, hQ, hy]
    ring
  have hexp : (b + d) * (n.choose 2) + b * n + (b + d) * n * n
      = b * n + (b + d) * (n.choose 2) + (b + d) * n * n := by ring
  have hX : (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (n.choose 2))
        * (PowerSeries.X : PowerSeries ℚ) ^ (b * n)
        * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * n)
      = (PowerSeries.X : PowerSeries ℚ)
        ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n) := by
    rw [← pow_add, ← pow_add, hexp]
  rw [hfac, heps0, hX]
  ring_nf

/-- Off-center pair of the folded Rothe sum. -/
private theorem rrFold_pair (b d n s : ℕ) (hc : 1 ≤ b + d) (hs1 : s ≠ 0)
    (hs2 : s ≤ n) :
    ((PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ ((n + s).choose 2)
      * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + s)
      * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ (n + s)
      * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (2 * n - (n + s)))
    + ((PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ ((n - s).choose 2)
      * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n - s)
      * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ (n - s)
      * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (2 * n - (n - s)))
    = ((-1 : PowerSeries ℚ) ^ n
        * (PowerSeries.X : PowerSeries ℚ)
          ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n))
      * (rrEps (b + d) b s
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + s)) := by
  have hQ0 : PowerSeries.constantCoeff (PowerSeries.X ^ (b + d) : PowerSeries ℚ)
      = 0 :=
    rrXpow_constCoeff _ hc
  have h2p : 2 * n - (n + s) = n - s := by omega
  have h2m : 2 * n - (n - s) = n + s := by omega
  rw [h2p, h2m]
  have hsym : gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n - s)
      = gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + s) := by
    have h1 := rrQBinom_symm _ hQ0 (2 * n) (n - s) (by omega : n - s ≤ 2 * n)
    have h2 : 2 * n - (n - s) = n + s := by omega
    rw [h2] at h1
    exact h1
  have hQp : (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ ((n + s).choose 2)
      = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * ((n + s).choose 2)) := by
    rw [← pow_mul]
  have hyp : ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (n - s)
      = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * (n - s)) := by
    rw [← pow_mul]
  have hexpp := rrExp_plus (b + d) b n s hs2
  have hfac1 : (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ ((n + s).choose 2)
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + s)
        * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ (n + s)
        * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (n - s)
      = ((-1 : PowerSeries ℚ) ^ n * (-1 : PowerSeries ℚ) ^ s)
        * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * ((n + s).choose 2))
          * (PowerSeries.X : PowerSeries ℚ) ^ (b * (n + s))
          * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * (n - s)))
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + s) := by
    rw [rrNegXpow b (n + s), pow_add ((-1 : PowerSeries ℚ)) n s, hQp, hyp]
    ring
  have hQm : (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ ((n - s).choose 2)
      = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * ((n - s).choose 2)) := by
    rw [← pow_mul]
  have hym : ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (n + s)
      = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * (n + s)) := by
    rw [← pow_mul]
  have hexpm := rrExp_minus (b + d) b n s hs2 (Nat.le_add_right b d)
  rw [Nat.add_sub_cancel_left] at hexpm
  have hfac2 : (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ ((n - s).choose 2)
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n - s)
        * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ (n - s)
        * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (n + s)
      = ((-1 : PowerSeries ℚ) ^ n * (-1 : PowerSeries ℚ) ^ s)
        * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * ((n - s).choose 2))
          * (PowerSeries.X : PowerSeries ℚ) ^ (b * (n - s))
          * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * (n + s)))
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + s) := by
    rw [hsym, rrNegXpow b (n - s), rrNegOnePow_sub s n hs2, hQm, hym]
    ring
  have hXp : (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * ((n + s).choose 2))
        * (PowerSeries.X : PowerSeries ℚ) ^ (b * (n + s))
        * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * (n - s))
      = ((PowerSeries.X : PowerSeries ℚ)
          ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n))
        * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (s.choose 2) + b * s) := by
    rw [← pow_add, ← pow_add, hexpp, pow_add]
  have hXm : (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * ((n - s).choose 2))
        * (PowerSeries.X : PowerSeries ℚ) ^ (b * (n - s))
        * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * (n + s))
      = ((PowerSeries.X : PowerSeries ℚ)
          ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n))
        * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (s.choose 2) + d * s) := by
    rw [← pow_add, ← pow_add, hexpm, pow_add]
  have heps : rrEps (b + d) b s
      = (-1 : PowerSeries ℚ) ^ s
        * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (s.choose 2) + b * s)
          + (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (s.choose 2) + d * s)) := by
    simp only [rrEps, hs1, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [hfac1, hfac2, heps, hXp, hXm]
  ring

/-- The Rothe sum folds around `n`, giving the `ε`-sum. -/
private theorem rrFold_sum_eq (b d n : ℕ) (hc : 1 ≤ b + d) :
    (∑ j ∈ Finset.range (2 * n + 1),
      (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (j.choose 2)
        * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) j
        * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ j
        * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (2 * n - j))
    = ((-1 : PowerSeries ℚ) ^ n
        * (PowerSeries.X : PowerSeries ℚ)
          ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n))
      * ∑ r ∈ Finset.range (n + 1),
        rrEps (b + d) b r
          * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + r) := by
  have hstep1 : (∑ j ∈ Finset.range (2 * n + 1),
        (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (j.choose 2)
          * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) j
          * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ j
          * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (2 * n - j))
      = ((PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n.choose 2)
          * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) n
          * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ n
          * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (2 * n - n))
        + ∑ r ∈ Finset.range n,
          (((PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ ((n + (r + 1)).choose 2)
            * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n)
              (n + (r + 1))
            * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ (n + (r + 1))
            * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n))
              ^ (2 * n - (n + (r + 1))))
          + ((PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ ((n - (r + 1)).choose 2)
            * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n)
              (n - (r + 1))
            * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ (n - (r + 1))
            * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n))
              ^ (2 * n - (n - (r + 1))))) :=
    rrSum_fold _ _ n
  have hstep2 : ((-1 : PowerSeries ℚ) ^ n
        * (PowerSeries.X : PowerSeries ℚ)
          ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n))
        * ∑ r ∈ Finset.range (n + 1),
          rrEps (b + d) b r
            * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + r)
      = ((-1 : PowerSeries ℚ) ^ n
          * (PowerSeries.X : PowerSeries ℚ)
            ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n))
        * (rrEps (b + d) b 0
          * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + 0))
        + ∑ r ∈ Finset.range n,
          (((-1 : PowerSeries ℚ) ^ n
            * (PowerSeries.X : PowerSeries ℚ)
              ^ (b * n + (b + d) * (n.choose 2) + (b + d) * n * n))
            * (rrEps (b + d) b (r + 1)
              * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n)
                (n + (r + 1)))) := by
    rw [Finset.mul_sum, Finset.sum_range_succ']
    exact add_comm _ _
  rw [hstep1, hstep2]
  congr 1
  · exact rrFold_center b d n
  · apply Finset.sum_congr rfl
    intro r hr
    have hrle : r + 1 ≤ n := by
      have hlt : r < n := Finset.mem_range.mp hr
      omega
    exact rrFold_pair b d n (r + 1) hc (by omega) hrle

/-- Folded finite Jacobi triple product. -/
private theorem rrSum_eps_mul_qBinom_eq_prod (c b n : ℕ) (hc : 1 ≤ c)
    (hbc : b ≤ c) :
    ∑ r ∈ Finset.range (n + 1),
        rrEps c b r * gaussBinom (PowerSeries.X ^ c : PowerSeries ℚ) (2 * n) (n + r)
      = ∏ i ∈ Finset.range n,
        ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (b + c * i))
          * (1 - (PowerSeries.X : PowerSeries ℚ) ^ ((c - b) + c * i))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbc
  have hsub : b + d - b = d := Nat.add_sub_cancel_left b d
  rw [hsub]
  have hQ0 : PowerSeries.constantCoeff (PowerSeries.X ^ (b + d) : PowerSeries ℚ)
      = 0 := rrXpow_constCoeff _ (by omega)
  set E : ℕ := b * n + (b + d) * (n.choose 2) + (b + d) * n * n with hEdef
  set C0 : PowerSeries ℚ :=
    (-1 : PowerSeries ℚ) ^ n * (PowerSeries.X : PowerSeries ℚ) ^ E with hCdef
  have hRothe := rrRothe (PowerSeries.X ^ (b + d) : PowerSeries ℚ)
    (-(PowerSeries.X : PowerSeries ℚ) ^ b)
    ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) (2 * n)
  have hProd : (∏ i ∈ Finset.range (2 * n),
        ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
          + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
            * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ i))
      = C0 * ∏ i ∈ Finset.range n,
        ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i))
          * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (d + (b + d) * i))) := by
    have h2n : 2 * n = n + n := two_mul n
    have hSplit : (∏ i ∈ Finset.range (2 * n),
          ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
            + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
              * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ i))
        = (∏ i ∈ Finset.range n,
            ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
              + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
                * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ i))
          * ∏ i ∈ Finset.range n,
            ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
              + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
                * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n + i)) := by
      rw [h2n, Finset.prod_range_add]
    have hRefl : (∏ i ∈ Finset.range n,
          ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
            + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
              * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ i))
        = ∏ i ∈ Finset.range n,
          ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
            + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
              * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n - 1 - i)) := by
      rw [← Finset.prod_range_reflect]
    have hFact1 : ∀ i ∈ Finset.range n,
        ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
          + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
            * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n - 1 - i))
        = (-(PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * (n - 1 - i)))
          * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (d + (b + d) * i)) := by
      intro i hi
      have hilt : i < n := Finset.mem_range.mp hi
      have hle : i + 1 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hsub : i + 1 + k - 1 - i = k := by omega
      rw [hsub]
      have hQ : (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ k
          = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * k) := by
        rw [← pow_mul]
      rw [hQ]
      have hXbQ : (-(PowerSeries.X : PowerSeries ℚ) ^ b)
            * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * k)
          = (-(PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * k)) := by
        have h1 : (PowerSeries.X : PowerSeries ℚ) ^ b
              * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * k)
            = (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * k) := by
          rw [← pow_add]
        rw [neg_mul, h1]
      rw [hXbQ]
      have hexp : (b + d) * (i + 1 + k)
          = (b + (b + d) * k) + (d + (b + d) * i) := by
        ring
      have hXcn : (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (i + 1 + k))
          = (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * k)
            * (PowerSeries.X : PowerSeries ℚ) ^ (d + (b + d) * i) := by
        rw [hexp, pow_add]
      rw [hXcn]
      ring
    have hFact2 : ∀ i ∈ Finset.range n,
        ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
          + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
            * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n + i))
        = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
          * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i)) := by
      intro i _
      have hQ : (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n + i)
          = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (n + i)) := by
        rw [← pow_mul]
      rw [hQ]
      have hXbQ : (-(PowerSeries.X : PowerSeries ℚ) ^ b)
            * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (n + i))
          = -((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
            * (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i)) := by
        have h1 : (PowerSeries.X : PowerSeries ℚ) ^ b
              * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (n + i))
            = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
              * (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i) := by
          have e1 : b + (b + d) * (n + i)
              = (b + d) * n + (b + (b + d) * i) := by ring
          calc (PowerSeries.X : PowerSeries ℚ) ^ b
                  * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * (n + i))
              = (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * (n + i)) := by
                rw [← pow_add]
            _ = (PowerSeries.X : PowerSeries ℚ)
                  ^ ((b + d) * n + (b + (b + d) * i)) := by rw [e1]
            _ = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
                * (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i) := by
                rw [pow_add]
        rw [neg_mul, h1]
      rw [hXbQ]
      ring
    have hFirst : (∏ i ∈ Finset.range n,
          ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
            + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
              * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n - 1 - i)))
        = (∏ i ∈ Finset.range n,
            (-(PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * (n - 1 - i))))
          * ∏ i ∈ Finset.range n,
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ (d + (b + d) * i)) := by
      rw [Finset.prod_congr rfl hFact1, Finset.prod_mul_distrib]
    have hSecond : (∏ i ∈ Finset.range n,
          ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
            + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
              * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (n + i)))
        = (∏ _i ∈ Finset.range n,
            (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n))
          * ∏ i ∈ Finset.range n,
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i)) := by
      rw [Finset.prod_congr rfl hFact2, Finset.prod_mul_distrib]
    have hNeg : ∀ i ∈ Finset.range n,
        (-(PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * (n - 1 - i)))
        = (-1 : PowerSeries ℚ)
          * (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * (n - 1 - i)) := by
      intro i _
      rw [neg_eq_neg_one_mul]
    have hNegProd : (∏ i ∈ Finset.range n,
          (-(PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * (n - 1 - i))))
        = (-1 : PowerSeries ℚ) ^ n
          * (PowerSeries.X : PowerSeries ℚ)
            ^ (∑ i ∈ Finset.range n, (b + (b + d) * (n - 1 - i))) := by
      rw [Finset.prod_congr rfl hNeg, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_range, Finset.prod_pow_eq_pow_sum]
    have hConstProd : (∏ _i ∈ Finset.range n,
          (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n))
        = (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * n) := by
      rw [Finset.prod_const, Finset.card_range, ← pow_mul]
    have hExpSum : (∑ i ∈ Finset.range n, (b + (b + d) * (n - 1 - i)))
        + (b + d) * n * n = E := by
      rw [hEdef]
      have hsum1 : (∑ i ∈ Finset.range n, (b + (b + d) * (n - 1 - i)))
          = b * n + (b + d) * (n.choose 2) := by
        have h1 : (∑ i ∈ Finset.range n, (b + (b + d) * (n - 1 - i)))
            = (∑ i ∈ Finset.range n, b)
              + (b + d) * ∑ i ∈ Finset.range n, (n - 1 - i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
        have h2 : (∑ i ∈ Finset.range n, b) = b * n := by
          rw [Finset.sum_const, Finset.card_range]
          ring
        have h3 : (∑ i ∈ Finset.range n, (n - 1 - i)) = n.choose 2 := by
          have hR : (∑ i ∈ Finset.range n, (n - 1 - i))
              = ∑ i ∈ Finset.range n, i := by
            have := Finset.sum_range_reflect (fun j => j) n
            simpa using this
          rw [hR, rrSum_range_id_eq_choose]
        rw [h1, h2, h3]
      omega
    have hCombine : (∏ i ∈ Finset.range (2 * n),
          ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)
            + (-(PowerSeries.X : PowerSeries ℚ) ^ b)
              * (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ i))
        = ((-1 : PowerSeries ℚ) ^ n
            * (PowerSeries.X : PowerSeries ℚ)
              ^ (∑ i ∈ Finset.range n, (b + (b + d) * (n - 1 - i)))
            * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * n))
          * ((∏ i ∈ Finset.range n,
              (1 - (PowerSeries.X : PowerSeries ℚ) ^ (d + (b + d) * i)))
            * ∏ i ∈ Finset.range n,
              (1 - (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i))) := by
      rw [hSplit, hRefl, hFirst, hSecond, hNegProd, hConstProd]
      ring
    have hPow : (PowerSeries.X : PowerSeries ℚ)
          ^ (∑ i ∈ Finset.range n, (b + (b + d) * (n - 1 - i)))
          * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * n)
        = (PowerSeries.X : PowerSeries ℚ) ^ E := by
      rw [← pow_add, hExpSum]
    have hRHS : (∏ i ∈ Finset.range n,
          (1 - (PowerSeries.X : PowerSeries ℚ) ^ (d + (b + d) * i)))
          * ∏ i ∈ Finset.range n,
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i))
        = ∏ i ∈ Finset.range n,
          ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i))
            * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (d + (b + d) * i))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    have hC0Eq : (-1 : PowerSeries ℚ) ^ n
          * (PowerSeries.X : PowerSeries ℚ)
            ^ (∑ i ∈ Finset.range n, (b + (b + d) * (n - 1 - i)))
          * (PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n * n) = C0 := by
      rw [hCdef, mul_assoc, ← pow_add, hExpSum]
    rw [hCombine, hC0Eq, hRHS]
  have hSum : (∑ j ∈ Finset.range (2 * n + 1),
        (PowerSeries.X ^ (b + d) : PowerSeries ℚ) ^ (j.choose 2)
          * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) j
          * (-(PowerSeries.X : PowerSeries ℚ) ^ b) ^ j
          * ((PowerSeries.X : PowerSeries ℚ) ^ ((b + d) * n)) ^ (2 * n - j))
      = C0 * ∑ r ∈ Finset.range (n + 1),
        rrEps (b + d) b r
          * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + r) := by
    rw [hCdef, hEdef]
    exact rrFold_sum_eq b d n hc
  have hCne : C0 ≠ 0 := by
    simp only [hCdef]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact neg_ne_zero.mpr one_ne_zero
    · apply pow_ne_zero
      exact PowerSeries.X_ne_zero
  have hEq : C0 * ∏ i ∈ Finset.range n,
        ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (b + (b + d) * i))
          * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (d + (b + d) * i)))
      = C0 * ∑ r ∈ Finset.range (n + 1),
        rrEps (b + d) b r
          * gaussBinom (PowerSeries.X ^ (b + d) : PowerSeries ℚ) (2 * n) (n + r) := by
    rw [← hProd, ← hSum]
    exact hRothe
  have hCancel := mul_left_cancel₀ hCne hEq
  exact hCancel.symm

/-! ## unit Bailey pair -/

/-- Unit Bailey pair relative to `a = 1`. -/
private theorem rrUnit_bailey_pair (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1), rrU r * rrIp (n - r) * rrIp (n + r)
      = (if n = 0 then 1 else 0) := by
  by_cases hn : n = 0
  · subst hn
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    have hu0 : rrU 0 = 1 := by simp [rrU, rrEps]
    have hip0 : rrIp 0 = 1 := by
      simp only [rrIp, rrP, qPochFin]
      rw [Finset.prod_range_zero]
      simp
    simp only [Nat.sub_zero, Nat.add_zero]
    rw [hu0, hip0]
    simp
  · simp only [hn, ↓reduceIte]
    have hJTP := rrSum_eps_mul_qBinom_eq_prod 1 0 n (by omega) (by omega)
    simp only [rrU] at hJTP ⊢
    have hQ1 : (PowerSeries.X ^ 1 : PowerSeries ℚ) = PowerSeries.X := pow_one _
    rw [hQ1] at hJTP
    have hprod0 : (∏ i ∈ Finset.range n,
        ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (0 + 1 * i))
          * (1 - (PowerSeries.X : PowerSeries ℚ) ^ ((1 - 0) + 1 * i)))) = 0 := by
      have hmem : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
      apply Finset.prod_eq_zero hmem
      have h0 : (0 : ℕ) + 1 * 0 = 0 := by omega
      rw [h0, pow_zero, sub_self, zero_mul]
    rw [hprod0] at hJTP
    have hLHS0 : (∑ r ∈ Finset.range (n + 1),
        rrEps 1 0 r
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (2 * n) (n + r)) = 0 :=
      hJTP
    have hfactor : (∑ r ∈ Finset.range (n + 1),
          rrEps 1 0 r
            * gaussBinom (PowerSeries.X : PowerSeries ℚ) (2 * n) (n + r))
        = rrP (2 * n) * (∑ r ∈ Finset.range (n + 1),
          rrEps 1 0 r * rrIp (n - r) * rrIp (n + r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hrle : r ≤ n := by
        have hlt : r < n + 1 := Finset.mem_range.mp hr
        omega
      have hle : n + r ≤ 2 * n := by omega
      have hMk : 2 * n - (n + r) = n - r := by omega
      have hQ := rrQBinom_eq_rrQPoch_mul_inv (PowerSeries.X : PowerSeries ℚ)
        PowerSeries.constantCoeff_X (2 * n) (n + r) hle
      simp only [rrP, rrIp] at hQ ⊢
      rw [hMk] at hQ
      rw [hQ]
      ring
    rw [hfactor] at hLHS0
    have hPne : rrP (2 * n) ≠ 0 := by
      simp only [rrP]
      exact rrQPoch_ne_zero _ PowerSeries.constantCoeff_X _
    exact (mul_eq_zero.mp hLHS0).resolve_left hPne

/-! ## finite Rogers–Ramanujan identity -/

/-- Auxiliary: `X^(2r²)·u(r) = θ(r)`. -/
private theorem rrTheta_of_unit (r : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2) * rrU r = rrTheta r := by
  simp only [rrU, rrTheta, rrEps]
  by_cases hr0 : r = 0
  · subst hr0
    simp
  · simp only [hr0, ↓reduceIte]
    have hr2 : r * r = 2 * (r.choose 2) + r :=
      (rrTwo_choose_add_self r).symm
    have hr2pow : r ^ 2 = r * r := by rw [pow_two]
    have e1 : 2 * r ^ 2 + (1 * (r.choose 2) + 0 * r)
        = 5 * (r.choose 2) + 2 * r := by
      rw [hr2pow, hr2]
      ring
    have e2 : 2 * r ^ 2 + (1 * (r.choose 2) + (1 - 0) * r)
        = 5 * (r.choose 2) + (5 - 2) * r := by
      rw [hr2pow, hr2]
      ring
    have hX1 : (PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2)
          * ((PowerSeries.X : PowerSeries ℚ) ^ (1 * (r.choose 2) + 0 * r))
        = (PowerSeries.X : PowerSeries ℚ) ^ (5 * (r.choose 2) + 2 * r) := by
      rw [← pow_add, e1]
    have hX2 : (PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2)
          * ((PowerSeries.X : PowerSeries ℚ) ^ (1 * (r.choose 2) + (1 - 0) * r))
        = (PowerSeries.X : PowerSeries ℚ) ^ (5 * (r.choose 2) + (5 - 2) * r) := by
      rw [← pow_add, e2]
    calc (PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2)
            * ((-1 : PowerSeries ℚ) ^ r
              * ((PowerSeries.X : PowerSeries ℚ) ^ (1 * (r.choose 2) + 0 * r)
                + (PowerSeries.X : PowerSeries ℚ)
                  ^ (1 * (r.choose 2) + (1 - 0) * r)))
        = (-1 : PowerSeries ℚ) ^ r
            * (((PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2)
              * (PowerSeries.X : PowerSeries ℚ) ^ (1 * (r.choose 2) + 0 * r))
              + ((PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2)
              * (PowerSeries.X : PowerSeries ℚ)
                ^ (1 * (r.choose 2) + (1 - 0) * r))) := by
          ring
      _ = (-1 : PowerSeries ℚ) ^ r
            * ((PowerSeries.X : PowerSeries ℚ) ^ (5 * (r.choose 2) + 2 * r)
              + (PowerSeries.X : PowerSeries ℚ)
                ^ (5 * (r.choose 2) + (5 - 2) * r)) := by
          rw [hX1, hX2]

/-- Finite Rogers–Ramanujan polynomial identity. -/
private theorem rrFinite_identity (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp (n - j) * rrIp j
      = ∑ r ∈ Finset.range (n + 1),
        rrTheta r * rrIp (n - r) * rrIp (n + r) := by
  have hU : ∀ m, (if m = 0 then (1 : PowerSeries ℚ) else 0)
      = ∑ r ∈ Finset.range (m + 1), rrU r * rrIp (m - r) * rrIp (m + r) :=
    fun m => (rrUnit_bailey_pair m).symm
  have hcollapse : ∀ m, (∑ j ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
          * (if j = 0 then (1 : PowerSeries ℚ) else 0) * rrIp (m - j))
      = rrIp m := by
    intro m
    have hterm : ∀ j ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
          * (if j = 0 then (1 : PowerSeries ℚ) else 0) * rrIp (m - j)
          = (if j = 0 then rrIp m else 0) := by
      intro j _
      by_cases hj : j = 0
      · subst hj
        simp
      · simp [hj]
    rw [Finset.sum_congr rfl hterm]
    simp
  have hIp : ∀ m, rrIp m
      = ∑ r ∈ Finset.range (m + 1),
        ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r)
          * rrIp (m - r) * rrIp (m + r) := by
    intro m
    have hstep := rrBailey_step rrU (fun k => if k = 0 then 1 else 0) hU m
    rw [hcollapse m] at hstep
    have hterm : ∀ r ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r * rrIp (m - r)
          * rrIp (m + r)
        = ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r)
          * rrIp (m - r) * rrIp (m + r) := by
      intro r _
      ring
    rw [Finset.sum_congr rfl hterm] at hstep
    exact hstep
  have hstep2 := rrBailey_step
    (fun r => (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r) rrIp hIp n
  have hLHScomm : (∑ j ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j * rrIp (n - j))
      = ∑ j ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp (n - j) * rrIp j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hRHS : (∑ r ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2)
          * ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r)
          * rrIp (n - r) * rrIp (n + r))
      = ∑ r ∈ Finset.range (n + 1),
        rrTheta r * rrIp (n - r) * rrIp (n + r) := by
    apply Finset.sum_congr rfl
    intro r _
    have hth := rrTheta_of_unit r
    have hpow : (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2)
          * ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r)
        = (PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2) * rrU r := by
      have hadd : r ^ 2 + r ^ 2 = 2 * r ^ 2 := by ring
      calc (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2)
              * ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r)
          = ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2)
              * (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2)) * rrU r := by
            ring
        _ = (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2 + r ^ 2) * rrU r := by
            rw [← pow_add]
        _ = (PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2) * rrU r := by
            rw [hadd]
    calc (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2)
            * ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r)
            * rrIp (n - r) * rrIp (n + r)
        = ((PowerSeries.X : PowerSeries ℚ) ^ (2 * r ^ 2) * rrU r)
          * rrIp (n - r) * rrIp (n + r) := by
          rw [hpow]
      _ = rrTheta r * rrIp (n - r) * rrIp (n + r) := by
          rw [hth]
  calc (∑ j ∈ Finset.range (n + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp (n - j) * rrIp j)
        = (∑ j ∈ Finset.range (n + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j * rrIp (n - j)) :=
          hLHScomm.symm
      _ = (∑ r ∈ Finset.range (n + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2)
            * ((PowerSeries.X : PowerSeries ℚ) ^ (r ^ 2) * rrU r)
            * rrIp (n - r) * rrIp (n + r)) := hstep2
      _ = ∑ r ∈ Finset.range (n + 1),
          rrTheta r * rrIp (n - r) * rrIp (n + r) := hRHS

/-! ## truncations from the finite identities -/

/-- `X^r` divides `θ(r)`. -/
private theorem rrXpow_dvd_theta (r : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ r ∣ rrTheta r := by
  simp only [rrTheta, rrEps]
  by_cases hr : r = 0
  · subst hr
    simp
  · simp only [hr, ↓reduceIte]
    have h1 : r ≤ 5 * (r.choose 2) + 2 * r := by
      have hC : 0 ≤ 5 * (r.choose 2) := Nat.zero_le _
      omega
    have h2 : r ≤ 5 * (r.choose 2) + (5 - 2) * r := by
      have hC : 0 ≤ 5 * (r.choose 2) := Nat.zero_le _
      omega
    have d1 : (PowerSeries.X : PowerSeries ℚ) ^ r
        ∣ (PowerSeries.X : PowerSeries ℚ) ^ (5 * (r.choose 2) + 2 * r) :=
      pow_dvd_pow _ h1
    have d2 : (PowerSeries.X : PowerSeries ℚ) ^ r
        ∣ (PowerSeries.X : PowerSeries ℚ) ^ (5 * (r.choose 2) + (5 - 2) * r) :=
      pow_dvd_pow _ h2
    have dsum : (PowerSeries.X : PowerSeries ℚ) ^ r
        ∣ (PowerSeries.X : PowerSeries ℚ) ^ (5 * (r.choose 2) + 2 * r)
          + (PowerSeries.X : PowerSeries ℚ) ^ (5 * (r.choose 2) + (5 - 2) * r) :=
      dvd_add d1 d2
    exact dvd_mul_of_dvd_right dsum _

/-- A `θ`-multiple of two near-one brackets is `θ` mod `X^(n+1)`. -/
private theorem rrDvd_theta_mul_sub (r n : ℕ) (hr : r ≤ n) (U V : PowerSeries ℚ)
    (hU : (PowerSeries.X : PowerSeries ℚ) ^ (n - r + 1) ∣ U - 1)
    (hV : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1) ∣ V - 1) :
    (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrTheta r * U * V - rrTheta r := by
  have hθ := rrXpow_dvd_theta r
  have hexp : r + (n - r + 1) = n + 1 := by omega
  have hUV : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrTheta r * (U - 1) := by
    have hmul := mul_dvd_mul hθ hU
    rw [← pow_add, hexp] at hmul
    exact hmul
  have t1 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrTheta r * (U - 1) * V :=
    dvd_mul_of_dvd_left hUV V
  have t2 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrTheta r * (V - 1) :=
    dvd_mul_of_dvd_right hV _
  have hdecomp : rrTheta r * U * V - rrTheta r
      = rrTheta r * (U - 1) * V + rrTheta r * (V - 1) := by ring
  rw [hdecomp]
  exact dvd_add t1 t2

/-- Truncation of the finite RR identity. -/
private theorem rrTrunc_RR (n : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrP n * (∑ k ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k) - rrT n := by
  have hFin := rrFinite_identity n
  simp only [rrT]
  have hPS : rrP n * (∑ k ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k)
      = ∑ j ∈ Finset.range (n + 1),
        rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j) := by
    rw [Finset.mul_sum]
  have hP2L : (rrP n * rrP n) * (∑ j ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp (n - j) * rrIp j)
      = ∑ j ∈ Finset.range (n + 1),
        (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
          * (rrP n * rrIp (n - j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hP2R : (rrP n * rrP n) * (∑ r ∈ Finset.range (n + 1),
        rrTheta r * rrIp (n - r) * rrIp (n + r))
      = ∑ r ∈ Finset.range (n + 1),
        rrTheta r * ((rrP n * rrIp (n - r)) * (rrP n * rrIp (n + r))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hP2eq : (∑ j ∈ Finset.range (n + 1),
        (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
          * (rrP n * rrIp (n - j)))
      = ∑ r ∈ Finset.range (n + 1),
        rrTheta r * ((rrP n * rrIp (n - r)) * (rrP n * rrIp (n + r))) := by
    have hMul : (rrP n * rrP n) * (∑ j ∈ Finset.range (n + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp (n - j) * rrIp j)
        = (rrP n * rrP n) * (∑ r ∈ Finset.range (n + 1),
          rrTheta r * rrIp (n - r) * rrIp (n + r)) := by
      rw [hFin]
    rw [hP2L, hP2R] at hMul
    exact hMul
  have hleft : ∀ j ∈ Finset.range (n + 1),
      (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
          - (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
            * (rrP n * rrIp (n - j)) := by
    intro j hj
    have hjle : j ≤ n := by
      have hlt : j < n + 1 := Finset.mem_range.mp hj
      omega
    have hmin : min n (n - j) = n - j := Nat.min_eq_right (Nat.sub_le n j)
    have hg : (PowerSeries.X : PowerSeries ℚ) ^ (n - j + 1)
        ∣ rrP n * rrIp (n - j) - 1 := by
      have h0 := rrXpow_dvd_qPoch_mul_inv_sub_one 1 n (n - j) (by omega)
      have hQ1 : (PowerSeries.X ^ 1 : PowerSeries ℚ) = PowerSeries.X :=
        pow_one _
      have hmin1 : 1 * (min n (n - j) + 1) = n - j + 1 := by
        rw [hmin, one_mul]
      rw [hmin1, hQ1] at h0
      simpa only [rrP, rrIp] using h0
    have hf : (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2)
        ∣ rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j) := by
      have hfac : rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j)
          = (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * (rrP n * rrIp j) := by
        ring
      rw [hfac]
      exact dvd_mul_right _ _
    have hj2 : j ≤ j ^ 2 := by
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp
      · calc j = j * 1 := (mul_one _).symm
          _ ≤ j * j := Nat.mul_le_mul (le_refl _) (by omega)
          _ = j ^ 2 := (pow_two _).symm
    have hle : n + 1 ≤ j ^ 2 + (n - j + 1) := by omega
    have hmain := rrDvd_mul_sub (j ^ 2) (n - j + 1)
      (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
      (rrP n * rrIp (n - j)) hf hg
    have hpow : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ (PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2 + (n - j + 1)) :=
      pow_dvd_pow _ hle
    have hneg : (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
          - (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
            * (rrP n * rrIp (n - j))
        = -((rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
            * (rrP n * rrIp (n - j))
          - (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))) := by
      ring
    rw [hneg]
    exact dvd_neg.mpr (dvd_trans hpow hmain)
  have hright : ∀ r ∈ Finset.range (n + 1),
      (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrTheta r * ((rrP n * rrIp (n - r)) * (rrP n * rrIp (n + r)))
          - rrTheta r := by
    intro r hr
    have hrle : r ≤ n := by
      have hlt : r < n + 1 := Finset.mem_range.mp hr
      omega
    have hminC : min n (n - r) = n - r := Nat.min_eq_right (Nat.sub_le n r)
    have hC : (PowerSeries.X : PowerSeries ℚ) ^ (n - r + 1)
        ∣ rrP n * rrIp (n - r) - 1 := by
      have h0 := rrXpow_dvd_qPoch_mul_inv_sub_one 1 n (n - r) (by omega)
      have hQ1 : (PowerSeries.X ^ 1 : PowerSeries ℚ) = PowerSeries.X :=
        pow_one _
      have hmin1 : 1 * (min n (n - r) + 1) = n - r + 1 := by
        rw [hminC, one_mul]
      rw [hmin1, hQ1] at h0
      simpa only [rrP, rrIp] using h0
    have hminD : min n (n + r) = n := Nat.min_eq_left (Nat.le_add_right n r)
    have hD : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrP n * rrIp (n + r) - 1 := by
      have h0 := rrXpow_dvd_qPoch_mul_inv_sub_one 1 n (n + r) (by omega)
      have hQ1 : (PowerSeries.X ^ 1 : PowerSeries ℚ) = PowerSeries.X :=
        pow_one _
      have hmin1 : 1 * (min n (n + r) + 1) = n + 1 := by
        rw [hminD, one_mul]
      rw [hmin1, hQ1] at h0
      simpa only [rrP, rrIp] using h0
    have hmain := rrDvd_theta_mul_sub r n hrle
      (rrP n * rrIp (n - r)) (rrP n * rrIp (n + r)) hC hD
    have hgoal : rrTheta r * ((rrP n * rrIp (n - r)) * (rrP n * rrIp (n + r)))
          - rrTheta r
        = rrTheta r * (rrP n * rrIp (n - r)) * (rrP n * rrIp (n + r))
          - rrTheta r := by ring
    rw [hgoal]
    exact hmain
  have hsum : (∑ j ∈ Finset.range (n + 1),
        rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
      - ∑ r ∈ Finset.range (n + 1), rrTheta r
      = (∑ j ∈ Finset.range (n + 1),
          ((rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
            - (rrP n * ((PowerSeries.X : PowerSeries ℚ) ^ (j ^ 2) * rrIp j))
              * (rrP n * rrIp (n - j))))
        + (∑ r ∈ Finset.range (n + 1),
          (rrTheta r * ((rrP n * rrIp (n - r)) * (rrP n * rrIp (n + r)))
            - rrTheta r)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linear_combination hP2eq
  rw [hPS, hsum]
  apply dvd_add
  · apply Finset.dvd_sum
    intro j hj
    exact hleft j hj
  · apply Finset.dvd_sum
    intro r hr
    exact hright r hr

/-- Truncation of the `q^5` Jacobi triple product. -/
private theorem rrTrunc_JTP (n : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ (n + 1) ∣ rrT n - rrPi5 n := by
  have hJTP := rrSum_eps_mul_qBinom_eq_prod 5 2 n (by omega) (by omega)
  have hQ5 : PowerSeries.constantCoeff (PowerSeries.X ^ 5 : PowerSeries ℚ)
      = 0 :=
    rrXpow_constCoeff 5 (by omega)
  have hP5 : rrP5 n = ∏ i ∈ Finset.range n,
      (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * i + 5)) := by
    simp only [rrP5, qPochFin]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    rw [← pow_mul]
    congr 1
  have hRHS : rrP5 n * (∏ i ∈ Finset.range n,
        ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 + 5 * i))
          * (1 - (PowerSeries.X : PowerSeries ℚ) ^ ((5 - 2) + 5 * i))))
      = rrPi5 n := by
    rw [hP5, ← Finset.prod_mul_distrib]
    simp only [rrPi5]
    apply Finset.prod_congr rfl
    intro i _
    have e1 : 2 + 5 * i = 5 * i + 2 := by omega
    have e2 : (5 - 2) + 5 * i = 5 * i + 3 := by omega
    rw [e1, e2]
    ring
  have hPE : rrP5 n * (∑ r ∈ Finset.range (n + 1),
        rrEps 5 2 r
          * gaussBinom (PowerSeries.X ^ 5 : PowerSeries ℚ) (2 * n) (n + r))
      = rrPi5 n := by
    have hJJ := congrArg (rrP5 n * ·) hJTP
    rwa [hRHS] at hJJ
  have hterm : ∀ r ∈ Finset.range (n + 1),
      rrP5 n * (rrTheta r
        * gaussBinom (PowerSeries.X ^ 5 : PowerSeries ℚ) (2 * n) (n + r))
      = rrTheta r
        * ((rrP5 (2 * n) * rrIp5 (n + r)) * (rrP5 n * rrIp5 (n - r))) := by
    intro r hr
    have hrle : r ≤ n := by
      have hlt : r < n + 1 := Finset.mem_range.mp hr
      omega
    have hle : n + r ≤ 2 * n := by omega
    have hMk : 2 * n - (n + r) = n - r := by omega
    have hQ := rrQBinom_eq_rrQPoch_mul_inv _ hQ5 (2 * n) (n + r) hle
    rw [hMk] at hQ
    simp only [rrP5, rrIp5, rrTheta] at hQ ⊢
    rw [hQ]
    ring
  have hdiv : ∀ r ∈ Finset.range (n + 1),
      (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrTheta r
            * ((rrP5 (2 * n) * rrIp5 (n + r)) * (rrP5 n * rrIp5 (n - r)))
          - rrTheta r := by
    intro r hr
    have hrle : r ≤ n := by
      have hlt : r < n + 1 := Finset.mem_range.mp hr
      omega
    have hminU : min n (n - r) = n - r := Nat.min_eq_right (Nat.sub_le n r)
    have hU0 := rrXpow_dvd_qPoch_mul_inv_sub_one 5 n (n - r) (by omega)
    have hminU1 : 5 * (min n (n - r) + 1) = 5 * (n - r + 1) := by rw [hminU]
    rw [hminU1] at hU0
    have hUle : n - r + 1 ≤ 5 * (n - r + 1) := by omega
    have hU : (PowerSeries.X : PowerSeries ℚ) ^ (n - r + 1)
        ∣ rrP5 n * rrIp5 (n - r) - 1 := by
      have hpow : (PowerSeries.X : PowerSeries ℚ) ^ (n - r + 1)
          ∣ (PowerSeries.X : PowerSeries ℚ) ^ (5 * (n - r + 1)) :=
        pow_dvd_pow _ hUle
      have hU0' : (PowerSeries.X : PowerSeries ℚ) ^ (5 * (n - r + 1))
          ∣ rrP5 n * rrIp5 (n - r) - 1 := by
        simpa only [rrP5, rrIp5] using hU0
      exact dvd_trans hpow hU0'
    have hminV : min (2 * n) (n + r) = n + r := by omega
    have hV0 := rrXpow_dvd_qPoch_mul_inv_sub_one 5 (2 * n) (n + r) (by omega)
    have hminV1 : 5 * (min (2 * n) (n + r) + 1) = 5 * (n + r + 1) := by
      rw [hminV]
    rw [hminV1] at hV0
    have hVle : n + 1 ≤ 5 * (n + r + 1) := by omega
    have hV : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrP5 (2 * n) * rrIp5 (n + r) - 1 := by
      have hpow : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
          ∣ (PowerSeries.X : PowerSeries ℚ) ^ (5 * (n + r + 1)) :=
        pow_dvd_pow _ hVle
      have hV0' : (PowerSeries.X : PowerSeries ℚ) ^ (5 * (n + r + 1))
          ∣ rrP5 (2 * n) * rrIp5 (n + r) - 1 := by
        simpa only [rrP5, rrIp5] using hV0
      exact dvd_trans hpow hV0'
    have hmain := rrDvd_theta_mul_sub r n hrle
      (rrP5 n * rrIp5 (n - r)) (rrP5 (2 * n) * rrIp5 (n + r)) hU hV
    have hgoal : rrTheta r
          * ((rrP5 (2 * n) * rrIp5 (n + r)) * (rrP5 n * rrIp5 (n - r)))
          - rrTheta r
        = rrTheta r * (rrP5 n * rrIp5 (n - r))
            * (rrP5 (2 * n) * rrIp5 (n + r))
          - rrTheta r := by ring
    rw [hgoal]
    exact hmain
  have hsumUV : (∑ r ∈ Finset.range (n + 1),
        rrTheta r
          * ((rrP5 (2 * n) * rrIp5 (n + r)) * (rrP5 n * rrIp5 (n - r))))
      = rrPi5 n := by
    have hPEθ : rrP5 n * (∑ r ∈ Finset.range (n + 1),
          rrTheta r
            * gaussBinom (PowerSeries.X ^ 5 : PowerSeries ℚ) (2 * n) (n + r))
        = rrPi5 n := by
      simpa only [rrTheta] using hPE
    rw [← hPEθ, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r hr => (hterm r hr).symm)
  have hdecomp : (∑ r ∈ Finset.range (n + 1), rrTheta r) - rrPi5 n
      = -∑ r ∈ Finset.range (n + 1),
        (rrTheta r
          * ((rrP5 (2 * n) * rrIp5 (n + r)) * (rrP5 n * rrIp5 (n - r)))
          - rrTheta r) := by
    rw [Finset.sum_sub_distrib, hsumUV]
    ring
  simp only [rrT]
  rw [hdecomp]
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro r hr
  exact hdiv r hr

/-! ## gap-2 subsets -/

/-- Inserting `m + 2` does not change the gap-2 inventory over `Icc 1 m`. -/
private theorem rrGap2_insert_filter (m : ℕ) :
    (Finset.Icc 1 (m + 1)).powerset.filter (fun t => rrGap2 (insert (m + 2) t))
      = (Finset.Icc 1 m).powerset.filter rrGap2 := by
  apply Finset.ext
  intro t
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hgap⟩
    have hno : m + 1 ∉ t := by
      intro hmem
      have h1 : m + 1 ∈ insert (m + 2) t := Finset.mem_insert_of_mem hmem
      have h2 : m + 2 ∈ insert (m + 2) t := Finset.mem_insert_self _ _
      have h3 := hgap _ h1 _ h2 (by omega : m + 1 < m + 2)
      omega
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxIcc := Finset.mem_Icc.mp (hsub hx)
      have hne : x ≠ m + 1 := by
        intro he
        apply hno
        rw [← he]
        exact hx
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb hab
      exact hgap a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
        hab
  · rintro ⟨hsub, hgap⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxIcc := Finset.mem_Icc.mp (hsub hx)
      exact Finset.mem_Icc.mpr ⟨hxIcc.1, by omega⟩
    · intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · omega
        · have hbIcc := Finset.mem_Icc.mp (hsub hb)
          omega
      · rcases hb with rfl | hb
        · have haIcc := Finset.mem_Icc.mp (hsub ha)
          omega
        · exact hgap a ha b hb hab

/-- Left-side recurrence: `L(m+2) = L(m+1) + X^(m+2) * L(m)`. -/
private theorem rrGap2_stepL (m : ℕ) :
    (∑ S ∈ (Finset.Icc 1 (m + 2)).powerset.filter rrGap2,
      (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
    = (∑ S ∈ (Finset.Icc 1 (m + 1)).powerset.filter rrGap2,
      (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
      + (PowerSeries.X : PowerSeries ℚ) ^ (m + 2)
        * (∑ S ∈ (Finset.Icc 1 m).powerset.filter rrGap2,
          (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id)) := by
  have eIcc : Finset.Icc 1 (m + 2)
      = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
    have e : m + 2 = (m + 1) + 1 := by omega
    rw [e]
    exact (Finset.insert_Icc_right_eq_Icc_add_one (a := 1) (b := m + 1)
      (by omega)).symm
  have ha : m + 2 ∉ Finset.Icc 1 (m + 1) := by
    intro h
    have hI := Finset.mem_Icc.mp h
    omega
  have hsplit : (∑ S ∈ (insert (m + 2) (Finset.Icc 1 (m + 1))).powerset,
        if rrGap2 S then (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id) else 0)
      = (∑ t ∈ (Finset.Icc 1 (m + 1)).powerset,
        if rrGap2 t then (PowerSeries.X : PowerSeries ℚ) ^ (t.sum id) else 0)
        + (∑ t ∈ (Finset.Icc 1 (m + 1)).powerset,
        if rrGap2 (insert (m + 2) t)
          then (PowerSeries.X : PowerSeries ℚ) ^ ((insert (m + 2) t).sum id)
          else 0) :=
    Finset.sum_powerset_insert ha _
  have hsecond : (∑ t ∈ (Finset.Icc 1 (m + 1)).powerset,
        if rrGap2 (insert (m + 2) t)
          then (PowerSeries.X : PowerSeries ℚ) ^ ((insert (m + 2) t).sum id)
          else 0)
      = (PowerSeries.X : PowerSeries ℚ) ^ (m + 2)
        * (∑ S ∈ (Finset.Icc 1 m).powerset.filter rrGap2,
          (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id)) := by
    rw [← Finset.sum_filter, rrGap2_insert_filter m, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hst : (insert (m + 2) t).sum id = (m + 2) + t.sum id := by
      have hmem : t ⊆ Finset.Icc 1 m :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
      have hnot : m + 2 ∉ t := by
        intro hcon
        have hI := Finset.mem_Icc.mp (hmem hcon)
        omega
      have h2 := Finset.sum_insert (f := id) hnot
      simpa using h2
    rw [hst, pow_add]
  rw [eIcc, Finset.sum_filter, hsplit, Finset.sum_filter, hsecond]

/-- Right-side recurrence: `R(m+2) = R(m+1) + X^(m+2) * R(m)`. -/
private theorem rrGap2_stepR (m : ℕ) :
    (∑ k ∈ Finset.range (m + 2 + 1),
      (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
        * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 2 + 1 - k) k)
    = (∑ k ∈ Finset.range (m + 1 + 1),
      (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
        * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 + 1 - k) k)
      + (PowerSeries.X : PowerSeries ℚ) ^ (m + 2)
        * (∑ k ∈ Finset.range (m + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
            * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k) := by
  have hPascal : ∀ k ∈ Finset.range (m + 2),
      gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 2 + 1 - (k + 1)) (k + 1)
      = gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) (k + 1)
        + (PowerSeries.X : PowerSeries ℚ) ^ (m + 1 - k - k)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k := by
    intro k hk
    have hkle : k ≤ m + 1 := by
      have hlt : k < m + 2 := Finset.mem_range.mp hk
      omega
    have eM : m + 2 + 1 - (k + 1) = (m + 1 - k) + 1 := by omega
    rw [eM]
    exact rrQBinom_succ_succ' _ PowerSeries.constantCoeff_X (m + 1 - k) k
  have hterm : ∀ k ∈ Finset.range (m + 2),
      (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
        * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 2 + 1 - (k + 1)) (k + 1)
      = ((PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) (k + 1))
        + (PowerSeries.X : PowerSeries ℚ) ^ (m + 2)
          * ((PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
            * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k) := by
    intro k hk
    rw [hPascal k hk]
    by_cases h2k : 2 * k ≤ m + 1
    · have e1 : (k + 1) ^ 2 + (m + 1 - k - k) = (m + 2) + k ^ 2 := by
        have hexp : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
        omega
      have hX : (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
            * (PowerSeries.X : PowerSeries ℚ) ^ (m + 1 - k - k)
          = (PowerSeries.X : PowerSeries ℚ) ^ (m + 2)
            * (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) := by
        rw [← pow_add, e1, pow_add]
      have hexpand : (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
            * (gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) (k + 1)
              + (PowerSeries.X : PowerSeries ℚ) ^ (m + 1 - k - k)
                * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k)
          = ((PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
              * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) (k + 1))
            + ((PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
              * (PowerSeries.X : PowerSeries ℚ) ^ (m + 1 - k - k))
              * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k := by
        ring
      rw [hexpand, hX]
      ring
    · have hlt : m + 1 - k < k := by omega
      have h0 : gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k = 0 :=
        gaussBinom_eq_zero_of_lt _ _ _ hlt
      rw [h0]
      simp only [mul_zero, add_zero]
  have hRsplit : (∑ k ∈ Finset.range (m + 2 + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 2 + 1 - k) k)
      = (∑ k ∈ Finset.range (m + 2),
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 2 + 1 - (k + 1))
            (k + 1))
        + (PowerSeries.X : PowerSeries ℚ) ^ (0 ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 2 + 1 - 0) 0 :=
    Finset.sum_range_succ' _ _
  have hS : (∑ k ∈ Finset.range (m + 2),
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 2 + 1 - (k + 1))
            (k + 1))
      = (∑ k ∈ Finset.range (m + 2),
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) (k + 1))
        + (∑ k ∈ Finset.range (m + 2),
          (PowerSeries.X : PowerSeries ℚ) ^ (m + 2)
            * ((PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
              * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k hk => hterm k hk)
  have hRm1peel : (∑ k ∈ Finset.range (m + 1 + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 + 1 - k) k)
      = (∑ k ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 + 1 - (k + 1))
            (k + 1))
        + (PowerSeries.X : PowerSeries ℚ) ^ (0 ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 + 1 - 0) 0 :=
    Finset.sum_range_succ' _ _
  have hG : (∑ k ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 + 1 - (k + 1))
            (k + 1))
      = (∑ k ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    have eK : m + 1 + 1 - (k + 1) = m + 1 - k := by omega
    rw [eK]
  have hsub2 : Finset.range (m + 1) ⊆ Finset.range (m + 2) := by
    intro x hx
    have hlt : x < m + 1 := Finset.mem_range.mp hx
    exact Finset.mem_range.mpr (by omega)
  have hF : (∑ k ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) (k + 1))
      = (∑ k ∈ Finset.range (m + 2),
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + 1) ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) (k + 1)) := by
    apply Finset.sum_subset hsub2
    intro x hx hxnot
    have hxeq : x = m + 1 := by
      have h1 : x < m + 2 := Finset.mem_range.mp hx
      have h2 : ¬ x < m + 1 := fun h => hxnot (Finset.mem_range.mpr h)
      omega
    rw [hxeq]
    have h0 : gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - (m + 1))
        ((m + 1) + 1) = 0 :=
      gaussBinom_eq_zero_of_lt _ _ _ (by omega)
    rw [h0]
    simp only [mul_zero]
  have hS2 : (∑ k ∈ Finset.range (m + 2),
          (PowerSeries.X : PowerSeries ℚ) ^ (m + 2)
            * ((PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
              * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k))
      = (PowerSeries.X : PowerSeries ℚ) ^ (m + 2)
        * (∑ k ∈ Finset.range (m + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
            * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k) := by
    rw [Finset.mul_sum]
    symm
    apply Finset.sum_subset hsub2
    intro x hx hxnot
    have hxeq : x = m + 1 := by
      have h1 : x < m + 2 := Finset.mem_range.mp hx
      have h2 : ¬ x < m + 1 := fun h => hxnot (Finset.mem_range.mpr h)
      omega
    rw [hxeq]
    have h0 : gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - (m + 1))
        (m + 1) = 0 :=
      gaussBinom_eq_zero_of_lt _ _ _ (by omega)
    rw [h0]
    simp only [mul_zero]
  have hC0 : (PowerSeries.X : PowerSeries ℚ) ^ (0 ^ 2)
        * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 2 + 1 - 0) 0
      = (PowerSeries.X : PowerSeries ℚ) ^ (0 ^ 2)
        * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 + 1 - 0) 0 := by
    rw [gaussBinom_zero_right, gaussBinom_zero_right]
  rw [hRsplit, hS, hRm1peel, hG, hF, hS2, hC0]
  ring

/-- Gap-2 subset generating function. -/
private theorem rrGap2_sum (m : ℕ) :
    (∑ S ∈ (Finset.Icc 1 m).powerset.filter rrGap2,
      (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
      = ∑ k ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k := by
  have hg0 : rrGap2 (∅ : Finset ℕ) :=
    fun a ha => absurd ha (Finset.notMem_empty a)
  have base0 : (∑ S ∈ (Finset.Icc 1 0).powerset.filter rrGap2,
        (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
      = ∑ k ∈ Finset.range (0 + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (0 + 1 - k) k := by
    have hIcc0 : Finset.Icc 1 0 = (∅ : Finset ℕ) :=
      Finset.Icc_eq_empty (by omega)
    have hset0 : (∅ : Finset ℕ).powerset.filter rrGap2 = {∅} := by
      rw [Finset.powerset_empty, Finset.filter_singleton]
      simp [hg0]
    rw [hIcc0, hset0, Finset.sum_singleton, Finset.sum_empty, pow_zero,
      show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one,
      gaussBinom_zero_right]
    have e0 : (0 : ℕ) ^ 2 = 0 := by decide
    rw [e0, pow_zero, mul_one]
  have base1 : (∑ S ∈ (Finset.Icc 1 1).powerset.filter rrGap2,
        (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
      = ∑ k ∈ Finset.range (1 + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (1 + 1 - k) k := by
    have hIcc1 : Finset.Icc 1 1 = {1} := Finset.Icc_self 1
    have hg1 : rrGap2 ({1} : Finset ℕ) := by
      intro a ha b hb hab
      have ha1 : a = 1 := Finset.mem_singleton.mp ha
      have hb1 : b = 1 := Finset.mem_singleton.mp hb
      omega
    have hps1 : ({1} : Finset ℕ).powerset = {∅, {1}} := by decide
    have hset1 : ({1} : Finset ℕ).powerset.filter rrGap2 = {∅, {1}} := by
      rw [hps1, Finset.filter_insert, Finset.filter_singleton]
      simp [hg0, hg1]
    rw [hIcc1, hset1, Finset.sum_insert (by decide), Finset.sum_singleton,
      Finset.sum_empty, Finset.sum_singleton, Finset.sum_range_succ,
      Finset.sum_range_one, gaussBinom_zero_right]
    have e0 : (0 : ℕ) ^ 2 = 0 := by decide
    have e1 : (1 : ℕ) ^ 2 = 1 := by decide
    have e11 : (1 : ℕ) + 1 - 1 = 1 := by omega
    rw [e0, e1, e11, gaussBinom_self]
    simp
  have key : ∀ m : ℕ,
      ((∑ S ∈ (Finset.Icc 1 m).powerset.filter rrGap2,
        (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
      = ∑ k ∈ Finset.range (m + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 - k) k)
      ∧ ((∑ S ∈ (Finset.Icc 1 (m + 1)).powerset.filter rrGap2,
        (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
      = ∑ k ∈ Finset.range (m + 1 + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℚ) (m + 1 + 1 - k) k) := by
    intro m
    induction m with
    | zero => exact ⟨base0, base1⟩
    | succ m ih =>
        obtain ⟨h0, h1⟩ := ih
        refine ⟨h1, ?_⟩
        have e : m + 1 + 1 = m + 2 := by omega
        rw [e]
        have hL := rrGap2_stepL m
        have hR := rrGap2_stepR m
        rw [hL, hR, h0, h1]
  exact (key m).1

/-! ## left-side truncation -/

/-- Left card as gap-2 subset count. -/
private theorem rrA_eq_gap2_card (N m : ℕ) (h : N ≤ m) :
    rrA N
      = (((Finset.Icc 1 m).powerset.filter rrGap2).filter
        (fun S => S.sum id = N)).card := by
  have hpos : ∀ S : Finset ℕ,
      S ∈ (Finset.Icc 1 m).powerset.filter rrGap2 →
      ∀ {i}, i ∈ S.val → 0 < i := by
    intro S hS i hi
    have hmem : S ⊆ Finset.Icc 1 m :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hiS : i ∈ S := Finset.mem_val.mp hi
    have hI := Finset.mem_Icc.mp (hmem hiS)
    omega
  have hsumN : ∀ S : Finset ℕ,
      S ∈ ((Finset.Icc 1 m).powerset.filter rrGap2).filter
        (fun S => S.sum id = N) → S.val.sum = N := by
    intro S hS
    have hN : S.sum id = N := (Finset.mem_filter.mp hS).2
    have hbridge : S.val.sum = S.sum id := Finset.sum_val S
    exact hbridge.trans hN
  have hnodup : ∀ p : Nat.Partition N, p ∈ Finset.univ.filter
      (fun p : Nat.Partition N =>
        p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b) →
      p.parts.Nodup := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  have hgap : ∀ p : Nat.Partition N, p ∈ Finset.univ.filter
      (fun p : Nat.Partition N =>
        p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b) →
      ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.2
  simp only [rrA]
  refine Finset.card_bij'
    (fun p _ => p.parts.toFinset)
    (fun S hS => ⟨S.val, hpos S (Finset.mem_filter.mp hS).1, hsumN S hS⟩)
    ?_ ?_ ?_ ?_
  · intro p hp
    show p.parts.toFinset ∈ (((Finset.Icc 1 m).powerset.filter rrGap2).filter
      (fun S => S.sum id = N))
    have nodup := hnodup p hp
    have hgap' := hgap p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_powerset]
      intro x hx
      have hmem : x ∈ p.parts := Multiset.mem_toFinset.mp hx
      have hposx : 0 < x := p.parts_pos hmem
      have hlex : x ≤ N := Nat.Partition.le_of_mem_parts hmem
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb hab
      exact hgap' a (Multiset.mem_toFinset.mp ha) b
        (Multiset.mem_toFinset.mp hb) hab
    · have hval : p.parts.toFinset.val = p.parts := by
        rw [Multiset.toFinset_val, Multiset.Nodup.dedup nodup]
      calc p.parts.toFinset.sum id
          = Multiset.sum p.parts.toFinset.val := (Finset.sum_val _).symm
        _ = Multiset.sum p.parts := by rw [hval]
        _ = N := p.parts_sum
  · intro S hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact S.nodup
    · intro a ha b hb hab
      have hgap2 : rrGap2 S :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
      exact hgap2 a (Finset.mem_val.mp ha) b (Finset.mem_val.mp hb) hab
  · intro p hp
    apply Nat.Partition.ext
    change (p.parts.toFinset).val = p.parts
    have hval : (p.parts.toFinset).val = p.parts := by
      rw [Multiset.toFinset_val, Multiset.Nodup.dedup (hnodup p hp)]
    exact hval
  · intro S hS
    change Multiset.toFinset S.val = S
    exact Finset.val_toFinset S

/-- Left generating series truncation. -/
private theorem rrTrunc_FA (n : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrFA - ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k := by
  have hFL : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrFA - (∑ S ∈ (Finset.Icc 1 n).powerset.filter rrGap2,
        (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    have hjle : j ≤ n := by omega
    have hFAj : PowerSeries.coeff j rrFA = ((rrA j : ℕ) : ℚ) := by
      simp only [rrFA, PowerSeries.coeff_mk]
    have hLj : PowerSeries.coeff j
          (∑ S ∈ (Finset.Icc 1 n).powerset.filter rrGap2,
            (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
        = ((rrA j : ℕ) : ℚ) := by
      rw [map_sum]
      simp only [PowerSeries.coeff_X_pow]
      rw [Finset.sum_boole]
      have hfil : ((Finset.Icc 1 n).powerset.filter rrGap2).filter
            (fun S => j = S.sum id)
          = ((Finset.Icc 1 n).powerset.filter rrGap2).filter
            (fun S => S.sum id = j) := by
        apply Finset.filter_congr
        intro S _
        exact eq_comm
      rw [hfil]
      have hA := rrA_eq_gap2_card j n hjle
      rw [← hA]
    have hsub : PowerSeries.coeff j (rrFA - (∑ S ∈
          (Finset.Icc 1 n).powerset.filter rrGap2,
          (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))) = 0 := by
      rw [map_sub, hFAj, hLj, sub_self]
    exact hsub
  have hLR : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ (∑ S ∈ (Finset.Icc 1 n).powerset.filter rrGap2,
        (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
        - ∑ k ∈ Finset.range (n + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k := by
    have hGap := rrGap2_sum n
    rw [hGap, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro k hk
    have hkle : k ≤ n := by
      have hlt : k < n + 1 := Finset.mem_range.mp hk
      omega
    have hkk : 2 * k ≤ k ^ 2 + 1 := by
      cases k with
      | zero => decide
      | succ t =>
          have hexp : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
          have hsq : 0 ≤ t ^ 2 := Nat.zero_le _
          omega
    by_cases h2k : 2 * k ≤ n + 1
    · have hmin : min (n + 1 - k) (n + 1 - 2 * k) = n + 1 - 2 * k := by
        apply Nat.min_eq_right
        omega
      have h0 := rrXpow_dvd_qPoch_mul_inv_sub_one 1 (n + 1 - k)
        (n + 1 - 2 * k) (by omega)
      have hmin1 : 1 * (min (n + 1 - k) (n + 1 - 2 * k) + 1)
          = n + 1 - 2 * k + 1 := by rw [hmin, one_mul]
      rw [hmin1, pow_one] at h0
      have hq : gaussBinom (PowerSeries.X : PowerSeries ℚ) (n + 1 - k) k
          = rrP (n + 1 - k) * rrIp k * rrIp (n + 1 - 2 * k) := by
        have hle : k ≤ n + 1 - k := by omega
        have hMk : n + 1 - k - k = n + 1 - 2 * k := by omega
        have hQ := rrQBinom_eq_rrQPoch_mul_inv _
          PowerSeries.constantCoeff_X (n + 1 - k) k hle
        rw [hMk] at hQ
        simpa only [rrP, rrIp] using hQ
      have hprod : (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2 + (n + 1 - 2 * k + 1))
          ∣ ((PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k)
            * (rrP (n + 1 - k) * rrIp (n + 1 - 2 * k) - 1) := by
        have hXk : (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
            ∣ (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k :=
          dvd_mul_of_dvd_left (dvd_refl _) _
        have hmul := mul_dvd_mul hXk h0
        rwa [← pow_add] at hmul
      have hle : n + 1 ≤ k ^ 2 + (n + 1 - 2 * k + 1) := by omega
      have hpow : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
          ∣ (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2 + (n + 1 - 2 * k + 1)) :=
        pow_dvd_pow _ hle
      have hdecomp : (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
            * gaussBinom (PowerSeries.X : PowerSeries ℚ) (n + 1 - k) k
          - (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k
          = ((PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k)
            * (rrP (n + 1 - k) * rrIp (n + 1 - 2 * k) - 1) := by
        rw [hq]
        ring
      rw [hdecomp]
      exact dvd_trans hpow hprod
    · have hlt : n + 1 - k < k := by omega
      have h0 : gaussBinom (PowerSeries.X : PowerSeries ℚ) (n + 1 - k) k = 0 :=
        gaussBinom_eq_zero_of_lt _ _ _ hlt
      have hkle2 : n + 1 ≤ k ^ 2 := by omega
      have hpow : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
          ∣ (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) :=
        pow_dvd_pow _ hkle2
      have hzero : (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2)
            * gaussBinom (PowerSeries.X : PowerSeries ℚ) (n + 1 - k) k
          - (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k
          = -((PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k) := by
        rw [h0]
        simp only [mul_zero, zero_sub]
      rw [hzero]
      exact dvd_neg.mpr (dvd_mul_of_dvd_left hpow _)
  have hdecomp : rrFA - ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k
      = (rrFA - (∑ S ∈ (Finset.Icc 1 n).powerset.filter rrGap2,
        (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id)))
        + ((∑ S ∈ (Finset.Icc 1 n).powerset.filter rrGap2,
        (PowerSeries.X : PowerSeries ℚ) ^ (S.sum id))
        - ∑ k ∈ Finset.range (n + 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k) := by
    ring
  rw [hdecomp]
  exact dvd_add hFL hLR

/-! ## right side and product identity -/

/-- Truncated good predicate for the finite `tprod` step. -/
private def rrGoodLe (n m : ℕ) : Prop := rrGood m ∧ m ≤ 5 * n

private instance rrGoodLe_dec (n : ℕ) : DecidablePred (rrGoodLe n) :=
  fun m => inferInstanceAs (Decidable (rrGood m ∧ m ≤ 5 * n))

/-- Truncated restricted-partition generating series. -/
private noncomputable def rrFB' (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun N => (((Nat.Partition.restricted N (rrGoodLe n)).card : ℕ) : ℚ)

section
open scoped PowerSeries.WithPiTopology

/-- Right generating series truncation. -/
private theorem rrTrunc_FB (n : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ (n + 1) ∣ rrE n * rrFB - 1 := by
  have hFBco : ∀ j : ℕ, j ≤ n →
      PowerSeries.coeff j rrFB = PowerSeries.coeff j (rrFB' n) := by
    intro j hj
    simp only [rrFB, rrB, rrFB', PowerSeries.coeff_mk]
    have hset : (Finset.univ.filter (fun p : Nat.Partition j =>
          ∀ m ∈ p.parts, m % 5 = 1 ∨ m % 5 = 4))
        = Nat.Partition.restricted j (rrGoodLe n) := by
      apply Finset.ext
      intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Nat.Partition.restricted]
      constructor
      · intro hp m hm
        have hle : m ≤ j := Nat.Partition.le_of_mem_parts hm
        refine ⟨hp m hm, by omega⟩
      · intro hp m hm
        exact (hp m hm).1
    rw [hset]
  have hFBdvd : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1) ∣ rrFB - rrFB' n := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    have hjle : j ≤ n := by omega
    have hco := hFBco j hjle
    have hsub : PowerSeries.coeff j (rrFB - rrFB' n)
        = PowerSeries.coeff j rrFB - PowerSeries.coeff j (rrFB' n) :=
      map_sub _ _ _
    rw [hsub, hco, sub_self]
  have hT := Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℚ (rrGoodLe n)
  have hFB'eq : rrFB' n = ∏' i, (if rrGoodLe n (i + 1)
      then ∑' j : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ ((i + 1) * j)
      else 1) :=
    hT
  have hfin : (∏' i, (if rrGoodLe n (i + 1)
        then ∑' j : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ ((i + 1) * j) else 1))
      = ∏ i ∈ Finset.range (5 * n),
        (if rrGoodLe n (i + 1)
          then ∑' j : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ ((i + 1) * j)
          else 1) := by
    apply tprod_eq_prod
    intro b hb
    have hb5 : 5 * n ≤ b := by simpa [Finset.mem_range] using hb
    have hneg : ¬ rrGoodLe n (b + 1) := by
      intro hcon
      have hle := hcon.2
      omega
    rw [ite_eq_right hneg]
  have hE1 : rrE n * rrFB' n = 1 := by
    rw [hFB'eq, hfin]
    simp only [rrE]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    have hi5 : i + 1 ≤ 5 * n := by
      have hlt : i < 5 * n := Finset.mem_range.mp hi
      omega
    by_cases hg : rrGood (i + 1)
    · have hg' : rrGoodLe n (i + 1) := ⟨hg, hi5⟩
      rw [ite_eq_left hg, ite_eq_left hg']
      have htsum : (∑' j : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ ((i + 1) * j))
          = ∑' j : ℕ, ((PowerSeries.X : PowerSeries ℚ) ^ (i + 1)) ^ j := by
        apply tsum_congr
        intro j
        rw [pow_mul]
      rw [htsum]
      exact PowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero
        (by simp)
    · have hneg' : ¬ rrGoodLe n (i + 1) := fun hcon => hg hcon.1
      rw [ite_eq_right hg, ite_eq_right hneg', mul_one]
  have hEFB : rrE n * rrFB - 1 = rrE n * (rrFB - rrFB' n) := by
    rw [← hE1]
    ring
  rw [hEFB]
  exact dvd_mul_of_dvd_right hFBdvd _

end

/-- Finite Euler product identity. -/
private theorem rrE_mul_Pi5 (n : ℕ) : rrE n * rrPi5 n = rrP (5 * n) := by
  induction n with
  | zero => simp [rrE, rrPi5, rrP, qPochFin]
  | succ n ih =>
      have h5n : 5 * (n + 1) = 5 * n + 5 := by ring
      have hE : rrE (n + 1)
          = rrE n * ∏ t ∈ Finset.range 5,
            (if rrGood (5 * n + t + 1)
              then 1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + t + 1)
              else 1) := by
        simp only [rrE]
        rw [show 5 * (n + 1) = 5 * n + 5 from by ring, Finset.prod_range_add]
      have hP : rrP (5 * (n + 1))
          = rrP (5 * n) * ∏ t ∈ Finset.range 5,
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ ((5 * n + t) + 1)) := by
        rw [h5n]
        exact (rrP_mul_tail (5 * n) 5).symm
      have hPi : rrPi5 (n + 1)
          = rrPi5 n * ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 2))
            * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 3))
            * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 5))) := by
        simp only [rrPi5, Finset.prod_range_succ]
      rw [hE, hPi, hP, ← ih]
      have g1 : rrGood (5 * n + 0 + 1) := by
        simp only [rrGood]
        have : (5 * n + 0 + 1) % 5 = 1 := by omega
        rw [this]
        left
        rfl
      have g2 : ¬ rrGood (5 * n + 1 + 1) := by
        simp only [rrGood]
        have hmod : (5 * n + 1 + 1) % 5 = 2 := by omega
        rw [hmod]
        decide
      have g3 : ¬ rrGood (5 * n + 2 + 1) := by
        simp only [rrGood]
        have hmod : (5 * n + 2 + 1) % 5 = 3 := by omega
        rw [hmod]
        decide
      have g4 : rrGood (5 * n + 3 + 1) := by
        simp only [rrGood]
        have : (5 * n + 3 + 1) % 5 = 4 := by omega
        rw [this]
        right
        rfl
      have g5 : ¬ rrGood (5 * n + 4 + 1) := by
        simp only [rrGood]
        have hmod : (5 * n + 4 + 1) % 5 = 0 := by omega
        rw [hmod]
        decide
      have hprod5 : (∏ t ∈ Finset.range 5,
            (if rrGood (5 * n + t + 1)
              then 1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + t + 1)
              else 1))
          = (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 1))
            * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 4)) := by
        rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
          Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
        simp only [g1, g2, g3, g4, g5, ↓reduceIte]
        have e1 : 5 * n + 0 + 1 = 5 * n + 1 := by omega
        have e4 : 5 * n + 3 + 1 = 5 * n + 4 := by omega
        rw [e1, e4]
        ring
      have hprod5' : (∏ t ∈ Finset.range 5,
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ ((5 * n + t) + 1)))
          = ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 1))
            * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 4)))
            * (((1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 2))
              * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 3))
              * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (5 * n + 5)))) := by
        rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
          Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
        have e1 : (5 * n + 0) + 1 = 5 * n + 1 := by omega
        have e2 : (5 * n + 1) + 1 = 5 * n + 2 := by omega
        have e3 : (5 * n + 2) + 1 = 5 * n + 3 := by omega
        have e4 : (5 * n + 3) + 1 = 5 * n + 4 := by omega
        have e5 : (5 * n + 4) + 1 = 5 * n + 5 := by omega
        rw [e1, e2, e3, e4, e5]
        ring
      rw [hprod5, hprod5']
      ring

/-- Constant coefficient of `E(n)` is one. -/
private theorem rrE_constantCoeff (n : ℕ) :
    PowerSeries.constantCoeff (rrE n) = 1 := by
  simp only [rrE]
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i _
  by_cases hg : rrGood (i + 1)
  · simp only [hg, ↓reduceIte]
    rw [map_sub, map_one]
    have hX : PowerSeries.constantCoeff
        ((PowerSeries.X : PowerSeries ℚ) ^ (i + 1)) = 0 := by
      rw [map_pow, PowerSeries.constantCoeff_X]
      exact zero_pow (by omega : i + 1 ≠ 0)
    rw [hX, sub_zero]
  · simp only [hg, ↓reduceIte, map_one]

/-- **Rogers–Ramanujan identity (first form).** For every natural number $n$, the number of
partitions of $n$ into distinct parts, any two of which differ by at least $2$, equals the number
of partitions of $n$ all of whose parts are congruent to $1$ or $4$ modulo $5$.

Proves `Wanted` entry `rogers_ramanujan_difference_two_vs_one_four`.

Source: George E. Andrews and David Newman, "The Minimal Excludant in
Integer Partitions," Journal of Integer Sequences 23 (2020), Article 20.2.3,
quoted Rogers–Ramanujan theorem at lines 173–178.
Public TeX URL:
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Andrews/andrews5.tex`
Retrieved TeX SHA-256:
`9f5fc80c212b5dc9cb8d7bcbc905d717f1aa9673ad7ada690f3eca3065c308c9` -/
public theorem rogers_ramanujan_difference_two_vs_one_four (n : ℕ) :
    (Finset.univ.filter (fun p : Nat.Partition n =>
      p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b)).card =
    (Finset.univ.filter (fun p : Nat.Partition n =>
      ∀ m ∈ p.parts, m % 5 = 1 ∨ m % 5 = 4)).card := by
  have h1 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrP n * rrFA - rrPi5 n := by
    have hFA := rrTrunc_FA n
    have hRR := rrTrunc_RR n
    have hJTP := rrTrunc_JTP n
    have e1 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrP n * rrFA
          - rrP n * (∑ k ∈ Finset.range (n + 1),
            (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k) := by
      have e : rrP n * rrFA
            - rrP n * (∑ k ∈ Finset.range (n + 1),
              (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k)
          = rrP n * (rrFA - ∑ k ∈ Finset.range (n + 1),
            (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k) := by
        ring
      rw [e]
      exact dvd_mul_of_dvd_right hFA _
    have e2 : rrP n * rrFA - rrPi5 n
        = (rrP n * rrFA - rrP n * (∑ k ∈ Finset.range (n + 1),
            (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k))
          + ((rrP n * (∑ k ∈ Finset.range (n + 1),
            (PowerSeries.X : PowerSeries ℚ) ^ (k ^ 2) * rrIp k) - rrT n)
            + (rrT n - rrPi5 n)) := by
      ring
    rw [e2]
    exact dvd_add e1 (dvd_add hRR hJTP)
  have hP5n : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrP (5 * n) - rrP n := by
    have h0 := rrXpow_dvd_qPoch_sub 1 (5 * n) n
    have hmin : min (5 * n) n = n := Nat.min_eq_right (by omega)
    have hmin1 : 1 * (min (5 * n) n + 1) = n + 1 := by rw [hmin, one_mul]
    have hQ1 : (PowerSeries.X ^ 1 : PowerSeries ℚ) = PowerSeries.X :=
      pow_one _
    rw [hmin1, hQ1] at h0
    simpa only [rrP] using h0
  have h2 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrE n * (rrP n * rrFA) - rrP n := by
    have e1 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrE n * (rrP n * rrFA) - rrE n * rrPi5 n := by
      have e : rrE n * (rrP n * rrFA) - rrE n * rrPi5 n
          = rrE n * (rrP n * rrFA - rrPi5 n) := by ring
      rw [e]
      exact dvd_mul_of_dvd_right h1 _
    have hEP : rrE n * rrPi5 n = rrP (5 * n) := rrE_mul_Pi5 n
    have ez : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrE n * rrPi5 n - rrP (5 * n) := by
      rw [hEP, sub_self]
      exact dvd_zero _
    have e2 : rrE n * (rrP n * rrFA) - rrP n
        = (rrE n * (rrP n * rrFA) - rrE n * rrPi5 n)
          + ((rrE n * rrPi5 n - rrP (5 * n)) + (rrP (5 * n) - rrP n)) := by
      ring
    rw [e2]
    exact dvd_add e1 (dvd_add ez hP5n)
  have h3 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
      ∣ rrE n * rrFA - 1 := by
    have hPip : rrP n * rrIp n = 1 := rrP_mul_ip n
    have e1 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrIp n * (rrE n * (rrP n * rrFA)) - rrIp n * rrP n := by
      have e : rrIp n * (rrE n * (rrP n * rrFA)) - rrIp n * rrP n
          = rrIp n * (rrE n * (rrP n * rrFA) - rrP n) := by ring
      rw [e]
      exact dvd_mul_of_dvd_right h2 _
    have e2 : rrIp n * (rrE n * (rrP n * rrFA)) - rrIp n * rrP n
        = rrE n * rrFA - 1 := by
      have h1 : rrIp n * (rrE n * (rrP n * rrFA))
          = (rrE n * rrFA) * (rrP n * rrIp n) := by ring
      have h2c : rrIp n * rrP n = rrP n * rrIp n := mul_comm _ _
      rw [h1, h2c, hPip, mul_one]
    rwa [e2] at e1
  have hFB := rrTrunc_FB n
  have h5 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1) ∣ rrFA - rrFB := by
    have h4 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ rrE n * (rrFA - rrFB) := by
      have e : rrE n * (rrFA - rrFB)
          = (rrE n * rrFA - 1) - (rrE n * rrFB - 1) := by ring
      rw [e]
      exact dvd_sub h3 hFB
    have hEcc : PowerSeries.constantCoeff (rrE n) ≠ 0 := by
      rw [rrE_constantCoeff n]
      exact one_ne_zero
    have hcancel : (rrE n)⁻¹ * rrE n = 1 :=
      PowerSeries.inv_mul_cancel _ hEcc
    have e1 : (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)
        ∣ (rrE n)⁻¹ * (rrE n * (rrFA - rrFB)) :=
      dvd_mul_of_dvd_right h4 _
    have e2 : (rrE n)⁻¹ * (rrE n * (rrFA - rrFB)) = rrFA - rrFB := by
      rw [← mul_assoc, hcancel, one_mul]
    rwa [e2] at e1
  have hco : PowerSeries.coeff n (rrFA - rrFB) = 0 := by
    rw [PowerSeries.X_pow_dvd_iff] at h5
    exact h5 n (by omega)
  have hFAc : PowerSeries.coeff n rrFA = ((rrA n : ℕ) : ℚ) := by
    simp only [rrFA, PowerSeries.coeff_mk]
  have hFBc : PowerSeries.coeff n rrFB = ((rrB n : ℕ) : ℚ) := by
    simp only [rrFB, PowerSeries.coeff_mk]
  have hsub : PowerSeries.coeff n rrFA - PowerSeries.coeff n rrFB = 0 := by
    have e : PowerSeries.coeff n rrFA - PowerSeries.coeff n rrFB
        = PowerSeries.coeff n (rrFA - rrFB) := (map_sub _ _ _).symm
    rw [e]
    exact hco
  rw [hFAc, hFBc] at hsub
  have hcast : ((rrA n : ℕ) : ℚ) = ((rrB n : ℕ) : ℚ) :=
    sub_eq_zero.mp hsub
  have hNat : rrA n = rrB n := Nat.cast_injective hcast
  exact hNat

end MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted

end
