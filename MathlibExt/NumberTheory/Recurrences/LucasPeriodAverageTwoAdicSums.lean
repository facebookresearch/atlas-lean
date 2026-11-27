/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.LucasPeriodAverage
public import MathlibExt.NumberTheory.Recurrences.NondegenerateLucasPair
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Nondivisibility of Lucas sums at powers of two -/

namespace MetaMathlibExt

@[expose] public section

/-- **Moduli divisible by their Lucas period.** For the Lucas sequence $U$ with integer
parameters $P$ and $Q \ne 0$ ($U_0 = 0$, $U_1 = 1$, $U_{j+2} = P U_{j+1} - Q U_j$), $S(U)$ is
the set of positive integers $n$ coprime to $Q$ such that the period $\pi_U(n)$ of $U$ modulo
$n$ divides $n$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.2. -/
def lucasPeriodSet (params : LucasSequenceParams) : Set ℕ :=
  {n | 0 < n ∧ IsCoprime (n : ℤ) params.q ∧ lucasUPeriod params n ∣ n}

/-- **Average set of a Lucas sequence.** Let $U$ be the Lucas sequence with parameters $P$ and
$Q \ne 0$, given by $U_0 = 0$, $U_1 = 1$ and $U_{k+2} = P U_{k+1} - Q U_k$, and let $S(U)$ be the
set of positive integers $n$ coprime to $Q$ such that the period $\pi_U(n)$ of $U$ modulo $n$
divides $n$. The average set $S'(U)$ is the set of $n \in S(U)$ with $n \mid U_1 + \dots + U_n$,
that is, those $n \in S(U)$ for which the average $(U_1 + \dots + U_n)/n$ is an integer.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.2. -/
def lucasAverageSet (params : LucasSequenceParams) : Set ℕ :=
  {n | n ∈ lucasPeriodSet params ∧ (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i}

end

namespace LucasTwoAdicSums

private def blockSum (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range n, w (j + 1)

private theorem blockSum_eq (w : ℕ → ℤ) (n : ℕ) :
    blockSum w n = ∑ j ∈ Finset.Icc 1 n, w j := by
  induction n with
  | zero => simp [blockSum]
  | succ n ih =>
    rw [blockSum, Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ← ih]
    rfl

private theorem blockSum_add (w : ℕ → ℤ) (n m : ℕ) :
    blockSum w (n + m) = blockSum w n + blockSum (fun j => w (n + j)) m := by
  simp [blockSum, Finset.sum_range_add, Nat.add_assoc]

-- A shift by 2^(k+1) differs from the identity by 2^(k+1) times a linear
-- combination of the current term and its successor.
private theorem shift_pow_two {p b : ℤ} (he : Even p) (ho : Odd b)
    (hpb : p + b ≡ 1 [ZMOD 4]) (k : ℕ) :
    ∃ a c : ℤ, (k = 0 → 2 ∣ a + c) ∧
      ∀ (w : ℕ → ℤ), (∀ j, w (j + 2) = p * w (j + 1) + b * w j) →
      ∀ j, w (j + 2 ^ (k + 1)) = w j + 2 ^ (k + 1) * (a * w j + c * w (j + 1)) := by
  induction k with
  | zero =>
    obtain ⟨d, hd⟩ := he
    obtain ⟨e, hb⟩ := ho
    have hdiv := Int.modEq_iff_dvd.mp hpb
    rw [hd, hb] at hdiv
    obtain ⟨z, hz⟩ := hdiv
    refine ⟨e, d, fun _ => ⟨-z, by omega⟩, fun w hw j => ?_⟩
    norm_num only [Nat.zero_add, pow_one]
    rw [hw j, hd, hb]
    ring
  | succ k ih =>
    obtain ⟨a, c, -, h⟩ := ih
    let D : ℤ := 2 ^ k
    refine ⟨a + D * (a ^ 2 + b * c ^ 2), c + D * (2 * a * c + p * c ^ 2),
      by simp, fun w hw j => ?_⟩
    have h₀ := h w hw j
    have h₁ := h w hw (j + 1)
    have h₂ := h w hw (j + 2 ^ (k + 1))
    have hi : j + 2 ^ (k + 1) + 1 = j + 1 + 2 ^ (k + 1) := by omega
    have hj : j + 2 ^ (k + 1) + 2 ^ (k + 1) = j + 2 ^ (k + 1 + 1) := by
      rw [pow_succ (2 : ℕ) (k + 1), Nat.mul_two, Nat.add_assoc]
    rw [hi, h₀, h₁, hw j] at h₂
    rw [← hj, h₂]
    dsimp [D]
    simp only [pow_succ' (2 : ℤ)]
    ring

-- In the two nondivisibility cases the normalized block sum is the sum of
-- the initial pair modulo 2. The length-two block is the base case.
private theorem blockSum_pow_two {p b : ℤ} (he : Even p) (ho : Odd b)
    (hpb : p + b ≡ 1 [ZMOD 4]) (w : ℕ → ℤ)
    (hw : ∀ j, w (j + 2) = p * w (j + 1) + b * w j) (k : ℕ) :
    blockSum w (2 ^ (k + 1)) ≡ 2 ^ k * (w 0 + w 1) [ZMOD 2 ^ (k + 1)] := by
  induction k generalizing w with
  | zero =>
    simp only [Nat.zero_add, pow_one, pow_zero, one_mul, blockSum]
    rw [show (2 : ℕ) = 1 + 1 by decide, Finset.sum_range_succ, Finset.sum_range_one]
    rw [show (0 : ℕ) + 1 = 1 by rfl, hw 0]
    obtain ⟨d, hd⟩ := he
    obtain ⟨e, hb⟩ := ho
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(d * w 1 + e * w 0), ?_⟩
    rw [hd, hb]
    ring
  | succ k ih =>
    obtain ⟨a, c, hac, h⟩ := shift_pow_two he ho hpb k
    let m : ℕ := 2 ^ (k + 1)
    let v (j : ℕ) : ℤ := a * w j + c * w (j + 1)
    have hv (j : ℕ) : v (j + 2) = p * v (j + 1) + b * v j := by
      dsimp [v]
      rw [show j + 2 + 1 = (j + 1) + 2 by omega, hw (j + 1), hw j]
      ring
    have hs : blockSum (fun j => w (m + j)) m = blockSum w m + 2 ^ (k + 1) * blockSum v m := by
      simp only [blockSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Nat.add_comm m] using h w hw (j + 1)
    have hm : 2 ^ (k + 1 + 1) = m + m := by rw [pow_succ, Nat.mul_two]
    rw [hm, blockSum_add, hs, ← add_assoc]
    have hd := (ih w hw).mul_left' (c := 2)
    have hmod : (2 : ℤ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := pow_succ' ..
    rw [hmod]
    have hz : 2 * 2 ^ (k + 1) ∣ 2 ^ (k + 1) * blockSum v m := by
      have hvEven : 2 ∣ blockSum v m := by
        cases k with
        | zero =>
          have h₁ := (ih v hv).of_dvd (show (2 : ℤ) ∣ 2 ^ (0 + 1) by norm_num)
          have hpair : 2 ∣ v 0 + v 1 := by
            obtain ⟨d, hd⟩ := he
            obtain ⟨e, hb⟩ := ho
            obtain ⟨z, hz⟩ := hac rfl
            refine ⟨z * (w 0 + w 1) + c * (d * w 1 + e * w 0), ?_⟩
            dsimp [v]
            rw [hw 0, hd, hb]
            linear_combination (w 0 + w 1) * hz
          exact Int.modEq_zero_iff_dvd.mp (h₁.trans
            (Int.modEq_zero_iff_dvd.mpr (by simpa using hpair)))
        | succ k =>
          have h₁ : (2 : ℤ) ∣ 2 ^ (k + 1) * (v 0 + v 1) := by
            rw [pow_succ']
            exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _
          have h₂ : (2 : ℤ) ∣ 2 ^ (k + 1 + 1) := by
            rw [pow_succ']
            exact dvd_mul_right 2 _
          exact Int.modEq_zero_iff_dvd.mp (((ih v hv).of_dvd h₂).trans
            (Int.modEq_zero_iff_dvd.mpr h₁))
      simpa [mul_comm 2 (2 ^ (k + 1) : ℤ)] using mul_dvd_mul_left (2 ^ (k + 1) : ℤ) hvEven
    have hzero := Int.modEq_zero_iff_dvd.mpr hz
    simpa only [m, two_mul, pow_succ' (2 : ℤ), add_zero, add_mul] using hd.add hzero

private theorem blockSum_mul_pow_two {p b : ℤ} (he : Even p) (ho : Odd b)
    (hpb : p + b ≡ 1 [ZMOD 4]) (w : ℕ → ℤ)
    (hw : ∀ j, w (j + 2) = p * w (j + 1) + b * w j) (k t : ℕ) :
    blockSum w (2 ^ (k + 1) * t) ≡ (t : ℤ) * (2 ^ k * (w 0 + w 1))
      [ZMOD 2 ^ (k + 1)] := by
  let m : ℕ := 2 ^ (k + 1)
  obtain ⟨a, c, -, h⟩ := shift_pow_two he ho hpb k
  have hshift (j : ℕ) : w (j + m) ≡ w j [ZMOD 2 ^ (k + 1)] :=
    Int.modEq_iff_dvd.mpr ⟨-(a * w j + c * w (j + 1)), by rw [h w hw j]; ring⟩
  have hrep (s j : ℕ) : w (m * s + j) ≡ w j [ZMOD 2 ^ (k + 1)] := by
    induction s with
    | zero => simp [Int.ModEq]
    | succ s ih =>
      rw [Nat.mul_succ, Nat.add_right_comm]
      exact (hshift (m * s + j)).trans ih
  have hblock (s l : ℕ) : blockSum (fun j => w (m * s + j)) l ≡ blockSum w l
      [ZMOD 2 ^ (k + 1)] := by
    induction l with
    | zero => simp [blockSum, Int.ModEq]
    | succ l ih =>
      simp only [blockSum, Finset.sum_range_succ] at ih ⊢
      exact ih.add (hrep s (l + 1))
  change blockSum w (m * t) ≡ _ [ZMOD _]
  induction t with
  | zero => simp [blockSum, Int.ModEq]
  | succ t ih =>
    rw [Nat.mul_succ, blockSum_add, Nat.cast_succ, add_mul, one_mul]
    exact ih.add ((hblock t m).trans (blockSum_pow_two he ho hpb w hw k))

private theorem sum_not_dvd (params : LucasSequenceParams) (he : Even params.p)
    (ho : Odd (-params.q)) (hpb : params.p + -params.q ≡ 1 [ZMOD 4])
    (n k : ℕ) (hk : 1 ≤ k) (hd : 2 ^ k ∣ n) (hnd : ¬ 2 ^ (k + 1) ∣ n) :
    ¬ ((2 ^ k : ℕ) : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨t, rfl⟩ := hd
  have ht : ¬ 2 ∣ t := by
    rintro ⟨s, rfl⟩
    apply hnd
    exact ⟨s, by rw [pow_succ (2 : ℕ) (k + 1), mul_assoc]⟩
  have hw (j : ℕ) : lucasU params (j + 2) =
      params.p * lucasU params (j + 1) + -params.q * lucasU params j := by
    rw [lucasU_add_two, sub_eq_add_neg, neg_mul]
  have h := blockSum_mul_pow_two he ho hpb (lucasU params) hw k t
  simp only [blockSum_eq, show lucasU params 0 = 0 by rfl,
    show lucasU params 1 = 1 by rfl, zero_add, mul_one] at h
  rw [Nat.cast_pow, Nat.cast_ofNat]
  intro hd
  have hd' := Int.modEq_zero_iff_dvd.mp (h.symm.trans (Int.modEq_zero_iff_dvd.mpr hd))
  obtain ⟨s, hs⟩ := hd'
  apply ht
  apply Int.ofNat_dvd.mp
  refine ⟨s, mul_left_cancel₀ (pow_ne_zero k (by decide : (2 : ℤ) ≠ 0)) ?_⟩
  rw [show ((2 : ℕ) : ℤ) = 2 by rfl]
  calc
    (2 : ℤ) ^ k * (t : ℤ) = 2 ^ (k + 1) * s := by rwa [mul_comm]
    _ = 2 ^ k * (2 * s) := by rw [pow_succ, mul_assoc]

private theorem sum_not_dvd_of_even (params : LucasSequenceParams) (he : Even params.p)
    (ho : Odd (-params.q)) (hpb : params.p + -params.q ≡ 1 [ZMOD 4]) (n : ℕ)
    (hn : 0 < n) (hen : Even n) :
    ¬ (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i := by
  let k := multiplicity 2 n
  have hval : ∀ j : ℕ, 2 ^ j ∣ n ↔ j ≤ k := fun j =>
    Nat.pow_dvd_iff_le_multiplicity (p := 2) (k := j) (by decide) hn.ne'
  have hk : 1 ≤ k := (hval 1).mp (by simpa [even_iff_two_dvd] using hen)
  have hd := (hval k).mpr le_rfl
  have hnd : ¬ 2 ^ (k + 1) ∣ n := fun h => by have := (hval (k + 1)).mp h; omega
  intro h
  exact sum_not_dvd params he ho hpb n k hk hd hnd ((Int.ofNat_dvd.mpr hd).trans h)

end LucasTwoAdicSums

open LucasTwoAdicSums in
private theorem nondivisibility_clauses (params : LucasSequenceParams) (he : Even params.p)
    (ho : Odd (-params.q)) (hpb : params.p + -params.q ≡ 1 [ZMOD 4]) :
    (∀ n k : ℕ, 1 ≤ k → 2 ^ k ∣ n → ¬ 2 ^ (k + 1) ∣ n →
      ¬ ((2 ^ k : ℕ) : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    (∀ n, 0 < n → Even n → ¬ ∃ x, n ∣ x ∧ x ∈ lucasAverageSet params) ∧
    ∀ m : ℕ, 0 < m → (m : ℤ) ∣ ∑ i ∈ Finset.Icc 1 m, lucasU params i → Odd m := by
  refine ⟨sum_not_dvd params he ho hpb, ?_, ?_⟩
  · rintro n _ hn ⟨x, hnx, hx⟩
    have hxpos : 0 < x := hx.1.1
    have hxdvd : (x : ℤ) ∣ ∑ i ∈ Finset.Icc 1 x, lucasU params i := hx.2
    have hxeven : Even x := even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hn).trans hnx)
    exact sum_not_dvd_of_even params he ho hpb x hxpos hxeven hxdvd
  · intro m hm hd
    exact (Nat.even_or_odd m).resolve_left fun heven =>
      sum_not_dvd_of_even params he ho hpb m hm heven hd

@[expose] public section

set_option linter.unusedVariables false in
/-- **Lucas sums not divisible by $2^k$ when $P \equiv 0$ and $-Q \equiv 1 \pmod 4$.** Let $P$
and $Q \ne 0$ be integers forming a nondegenerate Lucas pair with $P \equiv 0 \pmod 4$ and
$-Q \equiv 1 \pmod 4$, and let $U$ be the Lucas sequence given by $U_0 = 0$, $U_1 = 1$ and
$U_{k+2} = P U_{k+1} - Q U_k$. Let $S'(U)$ be the set of positive integers $n$ coprime to $Q$
such that the period $\pi_U(n)$ of $U$ modulo $n$ divides $n$ and $n \mid U_1 + \dots + U_n$.
Then for every $k \ge 1$ and every natural number $n$ with $2^k \mid n$ and $2^{k+1} \nmid n$,
$2^k$ does not divide $U_1 + \dots + U_n$; for every even $n > 0$, no element of $S'(U)$ is
divisible by $n$; and every positive integer $m$ with $m \mid U_1 + \dots + U_m$ is odd.

In the paper's notation $a = P$ and $b = -Q$, so the hypotheses are $a \equiv 0$ and
$b \equiv 1 \pmod 4$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.16
(`integers-2024-A36-thm-2-16`). -/
public theorem lucasU_sum_not_dvd_of_p_zero_mod_four (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p ≡ 0 [ZMOD 4]) (hq : -params.q
        ≡ 1 [ZMOD 4]) :
    (∀ n k : ℕ, 1 ≤ k → 2 ^ k ∣ n → ¬ 2 ^ (k + 1) ∣ n →
      ¬ ((2 ^ k : ℕ) : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    (∀ n, 0 < n → Even n → ¬ ∃ x, n ∣ x ∧ x ∈ lucasAverageSet params) ∧
    ∀ m : ℕ, 0 < m → (m : ℤ) ∣ ∑ i ∈ Finset.Icc 1 m, lucasU params i → Odd m := by
  have he : Even params.p := by
    rw [Int.even_iff]
    exact hp.of_dvd (by decide : (2 : ℤ) ∣ 4)
  have ho : Odd (-params.q) := by
    rw [Int.odd_iff]
    exact hq.of_dvd (by decide : (2 : ℤ) ∣ 4)
  exact nondivisibility_clauses params he ho (by simpa using hp.add hq)

set_option linter.unusedVariables false in
/-- **Lucas sums not divisible by $2^k$ when $P \equiv 2$ and $-Q \equiv -1 \pmod 4$.** Let $P$
and $Q \ne 0$ be integers forming a nondegenerate Lucas pair with $P \equiv 2 \pmod 4$ and
$-Q \equiv -1 \pmod 4$, and let $U$ be the Lucas sequence given by $U_0 = 0$, $U_1 = 1$ and
$U_{k+2} = P U_{k+1} - Q U_k$. Let $S'(U)$ be the set of positive integers $n$ coprime to $Q$
such that the period $\pi_U(n)$ of $U$ modulo $n$ divides $n$ and $n \mid U_1 + \dots + U_n$.
Then for every $k \ge 1$ and every natural number $n$ with $2^k \mid n$ and $2^{k+1} \nmid n$,
$2^k$ does not divide $U_1 + \dots + U_n$; for every even $n > 0$, no element of $S'(U)$ is
divisible by $n$; and every positive integer $m$ with $m \mid U_1 + \dots + U_m$ is odd.

In the paper's notation $a = P$ and $b = -Q$, so the hypotheses are $a \equiv 2$ and
$b \equiv -1 \pmod 4$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.18
(`integers-2024-A36-thm-2-18`). -/
public theorem lucasU_sum_not_dvd_of_p_two_mod_four (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p ≡ 2 [ZMOD 4]) (hq : -params.q
        ≡ -1 [ZMOD 4]) :
    (∀ n k : ℕ, 1 ≤ k → 2 ^ k ∣ n → ¬ 2 ^ (k + 1) ∣ n →
      ¬ ((2 ^ k : ℕ) : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    (∀ n, 0 < n → Even n → ¬ ∃ x, n ∣ x ∧ x ∈ lucasAverageSet params) ∧
    ∀ m : ℕ, 0 < m → (m : ℤ) ∣ ∑ i ∈ Finset.Icc 1 m, lucasU params i → Odd m := by
  have he : Even params.p := by
    rw [Int.even_iff]
    exact (hp.of_dvd (by decide : (2 : ℤ) ∣ 4)).trans (by decide : (2 : ℤ) ≡ 0 [ZMOD 2])
  have ho : Odd (-params.q) := by
    rw [Int.odd_iff]
    exact (hq.of_dvd (by decide : (2 : ℤ) ∣ 4)).trans (by decide : (-1 : ℤ) ≡ 1 [ZMOD 2])
  exact nondivisibility_clauses params he ho (by simpa using hp.add hq)

end

end MetaMathlibExt
