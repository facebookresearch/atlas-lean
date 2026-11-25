/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Doubling the decimal blocks of reciprocals of Mersenne primes -/

namespace MetaMathlibExt

-- Extracting a base-`q` block of the repeating numerator is a step of long division.
private theorem reciprocalBlock_eq_div {q M p i : ℕ} (hq : 0 < q) (hM : 0 < M)
    (hperiod : q ^ p % M = 1) (hi : i < p) :
    ((q ^ p - 1) / M / q ^ (p - (i + 1))) % q = q * (q ^ i % M) / M := by
  have hprefix : (q ^ p - 1) / M = q ^ p / M := by
    have h := Nat.mod_add_div (q ^ p) M
    rw [hperiod] at h
    have h' : q ^ p - 1 = M * (q ^ p / M) := by omega
    rw [h', Nat.mul_div_cancel_left _ hM]
  have hpow : q ^ p = q ^ (p - (i + 1)) * q ^ (i + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : i + 1 ≤ p)]
  have hstep : q ^ (i + 1) = q * (q ^ i % M) + (q ^ i / M * q) * M := by
    calc
      q ^ (i + 1) = q * (q ^ i % M + M * (q ^ i / M)) := by
        rw [Nat.mod_add_div, pow_succ']
      _ = _ := by ring
  have hlt : q * (q ^ i % M) / M < q :=
    (Nat.div_lt_iff_lt_mul hM).2 (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hM) hq)
  rw [hprefix, Nat.div_div_eq_div_mul, mul_comm M, ← Nat.div_div_eq_div_mul,
    hpow, Nat.mul_div_cancel_left _ (pow_pos hq _), hstep, Nat.add_mul_div_right _ _ hM,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- **Doubling recurrence for the blocks of $1/(2^p - 1)$.** Let $p$ be a natural number such
that $M = 2^p - 1$ is prime, let $L$ be the multiplicative order of $10$ modulo $M$ (the period of
the decimal expansion of $1/M$), and suppose that $p$ divides $L$. Put $\ell = L/p$ and let
$N = (10^L - 1)/M$ be the repeating block of $1/M$, read as an $L$-digit integer with leading
zeros. For $1 \le k \le p$ let $B_k = \lfloor N / 10^{\ell (p - k)} \rfloor \bmod 10^\ell$ be
the $k$-th block of $\ell$ digits of $N$ from the left, and extend the indices to all $j \ge 1$
by $B_j = B_k$ where $k = ((j - 1) \bmod p) + 1$. Let $r$ and $s$ be natural numbers with
$1 \le r \le p - 1$, $10^\ell \equiv 2^r \pmod{M}$ and $rs \equiv 1 \pmod{p}$. Then, as
integers:

(i) for every $k$ with $1 \le k \le p$, $B_{ks+1} = 2B_{(k-1)s+1} - 10^\ell$ if $k = p$,
$B_{ks+1} = 2B_{(k-1)s+1} + 1$ if $k = p - r$, and $B_{ks+1} = 2B_{(k-1)s+1}$ otherwise;

(ii) if $r = 1$, then for every $k$ with $1 \le k \le p$, $B_{k+1} = 2B_k - 10^\ell$ if $k = p$,
$B_{k+1} = 2B_k + 1$ if $k = p - 1$, and $B_{k+1} = 2B_k$ otherwise;

(iii) $B_1 + B_2 + \dots + B_p = 10^\ell - 1$.

Source: Amitabha Tripathi, *A Note on the Decimal Expansion of Reciprocals of Mersenne Primes*,
INTEGERS 24 (2024), Article A14, Theorem 1 (`integers-2024-A14-thm-1`). -/
public theorem mersenne_reciprocal_block_recurrence (p : ℕ) (hM : (2 ^ p - 1).Prime)
    (hdvd : p ∣ orderOf (10 : ZMod (2 ^ p - 1))) (r s : ℕ) (hr₁ : 1 ≤ r) (hr₂ : r ≤ p - 1)
    (hr : 10 ^ (orderOf (10 : ZMod (2 ^ p - 1)) / p) ≡ 2 ^ r [MOD 2 ^ p - 1])
    (hs : r * s ≡ 1 [MOD p]) :
    let L := orderOf (10 : ZMod (2 ^ p - 1))
    let ℓ := L / p
    let B : ℕ → ℤ := fun j =>
      (((10 ^ L - 1) / (2 ^ p - 1) / 10 ^ (ℓ * (p - ((j - 1) % p + 1)))) % 10 ^ ℓ : ℕ)
    (∀ k ∈ Finset.Icc 1 p,
      B (k * s + 1) =
        if k = p then 2 * B ((k - 1) * s + 1) - 10 ^ ℓ
        else if k = p - r then 2 * B ((k - 1) * s + 1) + 1
        else 2 * B ((k - 1) * s + 1)) ∧
    (r = 1 → ∀ k ∈ Finset.Icc 1 p,
      B (k + 1) =
        if k = p then 2 * B k - 10 ^ ℓ
        else if k = p - 1 then 2 * B k + 1
        else 2 * B k) ∧
    ∑ k ∈ Finset.Icc 1 p, B k = 10 ^ ℓ - 1 := by
  intro L ℓ B
  let M := 2 ^ p - 1
  let q := 10 ^ ℓ
  change q ≡ 2 ^ r [MOD M] at hr
  have hp : 1 < p := by omega
  have hM₀ : 0 < M := hM.pos
  have hq : 0 < q := pow_pos (by decide) _
  have htwo : 2 ^ p = M + 1 := Nat.sub_add_cancel Nat.one_le_two_pow |>.symm
  have htwo_mod : 2 ^ p ≡ 1 [MOD M] := by
    rw [htwo, Nat.ModEq, Nat.add_mod]
    simp
  let R (i : ℕ) : ℕ := 2 ^ (i % p)
  let F (i : ℕ) : ℤ := (q * R i / M : ℕ)
  have hR_lt (i : ℕ) : R i < M := by
    have hi := Nat.mod_lt i (by omega : 0 < p)
    have hle : R i ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hmore : 1 < 2 ^ (p - 1) := Nat.one_lt_two_pow (by omega)
    have hdouble : 2 ^ p = 2 * 2 ^ (p - 1) := by
      conv_lhs => rw [show p = p - 1 + 1 by omega, pow_succ']
    omega
  have hpow_mod (i : ℕ) : 2 ^ i ≡ R i [MOD M] := by
    calc
      2 ^ i = 2 ^ (i % p) * (2 ^ p) ^ (i / p) := by
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      _ ≡ 2 ^ (i % p) * 1 ^ (i / p) [MOD M] := (htwo_mod.pow _).mul_left _
      _ = R i := by simp [R]
  have hresidue (i : ℕ) : q ^ i % M = R (r * i) := by
    have h : q ^ i ≡ R (r * i) [MOD M] :=
      (hr.pow i).trans (by simpa only [← pow_mul] using hpow_mod (r * i))
    exact ((Nat.mod_modEq _ _).trans h).eq_of_lt_of_lt (Nat.mod_lt _ hM₀) (hR_lt _)
  have hperiod : q ^ p % M = 1 := by
    rw [hresidue]
    simp [R]
  -- Express the digit at index `j` by its incoming remainder.
  have hblock (j : ℕ) : B j = F (r * (j - 1)) := by
    have hL : ℓ * p = L := Nat.div_mul_cancel hdvd
    change (↑(((10 ^ L - 1) / M / 10 ^ (ℓ * (p - ((j - 1) % p + 1)))) % q : ℕ) : ℤ) = _
    rw [← hL, pow_mul, pow_mul]
    change (↑(((q ^ p - 1) / M / q ^ (p - ((j - 1) % p + 1))) % q : ℕ) : ℤ) = _
    rw [reciprocalBlock_eq_div hq hM₀ hperiod (Nat.mod_lt _ (by omega)), hresidue]
    simp only [F, R, Nat.mul_mod_mod]
  -- The outgoing remainder determines the carry when the incoming one is doubled.
  have hbalance (i : ℕ) : (M : ℤ) * F i + R (i + r) = (q : ℤ) * R i := by
    have hmod : (q * R i) % M = R (i + r) := by
      have h : q * R i ≡ R (i + r) [MOD M] := by
        calc
          q * R i ≡ 2 ^ r * 2 ^ i [MOD M] := hr.mul (hpow_mod i).symm
          _ = 2 ^ (i + r) := by rw [← pow_add, add_comm r]
          _ ≡ R (i + r) [MOD M] := hpow_mod _
      exact ((Nat.mod_modEq _ _).trans h).eq_of_lt_of_lt (Nat.mod_lt _ hM₀) (hR_lt _)
    dsimp only [F]
    exact_mod_cast (by rw [add_comm, ← hmod, Nat.mod_add_div] :
      M * (q * R i / M) + R (i + r) = q * R i)
  have hdouble (i : ℕ) : (R (i + 1) : ℤ) = 2 * R i -
      (if i % p + 1 = p then M else 0 : ℤ) := by
    have hi := Nat.mod_lt i (by omega : 0 < p)
    have hnext : (i + 1) % p = (i % p + 1) % p := (Nat.mod_add_mod i p 1).symm
    by_cases h : i % p + 1 = p
    · have hRp : 2 * R i = M + 1 := by
        change 2 * 2 ^ (i % p) = M + 1
        rw [← pow_succ', h, htwo]
      have hRnext : R (i + 1) = 1 := by simp [R, hnext, h]
      rw [hRnext, ite_eq_left h]
      have hRp' : (2 : ℤ) * R i = (M : ℤ) + 1 := by exact_mod_cast hRp
      omega
    · have hRnext : R (i + 1) = 2 * R i := by
        simp only [R, hnext, Nat.mod_eq_of_lt (show i % p + 1 < p by omega), pow_succ']
      rw [hRnext, ite_eq_right h, sub_zero]
      push_cast
      rfl
  have hstep (i : ℕ) (hi : i < p) :
      F (i + 1) = 2 * F i + (if i + 1 = p - r then 1 else 0) -
        (if i + 1 = p then (q : ℤ) else 0) := by
    have hcarry : ((i + r) % p + 1 = p) ↔ i + 1 = p - r := by
      by_cases h : i + r < p
      · rw [Nat.mod_eq_of_lt h]
        omega
      · rw [Nat.mod_eq_sub_mod (by omega : p ≤ i + r), Nat.mod_eq_of_lt (by omega)]
        omega
    have hleft := hdouble i
    rw [Nat.mod_eq_of_lt hi] at hleft
    have hright : (R (i + 1 + r) : ℤ) = 2 * R (i + r) -
        (if i + 1 = p - r then M else 0 : ℤ) := by
      simpa only [hcarry, show i + r + 1 = i + 1 + r by omega] using hdouble (i + r)
    apply mul_left_cancel₀ (show (M : ℤ) ≠ 0 by exact_mod_cast hM₀.ne')
    calc
      (M : ℤ) * F (i + 1) = (q : ℤ) * R (i + 1) - R (i + 1 + r) := by
        rw [← hbalance (i + 1), add_sub_cancel_right]
      _ = _ := by
        rw [hleft, hright]
        split_ifs <;> linear_combination -2 * hbalance i
  have hmul_inv (i : ℕ) : r * (s * i) ≡ i [MOD p] := by
    simpa only [mul_assoc, one_mul] using hs.mul_right i
  have hF_mod (i : ℕ) : F (i % p) = F i := by simp [F, R]
  have hreordered (i : ℕ) : B (i * s + 1) = F i := by
    rw [hblock, Nat.add_sub_cancel, mul_comm i s]
    exact congrArg (fun n : ℕ => (↑(q * 2 ^ n / M : ℕ) : ℤ)) (hmul_inv i)
  change (∀ k ∈ Finset.Icc 1 p, B (k * s + 1) = _) ∧
    (r = 1 → ∀ k ∈ Finset.Icc 1 p, B (k + 1) = _) ∧ ∑ k ∈ Finset.Icc 1 p, B k = (q : ℤ) - 1
  have hrec (k : ℕ) (hk : k ∈ Finset.Icc 1 p) :
      F k = if k = p then 2 * F (k - 1) - (q : ℤ)
        else if k = p - r then 2 * F (k - 1) + 1 else 2 * F (k - 1) := by
    obtain ⟨hk₁, hkp⟩ := Finset.mem_Icc.mp hk
    have h := hstep (k - 1) (by omega)
    rw [Nat.sub_add_cancel hk₁] at h
    split_ifs at h ⊢ <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hreordered, hreordered]
    simpa [q] using hrec k hk
  · intro hrOne k hk
    obtain ⟨hk₁, _⟩ := Finset.mem_Icc.mp hk
    have hnext : B (k + 1) = F k := by simp [hblock, hrOne]
    have hprev : B k = F (k - 1) := by simp [hblock, hrOne]
    rw [hnext, hprev]
    simpa [q, hrOne] using hrec k hk
  · -- Reindex by multiplication by `r`; its inverse is multiplication by `s`.
    have hsum : ∑ k ∈ Finset.Icc 1 p, B k = ∑ i ∈ Finset.range p, F i := by
      refine Finset.sum_bij' (fun k _ => (r * (k - 1)) % p) (fun i _ => (s * i) % p + 1)
        (fun _ _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega))) ?_ ?_ ?_ ?_
      · intro i _
        have hi := Nat.mod_lt (s * i) (show 0 < p by omega)
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro k hk
        obtain ⟨hk₁, hkp⟩ := Finset.mem_Icc.mp hk
        have hs' (i : ℕ) : s * (r * i) ≡ i [MOD p] := by
          rw [← mul_assoc, mul_comm s r]
          exact (by simpa only [one_mul] using hs.mul_right i)
        rw [Nat.mul_mod_mod, show s * (r * (k - 1)) % p = (k - 1) % p from hs' _,
          Nat.mod_eq_of_lt (by omega), Nat.sub_add_cancel hk₁]
      · intro i hi
        rw [Nat.add_sub_cancel, Nat.mul_mod_mod, show r * (s * i) % p = i % p from hmul_inv i,
          Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
      · intro k hk
        rw [hblock, hF_mod]
    have hcycle : ∑ i ∈ Finset.range p, F (i + 1) = ∑ i ∈ Finset.range p, F i := by
      have h := (Finset.sum_range_succ' F p).symm.trans (Finset.sum_range_succ F p)
      have hend : F p = F 0 := by simp [F, R]
      rw [hend] at h
      omega
    -- Over one cycle the two correction terms contribute once each.
    have hcorrection (a : ℕ) (ha : 1 ≤ a) (hap : a ≤ p) (c : ℤ) :
        ∑ i ∈ Finset.range p, (if i + 1 = a then c else 0) = c := by
      have hidx (i : ℕ) : i + 1 = a ↔ i = a - 1 := by omega
      simp only [hidx, Finset.sum_ite_eq', Finset.mem_range,
        ite_eq_left (show a - 1 < p by omega)]
    calc
      ∑ k ∈ Finset.Icc 1 p, B k = ∑ i ∈ Finset.range p, F i := hsum
      _ = (q : ℤ) - 1 := by
        have h := Finset.sum_congr rfl (fun i hi => hstep i (Finset.mem_range.mp hi))
        rw [hcycle, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          hcorrection (p - r) (by omega) (by omega), hcorrection p (by omega) le_rfl] at h
        omega

end MetaMathlibExt
