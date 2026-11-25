/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MathlibExt.NumberTheory.Wolstenholme

open scoped BigOperators

/-!
# Wolstenholme's theorem

For a prime `p ≥ 5`, the sum of the reciprocals of `1, …, p - 1` vanishes in
`ZMod (p ^ 2)`.

## Proof idea

Pair each `k` in the lower half with `p - k`. Since `(p : ZMod (p ^ 2)) ^ 2 = 0`,
expanding `(p - k)⁻¹` gives `-k⁻¹ - p * (k⁻¹) ^ 2`, so the paired harmonic sum
equals `-p` times a sum of inverse squares. Reducing that sum modulo `p` (via
`ZMod.castHom`), pairing squares `k⁻² = (p - k)⁻²`, and reindexing inverses to
squares shows it equals `(2 * 6)⁻¹` times `∑ k ^ 2 = 0` over `ZMod p` (using
`∑ k ^ 2 = (p - 1) * p * (2 * p - 1) / 6` and `p ∤ 6`), hence is divisible by
`p` and the total is `0` in `ZMod (p ^ 2)`.

## References

The statement is the first reciprocal congruence in Zubeyir Cinkir, "Beyond
Wolstenholme's Theorem", arXiv:2312.10667v1, `SumsinModp.tex` lines 145--154,
which states it modulo `p ^ 2` for primes `p ≥ 5` and cites J. Wolstenholme,
"On certain properties of prime numbers", Quarterly Journal of Mathematics 5
(1862), 35--39.
-/

private theorem eq_two_mul_half_add_one (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    p = 2 * ((p - 1) / 2) + 1 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  omega

private theorem coprime_of_mem_Ico (p k : ℕ) (hp : p.Prime)
    (hk : k ∈ Finset.Ico 1 p) :
    k.Coprime (p ^ 2) := by
  rw [Finset.mem_Ico] at hk
  have hndvd : ¬ p ∣ k := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have h1 : k.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd).symm
  exact h1.pow_right 2

private theorem isUnit_of_mem_Ico (p k : ℕ) (hp : p.Prime)
    (hk : k ∈ Finset.Ico 1 p) :
    IsUnit ((k : ZMod (p ^ 2))) :=
  (ZMod.isUnit_iff_coprime k (p ^ 2)).mpr (coprime_of_mem_Ico p k hp hk)

private theorem mem_Ico_sub (p k : ℕ) (h5 : 5 ≤ p)
    (hk : k ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) : p - k ∈ Finset.Ico 1 p := by
  rw [Finset.mem_Ico] at hk ⊢
  omega

private theorem isUnit_sub (p k : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hk : k ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) :
    IsUnit (((p - k : ℕ) : ZMod (p ^ 2))) :=
  isUnit_of_mem_Ico p (p - k) hp (mem_Ico_sub p k h5 hk)

private theorem mul_inv_cancel_of_mem_Ico (p k : ℕ) (hp : p.Prime)
    (hk : k ∈ Finset.Ico 1 p) :
    (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 := by
  have hcop : Nat.Coprime k (p ^ 2) := coprime_of_mem_Ico p k hp hk
  rw [Finset.mem_Ico] at hk
  have hlt : k < p ^ 2 := lt_of_lt_of_le hk.2 (Nat.le_self_pow (by omega) p)
  have hval : (k : ZMod (p ^ 2)).val = k := ZMod.val_natCast_of_lt hlt
  have hgcd : Nat.gcd k (p ^ 2) = 1 := hcop
  rw [ZMod.mul_inv_eq_gcd, hval, hgcd, Nat.cast_one]

private theorem pair_inv (p k : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hk : k ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) :
    (((p - k : ℕ) : ZMod (p ^ 2))⁻¹
      = -((k : ZMod (p ^ 2))⁻¹)
        - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
  have hkIco : k ∈ Finset.Ico 1 p := by
    rw [Finset.mem_Ico] at hk ⊢
    omega
  have hkp : k < p := (Finset.mem_Ico.mp hkIco).2
  have hk1 : (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 :=
    mul_inv_cancel_of_mem_Ico p k hp hkIco
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    have h0 : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := ZMod.natCast_self _
    rwa [Nat.cast_pow] at h0
  have hcast : ((p - k : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - k := by
    rw [Nat.cast_sub hkp.le]
  have hRHS : ((p - k : ℕ) : ZMod (p ^ 2))
      * (-((k : ZMod (p ^ 2))⁻¹)
        - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) = 1 := by
    rw [hcast]
    linear_combination (1 + (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) * hk1
      - ((k : ZMod (p ^ 2))⁻¹) ^ 2 * hp2
  have hLHS : ((p - k : ℕ) : ZMod (p ^ 2))
      * (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) = 1 :=
    mul_inv_cancel_of_mem_Ico p (p - k) hp (mem_Ico_sub p k h5 hk)
  have hEq : ((p - k : ℕ) : ZMod (p ^ 2)) * (((p - k : ℕ) : ZMod (p ^ 2))⁻¹)
      = ((p - k : ℕ) : ZMod (p ^ 2))
        * (-((k : ZMod (p ^ 2))⁻¹)
          - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
    rw [hLHS, hRHS]
  exact (isUnit_sub p k hp h5 hk).mul_left_cancel hEq

private theorem sum_Ico_pair (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (M : Type*)
    [AddCommMonoid M] (f : ℕ → M) :
    ∑ k ∈ Finset.Ico 1 p, f k
      = ∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), (f k + f (p - k)) := by
  have hpm : p = 2 * ((p - 1) / 2) + 1 := eq_two_mul_half_add_one p hp h5
  have hsplit := Finset.sum_Ico_consecutive f (show 1 ≤ (p - 1) / 2 + 1 by omega)
    (show (p - 1) / 2 + 1 ≤ p by omega)
  have hreindex : ∑ k ∈ Finset.Ico ((p - 1) / 2 + 1) p, f k
      = ∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), f (p - k) := by
    apply Finset.sum_bij (fun k _ => p - k)
    · intro k hk
      rw [Finset.mem_Ico] at hk ⊢
      omega
    · intro k1 hk1 k2 hk2 h
      rw [Finset.mem_Ico] at hk1 hk2
      omega
    · intro j hj
      rw [Finset.mem_Ico] at hj
      refine ⟨p - j, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro k hk
      rw [Finset.mem_Ico] at hk
      have hppk : p - (p - k) = k := by omega
      simp only [hppk]
  rw [← hsplit, hreindex, ← Finset.sum_add_distrib]

private theorem sum_inv_eq_neg_mul_sum_sq (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 2))⁻¹)
      = -(p : ZMod (p ^ 2))
        * ∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((k : ZMod (p ^ 2))⁻¹) ^ 2 := by
  rw [sum_Ico_pair p hp h5 (ZMod (p ^ 2)) (fun k => ((k : ZMod (p ^ 2))⁻¹))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pair_inv p k hp h5 hk]
  ring

private theorem map_inv_castHom (p k : ℕ) (hp : p.Prime) (hk : k ∈ Finset.Ico 1 p)
    (φ : ZMod (p ^ 2) →+* ZMod p)
    (hcast : φ (k : ZMod (p ^ 2)) = (k : ZMod p)) :
    φ ((k : ZMod (p ^ 2))⁻¹) = ((k : ZMod p))⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hk1 := mul_inv_cancel_of_mem_Ico p k hp hk
  have h := congrArg φ hk1
  rw [map_mul, map_one, hcast] at h
  exact eq_inv_of_mul_eq_one_right h

private theorem castHom_sum_sq (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (φ : ZMod (p ^ 2) →+* ZMod p)
    (hcast : ∀ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
      φ (k : ZMod (p ^ 2)) = (k : ZMod p)) :
    φ (∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2)
      = ∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), ((k : ZMod p)⁻¹) ^ 2 := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1p : k ∈ Finset.Ico 1 p := by
    have h := Finset.mem_Ico.mp hk
    rw [Finset.mem_Ico]
    omega
  rw [map_pow, map_inv_castHom p k hp hk1p φ (hcast k hk)]

private theorem neg_cast_sub_mod (p k : ℕ) (hk : k ∈ Finset.Ico 1 p) :
    ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
  have hkp : k ≤ p := (Finset.mem_Ico.mp hk).2.le
  rw [Nat.cast_sub hkp, ZMod.natCast_self, zero_sub]

private theorem inv_sq_pair_mod (p k : ℕ) (hp : p.Prime)
    (hk : k ∈ Finset.Ico 1 p) :
    (((p - k : ℕ) : ZMod p)⁻¹) ^ 2 = ((k : ZMod p)⁻¹) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [neg_cast_sub_mod p k hk, inv_neg, neg_sq]

private theorem sum_sq_halves (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2
      = 2 * ∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((k : ZMod p)⁻¹) ^ 2 := by
  rw [sum_Ico_pair p hp h5 (ZMod p) (fun k => ((k : ZMod p)⁻¹) ^ 2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkIco : k ∈ Finset.Ico 1 p := by
    have h := Finset.mem_Ico.mp hk
    rw [Finset.mem_Ico]
    omega
  rw [inv_sq_pair_mod p k hp hkIco]
  ring

private theorem mem_Ico_inv_val (p k : ℕ) (hp : p.Prime)
    (hk : k ∈ Finset.Ico 1 p) :
    (((k : ZMod p)⁻¹).val) ∈ Finset.Ico 1 p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  rw [Finset.mem_Ico] at hk ⊢
  have hkne : (k : ZMod p) ≠ 0 := by
    intro h0
    have hvalk := ZMod.val_natCast_of_lt hk.2
    have hcongr := congrArg ZMod.val h0
    rw [hvalk] at hcongr
    have h0val := ZMod.val_natCast_of_lt hp.pos
    rw [Nat.cast_zero] at h0val
    rw [h0val] at hcongr
    omega
  have hinv : (k : ZMod p)⁻¹ ≠ 0 := inv_ne_zero hkne
  have hval : (((k : ZMod p)⁻¹).val) ≠ 0 := by
    intro h0
    have hc := ZMod.natCast_zmod_val ((k : ZMod p)⁻¹)
    rw [h0, Nat.cast_zero] at hc
    exact hinv hc.symm
  exact ⟨by omega, ZMod.val_lt _⟩

private theorem sum_inv_sq_eq_sum_sq (p : ℕ) (hp : p.Prime) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2
      = ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  refine Finset.sum_bij (s := Finset.Ico 1 p) (t := Finset.Ico 1 p)
    (f := fun k => ((k : ZMod p)⁻¹) ^ 2) (g := fun k => (k : ZMod p) ^ 2)
    (i := fun k _ => (((k : ZMod p)⁻¹).val)) ?_ ?_ ?_ ?_
  · intro k hk
    exact mem_Ico_inv_val p k hp hk
  · intro a ha b hb h
    rw [Finset.mem_Ico] at ha hb
    have hcast := congrArg (fun n => ((n : ℕ) : ZMod p)) h
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    have hinv := congrArg Inv.inv hcast
    rw [inv_inv, inv_inv] at hinv
    have hval := congrArg ZMod.val hinv
    rw [ZMod.val_natCast_of_lt ha.2, ZMod.val_natCast_of_lt hb.2] at hval
    exact hval
  · intro j hj
    refine ⟨(((j : ZMod p)⁻¹).val), mem_Ico_inv_val p j hp hj, ?_⟩
    have hj2 := (Finset.mem_Ico.mp hj).2
    have hcast : ((((j : ZMod p)⁻¹).val : ℕ) : ZMod p) = (j : ZMod p)⁻¹ :=
      ZMod.natCast_zmod_val _
    have hinv : ((((j : ZMod p)⁻¹).val : ℕ) : ZMod p)⁻¹ = (j : ZMod p) := by
      rw [hcast, inv_inv]
    have hval := congrArg ZMod.val hinv
    rw [ZMod.val_natCast_of_lt hj2] at hval
    exact hval
  · intro k hk
    have hcast : ((((k : ZMod p)⁻¹).val : ℕ) : ZMod p) = (k : ZMod p)⁻¹ :=
      ZMod.natCast_zmod_val _
    rw [hcast]

private theorem six_mul_sum_Ico_sq (n : ℕ) :
    6 * ∑ k ∈ Finset.Ico 1 (n + 1), k ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
    linear_combination ih

private theorem sum_sq_eq_zero (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 ≤ p := hp.pos
  have hndvd6 : ¬ p ∣ 6 := by
    intro h
    have h23 : p ∣ 2 * 3 := by simpa using h
    have h2or3 := (Nat.Prime.dvd_mul hp).mp h23
    rcases h2or3 with h2 | h3
    · have hle := Nat.le_of_dvd (by norm_num) h2
      omega
    · have hle := Nat.le_of_dvd (by norm_num) h3
      omega
  have hcop : Nat.Coprime 6 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd6).symm
  have h6unit : IsUnit (6 : ZMod p) := by
    have h := (ZMod.isUnit_iff_coprime 6 p).mpr hcop
    simpa using h
  have hnat := six_mul_sum_Ico_sq (p - 1)
  rw [Nat.sub_add_cancel hp1] at hnat
  have hcast := congrArg (fun n => ((n : ℕ) : ZMod p)) hnat
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, ZMod.natCast_self,
    mul_zero, zero_mul, Nat.cast_ofNat] at hcast
  exact h6unit.mul_left_cancel (by rw [hcast, mul_zero])

private theorem sum_inv_sq_half_eq_zero (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  have hfull : ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 = 0 := by
    rw [sum_inv_sq_eq_sum_sq p hp, sum_sq_eq_zero p hp h5]
  have hhalves := sum_sq_halves p hp h5
  rw [hfull] at hhalves
  have hndvd2 : ¬ p ∣ 2 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    omega
  have hcop2 : Nat.Coprime 2 p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd2).symm
  have h2unit : IsUnit (2 : ZMod p) := by
    have h := (ZMod.isUnit_iff_coprime 2 p).mpr hcop2
    simpa using h
  have heq : (2 : ZMod p)
      * (∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), ((k : ZMod p)⁻¹) ^ 2)
      = 2 * 0 := by
    rw [mul_zero]
    exact hhalves.symm
  exact h2unit.mul_left_cancel heq

private theorem mul_sum_sq_eq_zero (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ZMod (p ^ 2))
      * ∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2
      = 0 := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have : NeZero (p ^ 2) := ⟨(pow_pos hp.pos 2).ne'⟩
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p (by omega)
  have hcast : ∀ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
      ZMod.castHom hdvd (ZMod p) (k : ZMod (p ^ 2)) = (k : ZMod p) :=
    fun k _ => map_natCast (ZMod.castHom hdvd (ZMod p)) k
  have hφS : ZMod.castHom hdvd (ZMod p)
      (∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2)
      = 0 := by
    rw [castHom_sum_sq p hp h5 (ZMod.castHom hdvd (ZMod p)) hcast,
      sum_inv_sq_half_eq_zero p hp h5]
  set S := ∑ k ∈ Finset.Ico 1 ((p - 1) / 2 + 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2
  have hSval : ((S.val : ℕ) : ZMod (p ^ 2)) = S := ZMod.natCast_zmod_val S
  have hφSval : ZMod.castHom hdvd (ZMod p) S = ((S.val : ℕ) : ZMod p) := by
    have h := map_natCast (ZMod.castHom hdvd (ZMod p)) S.val
    rwa [hSval] at h
  have hzero : ((S.val : ℕ) : ZMod p) = 0 := by rw [← hφSval, hφS]
  have hdvdS : p ∣ S.val := (ZMod.natCast_eq_zero_iff S.val p).mp hzero
  obtain ⟨t, ht⟩ := hdvdS
  have h0 : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := ZMod.natCast_self _
  have hSmul : (p : ZMod (p ^ 2)) * S = ((p * S.val : ℕ) : ZMod (p ^ 2)) := by
    rw [Nat.cast_mul, hSval]
  rw [hSmul, ht]
  have hring : p * (p * t) = p ^ 2 * t := by ring
  rw [hring, Nat.cast_mul, h0, zero_mul]

/-- **Wolstenholme's theorem.** If $p \ge 5$ is prime, then $\sum_{k=1}^{p-1} k^{-1} = 0$ in
$\mathbb{Z}/p^2\mathbb{Z}$, where $k^{-1}$ is the inverse of $k$ modulo $p^2$. -/
theorem wolstenholme (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 2))⁻¹) = 0 := by
  rw [sum_inv_eq_neg_mul_sum_sq p hp h5, neg_mul,
    mul_sum_sq_eq_zero p hp h5, neg_zero]

end MathlibExt.NumberTheory.Wolstenholme
