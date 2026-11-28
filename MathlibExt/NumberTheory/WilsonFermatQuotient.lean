/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FermatQuotient

import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.Ring

/-!
# Wilson's theorem modulo the square of an odd prime

Levaillant's formula in terms of Fermat quotients follows by expanding products in `ZMod (p ^ 2)`:
all terms containing two factors of `p` vanish.
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonFaulhaberWanted

private theorem coprime_of_mem {p k : ℕ} (hp : p.Prime)
    (h : k ∈ Finset.Icc 1 (p - 1)) : IsCoprime (k : ℤ) (p : ℤ) := by
  rw [Finset.mem_Icc] at h
  have hlt : k < p := by have := hp.pos; omega
  exact Nat.isCoprime_iff_coprime.mpr
    ((hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt h.1 hlt)).symm)

private theorem prod_one_add_mul_of_square_zero {R ι : Type*} [CommRing R]
    (x : R) (hx : x * x = 0) (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 + x * f i) = 1 + x * ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, ih]
    calc
      _ = 1 + x * (f i + ∑ j ∈ s, f j) + (x * x) * (f i * ∑ j ∈ s, f j) := by ring
      _ = _ := by rw [hx, zero_mul, add_zero]

/-- **Wilson's theorem modulo $p^2$.** Let $p$ be an odd prime and, for $1 \le k \le p - 1$, let
$q_p(k)$ be the Fermat quotient of $k$, the integer with $k^{p-1} = 1 + p\, q_p(k)$. Then
$$
(p - 1)! \equiv -1 + p \sum_{k=1}^{p-1} q_p(k) \pmod{p^2}.
$$

Source: Claire Levaillant, "Wilson's Theorem Modulo
`p^2` Derived from Faulhaber Polynomials", Theorem 1. -/
theorem wilson_mod_prime_sq (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (Nat.factorial (p - 1) : ZMod (p ^ 2)) =
      -1 + (p : ZMod (p ^ 2)) *
        ∑ k ∈ (Finset.Icc 1 (p - 1)).attach,
          ((Int.fermatQuotient p hp (k.1 : ℤ)
            (by exact coprime_of_mem hp k.2) : ℤ) : ZMod (p ^ 2)) := by
  let x : ZMod (p ^ 2) := p
  have hx : x * x = 0 := by
    calc
      x * x = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by simp only [x, pow_two, Nat.cast_mul]
      _ = 0 := ZMod.natCast_self _
  let s := Finset.Icc 1 (p - 1)
  let q (k : s) : ZMod (p ^ 2) := Int.fermatQuotient p hp (k.1 : ℤ) (coprime_of_mem hp k.2)
  have hq (k : s) : (k.1 : ZMod (p ^ 2)) ^ (p - 1) = 1 + x * q k := by
    have h := congrArg (fun n : ℤ => (n : ZMod (p ^ 2)))
      (Int.natCast_mul_fermatQuotient p hp (k.1 : ℤ) (coprime_of_mem hp k.2))
    have h' : x * q k = (k.1 : ZMod (p ^ 2)) ^ (p - 1) - 1 := by
      simpa only [x, q, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one]
        using h
    rw [h']
    ring
  have hfacprod : ∏ k ∈ s.attach, (k.1 : ZMod (p ^ 2)) =
      (Nat.factorial (p - 1) : ZMod (p ^ 2)) := by
    have hs : s = Ico 1 (p - 1).succ := by
      ext k
      simp [s]
    rw [Finset.prod_attach, ← Finset.prod_natCast, hs, Finset.prod_Ico_id_eq_factorial]
  have hprod : (Nat.factorial (p - 1) : ZMod (p ^ 2)) ^ (p - 1) =
      1 + x * ∑ k ∈ s.attach, q k := by
    rw [← hfacprod, ← Finset.prod_pow]
    simp_rw [hq]
    exact prod_one_add_mul_of_square_zero x hx s.attach q
  -- Ordinary Wilson gives the integral lift `(p - 1)! + 1 = p * w`.
  obtain ⟨w, hw⟩ : (p : ℤ) ∣ (Nat.factorial (p - 1) : ℤ) + 1 := by
    let : Fact p.Prime := ⟨hp⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp [ZMod.wilsons_lemma p]
  have hw' : (Nat.factorial (p - 1) : ZMod (p ^ 2)) + 1 = x * (w : ZMod (p ^ 2)) := by
    simpa only [x, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one] using
      congrArg (fun n : ℤ => (n : ZMod (p ^ 2))) hw
  have hfac : (Nat.factorial (p - 1) : ZMod (p ^ 2)) = -1 + x * (w : ZMod (p ^ 2)) := by
    rw [← hw']
    ring
  -- The even exponent removes the sign; the linear coefficient `-(p - 1)` acts as `1` on `p * w`.
  have hpow : (Nat.factorial (p - 1) : ZMod (p ^ 2)) ^ (p - 1) =
      1 + x * (w : ZMod (p ^ 2)) := by
    let y := (w : ZMod (p ^ 2))
    have hneg : (Nat.factorial (p - 1) : ZMod (p ^ 2)) = -(1 + x * (-y)) := by
      rw [hfac]
      dsimp [y]
      ring
    have hlinear := prod_one_add_mul_of_square_zero x hx (Finset.range (p - 1)) (fun _ => -y)
    simp only [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlinear
    rw [hneg, (hp.even_sub_one hp2).neg_pow, hlinear, Nat.cast_sub hp.one_le, Nat.cast_one]
    calc
      _ = 1 + x * y - (x * x) * y := by change 1 + x * ((x - 1) * -y) = _; ring
      _ = _ := by rw [hx, zero_mul, sub_zero]
  have hsum := add_left_cancel (hpow.symm.trans hprod)
  change (Nat.factorial (p - 1) : ZMod (p ^ 2)) = -1 + x * ∑ k ∈ s.attach, q k
  rw [hfac, hsum]

end MathlibExt.NumberTheory.WilsonFaulhaberWanted

end
