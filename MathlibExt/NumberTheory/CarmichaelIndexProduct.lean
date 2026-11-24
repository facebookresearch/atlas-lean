/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Equiv.Option
import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
public import MathlibExt.NumberTheory.CarmichaelIndex

/-!
# Product formula for the Carmichael index

The Carmichael index is a product of local counts of fixed residues modulo the prime powers
in the modulus.
-/

namespace MetaMathlibExt

private theorem carmichaelIndex_eq_prod.index_eq_card_fixed (n : ℕ) [NeZero n] :
    carmichaelIndex n = Nat.card {x : ZMod n // x ^ n = x} := by
  classical
  let s := (Finset.range n).filter fun a => a ^ n ≡ a [MOD n]
  let e : s ≃ {x : ZMod n // x ^ n = x} :=
    { toFun a := ⟨(a.val : ZMod n), by
        simpa only [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] using
          (Finset.mem_filter.mp a.property).2⟩
      invFun x := ⟨x.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.val.val_lt, by
        simpa only [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ZMod.natCast_zmod_val]
          using x.property⟩⟩
      left_inv a := Subtype.ext (ZMod.val_natCast_of_lt
        (Finset.mem_range.mp (Finset.mem_filter.mp a.property).1))
      right_inv x := Subtype.ext (ZMod.natCast_zmod_val x.val) }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

private theorem carmichaelIndex_eq_prod.eq_zero_of_fixed_of_not_isUnit {n p e : ℕ}
    (hn : 2 ≤ n) (hp : p.Prime) (he : 0 < e) {x : ZMod (p ^ e)}
    (hfix : x ^ n = x) (hx : ¬ IsUnit x) : x = 0 := by
  let : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdvd : p ∣ x.val := by
    by_contra h
    exact hx (ZMod.natCast_zmod_val x ▸
      (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).mpr h)
  obtain ⟨a, ha⟩ := hdvd
  -- A nonunit is a multiple of the prime, so it is nilpotent.
  have hnil : IsNilpotent x := ⟨e, by
    rw [← ZMod.natCast_zmod_val x, ha, Nat.cast_mul, mul_pow, ← Nat.cast_pow,
      ZMod.natCast_self, zero_mul]⟩
  have hu := (hnil.pow_of_pos (n := n - 1) (by omega)).isUnit_sub_one
  apply hu.mul_right_cancel
  rw [mul_sub, mul_one, mul_comm x, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n),
    hfix, sub_self, zero_mul]

private theorem carmichaelIndex_eq_prod.order_dvd_gcd_iff {n p e : ℕ}
    (hn : 2 ≤ n) (hp : p.Prime) (he : 0 < e) (hpe : p ^ e ∣ n)
    (u : (ZMod (p ^ e))ˣ) :
    orderOf u ∣ n - 1 ↔ orderOf u ∣ Nat.gcd (p - 1) (n / p ^ e - 1) := by
  let : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpn : p ∣ n := (dvd_pow_self p he.ne').trans hpe
  have hcop : (n - 1).Coprime p := by
    refine (hp.coprime_iff_not_dvd.mpr fun h => hp.not_dvd_one ?_).symm
    apply (Nat.dvd_add_iff_right h).mpr
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  -- The order divides the totient, whose prime-power part is coprime to n - 1.
  have hcard : orderOf u ∣ p ^ (e - 1) * (p - 1) := by
    rw [← Nat.totient_prime_pow hp he, ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have hpmod : p ≡ 1 [MOD p - 1] :=
    Nat.modEq_sub hp.pos
  have hnmod : n ≡ n / p ^ e [MOD p - 1] := by
    simpa only [Nat.mul_div_cancel' hpe, one_pow, one_mul] using
      (hpmod.pow e).mul_right (n / p ^ e)
  have hquot : 1 ≤ n / p ^ e :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hpe) (pow_pos hp.pos _)
  rw [Nat.gcd_comm (p - 1), ← (hnmod.sub (by omega : 1 ≤ n) hquot Nat.ModEq.rfl).gcd_eq]
  exact ⟨fun h => Nat.dvd_gcd h
    (((hcop.of_dvd_left h).pow_right (e - 1)).dvd_of_dvd_mul_left hcard),
    fun h => h.trans (Nat.gcd_dvd_left _ _)⟩

private theorem carmichaelIndex_eq_prod.card_fixed_prime_pow {n p e : ℕ}
    (hn : 2 ≤ n) (hp : p.Prime) (he : 0 < e) (hpe : p ^ e ∣ n) :
    Nat.card {x : ZMod (p ^ e) // x ^ n = x} =
      Nat.card {u : (ZMod (p ^ e))ˣ //
        orderOf u ∣ Nat.gcd (p - 1) (n / p ^ e - 1)} + 1 := by
  classical
  let : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow he.ne' hp.one_lt⟩
  have unit_fixed (u : (ZMod (p ^ e))ˣ) :
      (u : ZMod (p ^ e)) ^ n = u ↔ orderOf u ∣ Nat.gcd (p - 1) (n / p ^ e - 1) := by
    rw [← order_dvd_gcd_iff hn hp he hpe, orderOf_dvd_iff_pow_eq_one]
    have hpow : (u : ZMod (p ^ e)) ^ (n - 1) * u = (u : ZMod (p ^ e)) ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [← hpow, ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one]
    exact ⟨fun h => u.isUnit.mul_right_cancel (h.trans (one_mul _).symm),
      fun h => by rw [h, one_mul]⟩
  let z : {x : ZMod (p ^ e) // x ^ n = x} := ⟨0, zero_pow (by omega)⟩
  let f : {u : (ZMod (p ^ e))ˣ // orderOf u ∣ Nat.gcd (p - 1) (n / p ^ e - 1)} →
      {x : {x : ZMod (p ^ e) // x ^ n = x} // x ≠ z} :=
    fun u => ⟨⟨u.val, (unit_fixed u.val).mpr u.property⟩,
      fun h => u.val.isUnit.ne_zero (congrArg Subtype.val h)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (Units.ext (congrArg (fun x => x.val.val) hab))
    · intro x
      have hx : IsUnit x.val.val := by
        by_contra h
        exact x.property (Subtype.ext (eq_zero_of_fixed_of_not_isUnit hn hp he x.val.property h))
      obtain ⟨u, hu⟩ := hx
      exact ⟨⟨u, (unit_fixed u).mp (hu.symm ▸ x.val.property)⟩,
        Subtype.ext (Subtype.ext hu)⟩
  rw [← Nat.card_congr (Equiv.optionSubtypeNe z), Finite.card_option,
    ← Nat.card_congr (Equiv.ofBijective f hf)]

/-- **Product formula for the Carmichael index.** Let $n \ge 2$ and, for each prime $p$ dividing
$n$, let $p^{e_p}$ be the largest power of $p$ dividing $n$. Then the Carmichael index of $n$ is
$N(n) = \prod_p \bigl(N(n; p^{e_p}) + 1\bigr)$, the product running over the primes $p$ dividing
$n$, where $N(n; p^{e_p})$ is the number of units of $\mathbb{Z}/p^{e_p}\mathbb{Z}$ whose
multiplicative order divides $\gcd(p - 1, n/p^{e_p} - 1)$.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Theorem 1 (`integers-2024-A40-thm-1`). -/
public theorem carmichaelIndex_eq_prod (n : ℕ) (hn : 2 ≤ n) :
    carmichaelIndex n = ∏ p ∈ n.primeFactors,
      (Nat.card {u : (ZMod (p ^ n.factorization p))ˣ //
        orderOf u ∣ Nat.gcd (p - 1) (n / p ^ n.factorization p - 1)} + 1) := by
  classical
  let : NeZero n := ⟨by omega⟩
  let e := ZMod.equivPi n (NeZero.ne n)
  let fixedEquiv : {x : ZMod n // x ^ n = x} ≃
      ((p : n.primeFactors) → {x : ZMod (p ^ n.factorization p) // x ^ n = x}) :=
    (e.toEquiv.subtypeEquiv (q := fun x => ∀ p, (x p) ^ n = x p) fun x => by
      rw [← e.injective.eq_iff, map_pow]
      exact funext_iff).trans (Equiv.subtypePiEquivPi (p := fun _ x => x ^ n = x))
  rw [carmichaelIndex_eq_prod.index_eq_card_fixed, Nat.card_congr fixedEquiv,
    Nat.card_pi, ← Finset.prod_coe_sort n.primeFactors]
  apply Finset.prod_congr rfl
  intro p _
  obtain ⟨hprime, hdvd, hn0⟩ := Nat.mem_primeFactors.mp p.property
  exact carmichaelIndex_eq_prod.card_fixed_prime_pow hn hprime
    (hprime.factorization_pos_of_dvd hn0 hdvd) (Nat.ordProj_dvd n p)

end MetaMathlibExt
