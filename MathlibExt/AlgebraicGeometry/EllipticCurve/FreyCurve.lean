/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_FreyPackage_frey_isSemistableModel.lean`,
`Theorems/Thm_FreyCurve_isPeuRamifieeAt_odd_of_integralForm.lean`,
`Definitions/Def_FLTPrelim_FreyPackage.lean`,
`Definitions/Def_FLTPrelim_Modularity.lean`,
`Definitions/Def_WeierstrassCurve_PeuRamifiee.lean`
and
`P2M/Sol/S_FreyPackage_frey_isSemistableModel.lean`,
`P2M/Sol/S_FreyCurve_isPeuRamifieeAt_odd_of_integralForm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ModCases
import Mathlib.Tactic.Ring

@[expose] public section

open WeierstrassCurve

/-- A Weierstrass curve over `ℤ` is semistable when, at every prime dividing
its discriminant, the prime does not divide `c₄`. -/
def WeierstrassCurve.IsSemistableModel (W : WeierstrassCurve ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄

/-- A Weierstrass curve over `ℚ` is *peu ramifiée* at `ℓ` with respect to
`p` when `p` divides `padicValRat ℓ` of its discriminant: the multiplicity of `ℓ` in the
numerator minus that in the denominator. This integer is `0` when the discriminant is `0` and
when `ℓ` is `0` or `1`; it agrees with the `ℓ`-adic valuation only for prime `ℓ` and nonzero
discriminant. -/
def WeierstrassCurve.IsPeuRamifieeAt (W : WeierstrassCurve ℚ) (p ℓ : ℕ) : Prop :=
  (p : ℤ) ∣ padicValRat ℓ W.Δ

/-- The numerical data of a Frey curve: nonzero integers `a`, `b`, `c` and a
prime `p ≥ 5` with `a ^ p + b ^ p = c ^ p`, `gcd a b = 1`, `a ≡ 3 [ZMOD 4]`
and `b ≡ 0 [ZMOD 2]`. -/
structure FreyPackage where
  a : ℤ
  b : ℤ
  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0
  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p
  hFLT : a ^ p + b ^ p = c ^ p
  hgcdab : gcd a b = 1
  ha4 : (a : ZMod 4) = 3
  hb2 : (b : ZMod 2) = 0

namespace FreyPackage

/-- The Frey curve over `ℤ` attached to the data, with equation
`y² + xy = x³ + ((bᵖ - 1 - aᵖ) / 4) x² - (aᵖ bᵖ / 16) x`. -/
def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

/-- The Frey curve over `ℚ` attached to the data. -/
def freyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

private theorem hppos (P : FreyPackage) : 0 < P.p := lt_of_lt_of_le (by omega) P.hp5

private theorem hp0 (P : FreyPackage) : P.p ≠ 0 := P.hppos.ne'

private theorem gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p)
    (h : a ^ p + b ^ p = c ^ p) : gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp.ne', ← h]
    apply dvd_add <;> rw [Int.pow_dvd_pow_iff hp.ne']
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp.ne', h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp.ne']; exact gcd_dvd_right a c
    · rw [dvd_neg, Int.pow_dvd_pow_iff hp.ne']; exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar

private theorem hgcdac (P : FreyPackage) : gcd P.a P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos P.hFLT, P.hgcdab]

private theorem hgcdbc (P : FreyPackage) : gcd P.b P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos, gcd_comm, P.hgcdab]
  rw [add_comm]; exact P.hFLT

private theorem habc0 (P : FreyPackage) : P.a * P.b * P.c ≠ 0 :=
  mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0

private theorem freyCurveInt_map (P : FreyPackage) :
    (freyCurveInt P).map (algebraMap ℤ ℚ) = freyCurve P := by
  have two_dvd_b : 2 ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  ext
  · rfl
  · change (((P.b ^ P.p - 1 - P.a ^ P.p) / 4 : ℤ) : ℚ) = (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    rw [Rat.intCast_div]
    · norm_cast
    · rw [sub_sub]
      apply Int.dvd_sub
      · calc
          (4 : ℤ) = 2 ^ 2 := by norm_num
          _ ∣ P.b ^ 2 := pow_dvd_pow_of_dvd two_dvd_b 2
          _ ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1
        push_cast
        rw [P.ha4, show (3 : ZMod 4) = -1 from rfl, neg_one_pow_eq_ite, ite_eq_right]
        · norm_num
        · rw [Nat.Prime.even_iff P.pp]
          linarith [P.hp5]
  · rfl
  · change ((-(P.a ^ P.p) * (P.b ^ P.p) / 16 : ℤ) : ℚ) = -(P.a ^ P.p) * (P.b ^ P.p) / 16
    rw [Rat.intCast_div]
    · norm_cast
    · calc
        (16 : ℤ) = 2 ^ 4 := by norm_num
        _ ∣ P.b ^ 4 := pow_dvd_pow_of_dvd two_dvd_b 4
        _ ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
        _ ∣ _ := Int.dvd_mul_left _ _
  · rfl

private theorem freyCurve_Δ (P : FreyPackage) :
    P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

private def c₄Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

private theorem freyCurve_c₄_eq_intCast (P : FreyPackage) : P.freyCurve.c₄ = (c₄Int P : ℚ) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, freyCurve, c₄Int]
  push_cast
  field_simp
  ring

private theorem c₄Int_eq_sub (P : FreyPackage) :
    c₄Int P = (P.c ^ P.p) ^ 2 - (P.a * P.b) ^ P.p := by
  rw [c₄Int, ← P.hFLT, mul_pow]
  ring

private theorem not_dvd_c₄Int (P : FreyPackage) {q : ℤ} (hq : Prime q)
    (hqbad : q ∣ P.a * P.b * P.c) : ¬q ∣ c₄Int P := by
  intro hdvd
  rcases hq.dvd_mul.mp hqbad with hab | hc
  · rcases hq.dvd_mul.mp hab with ha | hb
    · have hqb : ¬q ∣ P.b := fun hb =>
        hq.not_isUnit (isUnit_of_dvd_one (P.hgcdab ▸ dvd_gcd ha hb))
      have hqap : q ∣ P.a ^ P.p := dvd_pow ha P.hp0
      rw [c₄Int, dvd_add_right (dvd_add (dvd_pow hqap two_ne_zero)
        (dvd_mul_of_dvd_left hqap _))] at hdvd
      exact hqb (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hdvd))
    · have hqa : ¬q ∣ P.a := fun ha =>
        hq.not_isUnit (isUnit_of_dvd_one (P.hgcdab ▸ dvd_gcd ha hb))
      have hqbp : q ∣ P.b ^ P.p := dvd_pow hb P.hp0
      rw [c₄Int, add_assoc, dvd_add_left (dvd_add (dvd_mul_of_dvd_right hqbp _)
        (dvd_pow hqbp two_ne_zero))] at hdvd
      exact hqa (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hdvd))
  · have hqa : ¬q ∣ P.a := fun ha =>
      hq.not_isUnit (isUnit_of_dvd_one (P.hgcdac ▸ dvd_gcd ha hc))
    have hqb : ¬q ∣ P.b := fun hb =>
      hq.not_isUnit (isUnit_of_dvd_one (P.hgcdbc ▸ dvd_gcd hb hc))
    rw [c₄Int_eq_sub, dvd_sub_right (dvd_pow (dvd_pow hc P.hp0) two_ne_zero)] at hdvd
    rcases hq.dvd_mul.mp (hq.dvd_of_dvd_pow hdvd) with h | h
    exacts [hqa h, hqb h]

private theorem freyCurveInt_c₄ (P : FreyPackage) : (freyCurveInt P).c₄ = c₄Int P := by
  have h : (algebraMap ℤ ℚ) (freyCurveInt P).c₄ = ((c₄Int P : ℤ) : ℚ) := by
    rw [← map_c₄, freyCurveInt_map, ← freyCurve_c₄_eq_intCast]
  rw [eq_intCast] at h
  exact_mod_cast h

private theorem freyCurveInt_Δ_mul (P : FreyPackage) :
    (freyCurveInt P).Δ * 2 ^ 8 = (P.a * P.b * P.c) ^ (2 * P.p) := by
  have hΔ : (algebraMap ℤ ℚ) (freyCurveInt P).Δ
      = (P.a * P.b * P.c : ℚ) ^ (2 * P.p) / 2 ^ 8 := by
    rw [← map_Δ, freyCurveInt_map, freyCurve_Δ]
  rw [eq_intCast] at hΔ
  have h : ((((freyCurveInt P).Δ * 2 ^ 8 : ℤ)) : ℚ)
      = (((P.a * P.b * P.c) ^ (2 * P.p) : ℤ) : ℚ) := by
    push_cast
    rw [hΔ]
    field_simp
    norm_num
  exact_mod_cast h

private theorem dvd_abc_of_dvd_freyCurveInt_Δ (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hdvd : (q : ℤ) ∣ (freyCurveInt P).Δ) : (q : ℤ) ∣ P.a * P.b * P.c := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  exact hqZ.dvd_of_dvd_pow (n := 2 * P.p)
    (freyCurveInt_Δ_mul P ▸ hdvd.mul_right (2 ^ 8))

private theorem freyCurveInt_Δ_ne_zero (P : FreyPackage) :
    (freyCurveInt P).Δ ≠ 0 := by
  intro h
  have hmul := freyCurveInt_Δ_mul P
  rw [h, zero_mul] at hmul
  exact pow_ne_zero _ P.habc0 hmul.symm

private theorem padicValInt_freyCurveInt_Δ (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q (freyCurveInt P).Δ =
      2 * P.p * padicValInt q (P.a * P.b * P.c) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq28 : ¬ (q : ℤ) ∣ 2 ^ 8 := by
    intro h
    have h2 : (q : ℤ) ∣ 2 := hqZ.dvd_of_dvd_pow h
    have h2' : q ∣ 2 := by exact_mod_cast h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2')
  have hmul : padicValInt q ((freyCurveInt P).Δ * 2 ^ 8) =
      padicValInt q (freyCurveInt P).Δ := by
    rw [padicValInt.mul (freyCurveInt_Δ_ne_zero P) (by norm_num),
      padicValInt.eq_zero_of_not_dvd hq28, add_zero]
  rw [← hmul, freyCurveInt_Δ_mul]
  simp only [padicValInt, Int.natAbs_pow]
  exact padicValNat.pow _ _

private theorem p_dvd_padicValInt_freyCurveInt_discr (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    P.p ∣ padicValInt q (freyCurveInt P).Δ :=
  ⟨2 * padicValInt q (P.a * P.b * P.c), by
    rw [padicValInt_freyCurveInt_Δ P hq hq2]; ring⟩

private theorem freyCurve_Δ_eq_cast (P : FreyPackage) :
    P.freyCurve.Δ = (P.freyCurveInt.Δ : ℚ) := by
  rw [← freyCurveInt_map, WeierstrassCurve.map_Δ]
  rfl

private theorem p_dvd_padicValRat_freyCurve_discr (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    (P.p : ℤ) ∣ padicValRat q P.freyCurve.Δ := by
  rw [freyCurve_Δ_eq_cast, padicValRat.of_int]
  exact Int.natCast_dvd_natCast.mpr
    (p_dvd_padicValInt_freyCurveInt_discr P hq hq2)

/-- The Frey curve over `ℤ` is a semistable model: at every prime dividing
its discriminant, the prime does not divide `c₄`. -/
public theorem frey_isSemistableModel (P : FreyPackage) :
    P.freyCurveInt.IsSemistableModel := by
  intro q hq hdvdΔ
  rw [freyCurveInt_c₄]
  exact not_dvd_c₄Int P (Nat.prime_iff_prime_int.mp hq)
    (dvd_abc_of_dvd_freyCurveInt_Δ P hq hdvdΔ)

end FreyPackage

namespace FreyCurve

/-- For every odd prime `q`, the rational Frey curve attached to a Frey
package is peu ramifiée at `q` with respect to its exponent `p`: `p`
divides the `q`-adic valuation of the discriminant, since over `ℤ` that
valuation is `2 * p` times the valuation of `a * b * c`. -/
public theorem isPeuRamifieeAt_odd_of_integralForm (P : FreyPackage)
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    P.freyCurve.IsPeuRamifieeAt P.p q :=
  FreyPackage.p_dvd_padicValRat_freyCurve_discr P Fact.out hq2

end FreyCurve
