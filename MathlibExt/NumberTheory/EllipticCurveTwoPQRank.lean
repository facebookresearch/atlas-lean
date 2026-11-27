/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.Rat.Squarefree
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rank one cases for the elliptic curve `y² = x³ - 2pqx`

We prove that the rational point group has rank one when its rank is odd and the prime pair
satisfies the specified residue and Legendre-symbol conditions. The proof counts square classes
using the curves `y² = x³ - 2pqx` and `y² = x³ + 8pqx`, then applies height descent.
-/

namespace MetaMathlibExt.finrank_point_two_mul_mul_eq_one

private def OnCurve (B x y : ℚ) : Prop := y ^ 2 = x * (x ^ 2 + B)

private lemma val_add {p : ℕ} [Fact p.Prime] {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : padicValRat p x < padicValRat p y) :
    x + y ≠ 0 ∧ padicValRat p (x + y) = padicValRat p x := by
  have hne : x + y ≠ 0 := by
    intro he
    have hy' : y = -x := by linarith
    simp [hy'] at h
  exact ⟨hne, padicValRat.add_eq_of_lt hne hx hy h⟩

private lemma even_val_away {l : ℕ} [Fact l.Prime] {B : ℤ} {x y : ℚ}
    (hB : ¬(l : ℤ) ∣ B) (hx : x ≠ 0) (hxy : OnCurve B x y) :
    Even (padicValRat l x) := by
  have hB0 : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (fun h ↦ hB (h ▸ dvd_zero _))
  have hvB : padicValRat l (B : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hB]
    simp
  have hvx : padicValRat l (x ^ 2) = 2 * padicValRat l x := by
    rw [padicValRat.pow]
    norm_num
  have he := congrArg (padicValRat l) hxy
  change padicValRat l (y ^ 2) = padicValRat l (x * (x ^ 2 + B)) at he
  rcases lt_trichotomy (padicValRat l x) 0 with hn | hz | hp
  · obtain ⟨hne, hval⟩ :=
      val_add (pow_ne_zero 2 hx) hB0 (by rw [hvx, hvB]; omega)
    rw [padicValRat.pow, padicValRat.mul hx hne, hval, hvx] at he
    exact ⟨padicValRat l y - padicValRat l x, by omega⟩
  · simp [hz]
  · obtain ⟨hne, hval⟩ := val_add hB0 (pow_ne_zero 2 hx) (by rw [hvx, hvB]; omega)
    rw [add_comm] at hne hval
    rw [padicValRat.pow, padicValRat.mul hx hne, hval, hvB] at he
    exact ⟨padicValRat l y, by omega⟩

private lemma squarefree_part (x : ℚ) :
    ∃ (d : ℤ) (s : ℚ), Squarefree d ∧ x = (d : ℚ) * s ^ 2 := by
  let n : ℤ := x.num * x.den
  obtain ⟨b, a, hab, ha⟩ := exists_sq_mul_squarefree n.natAbs
  have hab' : (n.natAbs : ℤ) = (a : ℤ) * (b : ℤ) ^ 2 := by
    exact_mod_cast (mul_comm (b ^ 2) a ▸ hab.symm)
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hnum : (x.num : ℚ) = x * (x.den : ℚ) := (div_eq_iff hd).mp x.num_div_den
  have hrat : x = (n : ℚ) / (x.den : ℚ) ^ 2 := by
    dsimp [n]
    push_cast
    rw [hnum]
    field_simp
  rcases Int.natAbs_eq n with h | h
  · refine ⟨a, b / (x.den : ℚ), Int.squarefree_natCast.mpr ha, hrat.trans ?_⟩
    rw [h, hab']
    push_cast
    ring
  · refine ⟨-(a : ℤ), b / (x.den : ℚ), ?_, hrat.trans ?_⟩
    · simpa [← Int.squarefree_natAbs] using ha
    · rw [h, hab']
      push_cast
      ring

private lemma val_squarefree {l : ℕ} [Fact l.Prime] {d : ℤ} (hd : Squarefree d) :
    padicValRat l (d : ℚ) = if (l : ℤ) ∣ d then 1 else 0 := by
  rw [padicValRat.of_int]
  split_ifs with hl
  · have h1 : 1 ≤ padicValInt l d := by
      simpa [hd.ne_zero] using (padicValInt_dvd_iff (p := l) 1 d).mp (by simpa using hl)
    have h2 : ¬2 ≤ padicValInt l d := by
      intro hh
      have hs := (padicValInt_dvd_iff (p := l) 2 d).mpr (.inr hh)
      exact (Int.squarefree_iff_prime_sq_not_dvd.mp hd l Fact.out) hs
    omega
  · simp [padicValInt.eq_zero_of_not_dvd hl]

private lemma part_dvd {B d : ℤ} {x y s : ℚ} (hx : x ≠ 0)
    (hxy : OnCurve B x y) (hd : Squarefree d) (hxs : x = (d : ℚ) * s ^ 2) : d ∣ B := by
  rw [← Int.natAbs_dvd_natAbs]
  by_cases hB : B = 0
  · simp [hB]
  apply (Nat.factorization_le_iff_dvd (by simpa using hd.ne_zero) (by simpa using hB)).mp
  intro l
  by_cases hl : l.Prime
  · let : Fact l.Prime := ⟨hl⟩
    have hd' := Int.squarefree_natAbs.mpr hd
    by_cases hld : l ∣ d.natAbs
    · rw [Nat.factorization_eq_one_of_squarefree hd' hl hld]
      have hld' : (l : ℤ) ∣ d := Int.natCast_dvd.mpr hld
      have hlB : (l : ℤ) ∣ B := by
        by_contra hn
        obtain ⟨z, hz⟩ := even_val_away hn hx hxy
        have hs : s ≠ 0 := by rintro rfl; exact hx (by simpa using hxs)
        rw [hxs, padicValRat.mul (Int.cast_ne_zero.mpr hd.ne_zero) (pow_ne_zero 2 hs),
          padicValRat.pow, val_squarefree hd, ite_eq_left hld'] at hz
        omega
      exact (hl.dvd_iff_one_le_factorization (by simpa using hB)).mp (Int.natCast_dvd.mp hlB)
    · simp [Nat.factorization_eq_zero_of_not_dvd hld]
  · simp [Nat.factorization_eq_zero_of_not_prime d.natAbs hl]

private lemma invert_x {B x y : ℚ} (hx : x ≠ 0) (hxy : OnCurve B x y) :
    OnCurve B (B / x) (B * y / x ^ 2) := by
  unfold OnCurve at *
  field_simp
  linear_combination B ^ 2 * hxy

private lemma quartic {B d e : ℤ} {x y s : ℚ} (hx : x ≠ 0)
    (hxy : OnCurve B x y) (hxs : x = (d : ℚ) * s ^ 2) (hB : B = d * e) :
    ∃ u v w : ℤ, u.natAbs.Coprime v.natAbs ∧ w ^ 2 = d * u ^ 4 + e * v ^ 4 := by
  have hd : (d : ℚ) ≠ 0 := left_ne_zero_of_mul (hxs ▸ hx)
  have hs : s ≠ 0 := by rintro rfl; exact hx (by simpa using hxs)
  have hv : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have hu : (s.num : ℚ) = s * (s.den : ℚ) := (div_eq_iff hv).mp s.num_div_den
  have hsq : IsSquare ((↑(d * s.num ^ 4 + e * (s.den : ℤ) ^ 4) : ℚ)) := by
    refine ⟨y * (s.den : ℚ) ^ 2 / ((d : ℚ) * s), ?_⟩
    push_cast
    rw [hu]
    unfold OnCurve at hxy
    rw [hxs, hB] at hxy
    push_cast at hxy
    field_simp
    linear_combination -hxy
  obtain ⟨w, hw⟩ := Rat.isSquare_intCast_iff.mp hsq
  exact ⟨s.num, s.den, w, by simpa using s.reduced, by simpa [pow_two] using hw.symm⟩


-- Inversion by the coefficient interchanges the two parities of the 2-adic valuation.
private lemma odd_part {B : ℤ} {x y : ℚ} (hB : B ≠ 0)
    (hpar : Odd (padicValRat 2 (B : ℚ))) (hx : x ≠ 0) (hxy : OnCurve B x y) :
    ∃ (d : ℤ) (s t : ℚ), Squarefree d ∧ ¬(2 : ℤ) ∣ d ∧ d ∣ B ∧
      OnCurve B ((d : ℚ) * s ^ 2) t ∧
      (x = (d : ℚ) * s ^ 2 ∨ (B : ℚ) / x = (d : ℚ) * s ^ 2) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hB
  have oddpart {X Y : ℚ} (hX : X ≠ 0) (h : Even (padicValRat 2 X))
      (hXY : OnCurve B X Y) :
      ∃ (d : ℤ) (s : ℚ), Squarefree d ∧ ¬(2 : ℤ) ∣ d ∧ d ∣ B ∧
        X = (d : ℚ) * s ^ 2 := by
    obtain ⟨d, s, hd, hds⟩ := squarefree_part X
    have hs : s ≠ 0 := by rintro rfl; exact hX (by simpa using hds)
    refine ⟨d, s, hd, ?_, part_dvd hX hXY hd hds, hds⟩
    intro h2
    obtain ⟨i, hi⟩ := h
    rw [hds, padicValRat.mul (Int.cast_ne_zero.mpr hd.ne_zero) (pow_ne_zero 2 hs),
      padicValRat.pow, val_squarefree hd, ite_eq_left (show ((2 : ℕ) : ℤ) ∣ d from h2)] at hi
    omega
  by_cases h : Even (padicValRat 2 x)
  · obtain ⟨d, s, hd, h2, hdvd, hds⟩ := oddpart hx h hxy
    exact ⟨d, s, y, hd, h2, hdvd, hds ▸ hxy, .inl hds⟩
  · have hinv := invert_x hx hxy
    have h' : Even (padicValRat 2 ((B : ℚ) / x)) := by
      rw [padicValRat.div hb hx]
      obtain ⟨a, ha⟩ := hpar
      obtain ⟨b, hb⟩ := Int.not_even_iff_odd.mp h
      exact ⟨a - b, by omega⟩
    obtain ⟨d, s, hd, h2, hdvd, hds⟩ := oddpart (div_ne_zero hb hx) h' hinv
    exact ⟨d, s, _, hd, h2, hdvd, hds ▸ hinv, .inr hds⟩

private lemma odd_dvd {k : ℕ} {d : ℤ} {n : ℕ} (h2 : ¬(2 : ℤ) ∣ d)
    (h : d.natAbs ∣ 2 ^ k * n) : d ∣ (n : ℤ) := by
  have hc : d.natAbs.Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (mt Int.natCast_dvd.mpr h2)).symm
  exact Int.natAbs_dvd_natAbs.mp (by simpa using (hc.pow_right k).dvd_of_dvd_mul_left h)

private def signedFactors (p q : ℕ) : List (ℤ × ℤ) :=
  [(1, (p : ℤ) * q), (-1, -((p : ℤ) * q)),
    (p, q), (-(p : ℤ), -(q : ℤ)), (q, p), (-(q : ℤ), -(p : ℤ)),
    ((p : ℤ) * q, 1), (-((p : ℤ) * q), -1)]

private lemma divisor_cases {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {d : ℤ}
    (hd : d ∣ (p : ℤ) * q) :
    ∃ e : ℤ, d * e = (p : ℤ) * q ∧
      (d, e) ∈ signedFactors p q := by
  have hn : d.natAbs ∣ p * q := by
    simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr hd
  obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.mp hn
  rcases Int.natAbs_eq d with hs | hs <;>
    rcases (Nat.dvd_prime hp).mp ha with ha | ha <;> subst a <;>
    rcases (Nat.dvd_prime hq).mp hb with hb | hb <;> subst b <;>
    rw [← hab] at hs <;> subst d <;> push_cast
  · exact ⟨(p : ℤ) * q, by ring, by simp [signedFactors]⟩
  · exact ⟨(p : ℤ), by ring, by simp [signedFactors]⟩
  · exact ⟨(q : ℤ), by ring, by simp [signedFactors]⟩
  · exact ⟨1, by ring, by simp [signedFactors]⟩
  · exact ⟨-((p : ℤ) * q), by ring, by simp [signedFactors]⟩
  · exact ⟨-(p : ℤ), by ring, by simp [signedFactors]⟩
  · exact ⟨-(q : ℤ), by ring, by simp [signedFactors]⟩
  · exact ⟨-1, by ring, by simp [signedFactors]⟩

private lemma odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.mp (hp.odd_of_ne_two hp2)

private lemma coeff_val {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) {k : ℤ} (hk : k = -2 ∨ k = 8) :
    Odd (padicValRat 2 ((k * (p : ℤ) * q : ℤ) : ℚ)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hk0 : (k : ℚ) ≠ 0 := by rcases hk with rfl | rfl <;> norm_num
  have hvalp : padicValRat 2 (p : ℚ) = 0 := by
    rw [← padicValRat_of_nat, multiplicity_primes (Ne.symm hp2)]
    rfl
  have hvalq : padicValRat 2 (q : ℚ) = 0 := by
    rw [← padicValRat_of_nat, multiplicity_primes (Ne.symm hq2)]
    rfl
  push_cast
  rw [padicValRat.mul (mul_ne_zero hk0 hp0) hq0, padicValRat.mul hk0 hp0, hvalp, hvalq]
  simp only [add_zero]
  rcases hk with rfl | rfl
  · change Odd (padicValRat 2 (-(2 : ℚ)))
    rw [padicValRat.neg, show (2 : ℚ) = ((2 : ℕ) : ℚ) by rfl,
      padicValRat.self (by decide : 1 < 2)]
    decide
  · change Odd (padicValRat 2 ((2 : ℚ) ^ 3))
    rw [padicValRat.pow, show (2 : ℚ) = ((2 : ℕ) : ℚ) by rfl,
      padicValRat.self (by decide : 1 < 2)]
    decide

-- After the inversion, the odd squarefree part divides pq and yields a primitive quartic.
private lemma normalized_point {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) {k : ℤ} (hk : k = -2 ∨ k = 8)
    {x y : ℚ} (hx : x ≠ 0) (hxy : OnCurve ((k * (p : ℤ) * q : ℤ) : ℚ) x y) :
    ∃ (d e u v w : ℤ) (s : ℚ), d * e = (p : ℤ) * q ∧
      (d, e) ∈ signedFactors p q ∧
      u.natAbs.Coprime v.natAbs ∧ w ^ 2 = d * u ^ 4 + k * e * v ^ 4 ∧
      (x = (d : ℚ) * s ^ 2 ∨ ((k * (p : ℤ) * q : ℤ) : ℚ) / x = (d : ℚ) * s ^ 2) := by
  have hB : k * (p : ℤ) * q ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (by exact_mod_cast hp.ne_zero))
      (by exact_mod_cast hq.ne_zero)
    rcases hk with rfl | rfl <;> decide
  obtain ⟨d, s, t, _, h2, hdiv, ht, hs⟩ :=
    odd_part hB (coeff_val hp hq hp2 hq2 hk) hx hxy
  have hdk : d.natAbs ∣ k.natAbs * (p * q) := by
    simpa [Int.natAbs_mul, mul_assoc] using Int.natAbs_dvd_natAbs.mpr hdiv
  have hdpq : d ∣ (p : ℤ) * q := by
    rw [← Int.natCast_mul]
    rcases hk with rfl | rfl
    · exact odd_dvd h2 (k := 1) hdk
    · exact odd_dvd h2 (k := 3) hdk
  obtain ⟨e, he, hm⟩ := divisor_cases hp hq hdpq
  have hds : (d : ℚ) * s ^ 2 ≠ 0 := by
    rcases hs with h | h
    · exact h ▸ hx
    · exact h ▸ div_ne_zero (Int.cast_ne_zero.mpr hB) hx
  obtain ⟨u, v, w, huv, hw⟩ := quartic hds ht rfl
    (show k * (p : ℤ) * q = d * (k * e) from by rw [mul_assoc, ← he]; ring)
  exact ⟨d, e, u, v, w, s, he, hm, huv, hw, hs⟩


private lemma no_common_prime {l : ℕ} (hl : l.Prime) {u v : ℤ}
    (hc : u.natAbs.Coprime v.natAbs) (hu : (l : ℤ) ∣ u) (hv : (l : ℤ) ∣ v) : False := by
  have h := Nat.dvd_gcd (Int.natCast_dvd.mp hu) (Int.natCast_dvd.mp hv)
  rw [hc.gcd_eq_one] at h
  exact hl.not_dvd_one h

private lemma fourth16 (u : ℤ) :
    (u : ZMod 16) ^ 4 = if 2 ∣ u then 0 else 1 := by
  have h : ∀ a : ZMod 16, a ^ 4 = if a.val % 2 = 0 then 0 else 1 := by decide
  have hv := ZMod.val_intCast (n := 16) u
  have hv' : ((u : ZMod 16).val % 2 = 0) ↔ (2 : ℤ) ∣ u := by
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  simpa [hv'] using h (u : ZMod 16)

private lemma quartic_u_odd {d e u v w k : ℤ} (hk : k = -2 ∨ k = 8)
    (he : ¬(2 : ℤ) ∣ e) (hc : u.natAbs.Coprime v.natAbs)
    (hw : w ^ 2 = d * u ^ 4 + k * e * v ^ 4) : ¬(2 : ℤ) ∣ u := by
  intro hu
  have hv : ¬(2 : ℤ) ∣ v := no_common_prime Nat.prime_two hc hu
  have hh := congrArg (fun z : ℤ ↦ (z : ZMod 16)) hw
  push_cast at hh
  rw [fourth16, fourth16] at hh
  simp only [ite_eq_left hu, ite_eq_right hv, mul_zero, zero_add, mul_one] at hh
  have h : ∀ a w : ZMod 16, a.val % 2 = 1 →
      w ^ 2 ≠ -2 * a ∧ w ^ 2 ≠ 8 * a := by decide
  have he' : (e : ZMod 16).val % 2 = 1 := by
    rw [Int.dvd_iff_emod_eq_zero] at he
    have := ZMod.val_intCast (n := 16) e
    omega
  obtain ⟨hneg, hpos⟩ := h (e : ZMod 16) (w : ZMod 16) he'
  rcases hk with rfl | rfl
  · exact hneg (by simpa using hh)
  · exact hpos (by simpa using hh)

private lemma fourth8 (u : ℤ) :
    (u : ZMod 8) ^ 4 = if 2 ∣ u then 0 else 1 := by
  have h : ∀ a : ZMod 8, a ^ 4 = if a.val % 2 = 0 then 0 else 1 := by decide
  have hv := ZMod.val_intCast (n := 8) u
  have hv' : ((u : ZMod 8).val % 2 = 0) ↔ (2 : ℤ) ∣ u := by
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  simpa [hv'] using h (u : ZMod 8)

private lemma odd_factors {d e : ℤ} {p q : ℕ} (hp : p % 2 = 1) (hq : q % 2 = 1)
    (he : d * e = (p : ℤ) * q) : ¬(2 : ℤ) ∣ d ∧ ¬(2 : ℤ) ∣ e := by
  have hprod : ¬(2 : ℤ) ∣ (p : ℤ) * q := by
    change ¬((2 : ℕ) : ℤ) ∣ (p : ℤ) * q
    rw [← Int.natCast_mul, Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, hp, hq]
    decide
  rw [← he] at hprod
  exact ⟨fun h ↦ hprod (dvd_mul_of_dvd_left h _), fun h ↦ hprod (dvd_mul_of_dvd_right h _)⟩

private def admissible (d e : ℤ) : Prop :=
  (d : ZMod 8) = 1 ∨ (d : ZMod 8) - 2 * (e : ZMod 8) = 1

private instance admissibleDecidable (d e : ℤ) : Decidable (admissible d e) :=
  inferInstanceAs (Decidable (_ ∨ _))

private lemma original_admissible {d e u v w : ℤ}
    (hd : ¬(2 : ℤ) ∣ d) (he : ¬(2 : ℤ) ∣ e) (hc : u.natAbs.Coprime v.natAbs)
    (hw : w ^ 2 = d * u ^ 4 + (-2) * e * v ^ 4) : admissible d e := by
  have hu := quartic_u_odd (.inl rfl) he hc hw
  have hh := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hw
  push_cast at hh
  rw [fourth8, fourth8] at hh
  have hd' : (d : ZMod 8).val % 2 = 1 := by
    rw [Int.dvd_iff_emod_eq_zero] at hd
    have := ZMod.val_intCast (n := 8) d
    omega
  have h : ∀ d : ZMod 8, d.val % 2 = 1 → ∀ e w : ZMod 8,
      (w ^ 2 = d ∨ w ^ 2 = d - 2 * e) → d = 1 ∨ d - 2 * e = 1 := by decide
  refine h (d : ZMod 8) hd' (e : ZMod 8) (w : ZMod 8) ?_
  by_cases hv : (2 : ℤ) ∣ v
  · exact .inl (by simpa [hu, hv] using hh)
  · exact .inr (by simpa [hu, hv, sub_eq_add_neg] using hh)

private lemma dual_admissible {d e u v w : ℤ}
    (hd : ¬(2 : ℤ) ∣ d) (he : ¬(2 : ℤ) ∣ e) (hc : u.natAbs.Coprime v.natAbs)
    (hw : w ^ 2 = d * u ^ 4 + 8 * e * v ^ 4) : (d : ZMod 8) = 1 := by
  have hu := quartic_u_odd (.inr rfl) he hc hw
  have hh := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hw
  push_cast at hh
  rw [fourth8] at hh
  have hh' : (w : ZMod 8) ^ 2 = (d : ZMod 8) := by
    simpa [hu, show (8 : ZMod 8) = 0 by decide] using hh
  have hd' : (d : ZMod 8).val % 2 = 1 := by
    rw [Int.dvd_iff_emod_eq_zero] at hd
    have := ZMod.val_intCast (n := 8) d
    omega
  have h : ∀ w : ZMod 8, (w ^ 2).val % 2 = 1 → w ^ 2 = 1 := by decide
  exact hh' ▸ h (w : ZMod 8) (hh'.symm ▸ hd')

private def Cases (p q : ℕ) : Prop :=
  (p % 8, q % 8) ∈ [(3, 3), (3, 5), (3, 7), (5, 5), (5, 7)] ∨
    (p % 8 = 1 ∧ q % 8 ∈ [3, 5, 7] ∧ jacobiSym p q = -1)

private lemma cases_ne_two {p q : ℕ} (h : Cases p q) : p ≠ 2 ∧ q ≠ 2 := by
  simp [Cases] at h
  constructor <;> intro he <;> simp [he] at h

private lemma cast_mod8 {p a : ℕ} (h : p % 8 = a) : (p : ZMod 8) = (a : ZMod 8) := by
  rw [← ZMod.natCast_mod p 8, h]

private def originalReps (p q : ℕ) : List (ℤ × ℤ) :=
  (signedFactors p q).filter fun de ↦ admissible de.1 de.2

private lemma originalReps_length {p q : ℕ} (h : Cases p q) :
    (originalReps p q).length ≤ 4 := by
  simp only [Cases, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with h | ⟨hp, hq, _⟩
  · rcases h with h | h | h | h | h <;>
      obtain ⟨hp, hq⟩ := h <;>
      simp only [originalReps, signedFactors, List.filter_cons, List.filter_nil,
        admissible, Int.cast_one, Int.cast_mul, Int.cast_neg, Int.cast_natCast,
        cast_mod8 hp, cast_mod8 hq] <;> exact of_decide_eq_true rfl
  · rcases hq with hq | hq | hq <;>
      simp only [originalReps, signedFactors, List.filter_cons, List.filter_nil,
        admissible, Int.cast_one, Int.cast_mul, Int.cast_neg, Int.cast_natCast,
        cast_mod8 hp, cast_mod8 hq] <;> exact of_decide_eq_true rfl


-- A prime appearing once in a coefficient forces the other coefficient to be a square
-- modulo that prime. Primitivity ensures that the denominator used modulo the prime is nonzero.
private lemma quartic_square_mod {l : ℕ} (hl : l.Prime) {a b u v w : ℤ}
    (hb : ¬(l : ℤ) ∣ b) (hc : u.natAbs.Coprime v.natAbs)
    (hw : w ^ 2 = ((l : ℤ) * b) * u ^ 4 + a * v ^ 4) :
    IsSquare (a : ZMod l) := by
  let : Fact l.Prime := ⟨hl⟩
  have hcast := congrArg (fun z : ℤ ↦ (z : ZMod l)) hw
  push_cast at hcast
  simp only [ZMod.natCast_self, zero_mul, zero_add] at hcast
  have hv : (v : ZMod l) ≠ 0 := by
    intro hv
    have hw0 : (w : ZMod l) = 0 := by simpa [hv] using hcast
    have hvdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd v l).mp hv
    have hu : (u : ZMod l) ≠ 0 :=
      fun hu ↦ no_common_prime hl hc ((ZMod.intCast_zmod_eq_zero_iff_dvd u l).mp hu) hvdvd
    obtain ⟨v', hv'⟩ := hvdvd
    obtain ⟨w', hw'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd w l).mp hw0
    rw [hv', hw'] at hw
    have hh : (l : ℤ) ∣ b * u ^ 4 := by
      refine ⟨w' ^ 2 - a * (l : ℤ) ^ 2 * v' ^ 4, ?_⟩
      apply mul_left_cancel₀ (Int.natCast_ne_zero.mpr hl.ne_zero)
      linear_combination -hw
    have hcast' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mpr hh
    push_cast at hcast'
    have hb0 : (b : ZMod l) = 0 := by simpa [hu] using hcast'
    exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b l).mp hb0)
  refine ⟨(w : ZMod l) / (v : ZMod l) ^ 2, ?_⟩
  field_simp
  linear_combination -hcast

private lemma dual_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : Cases p q) {d e u v w : ℤ} (hd : 0 < d) (hm : (d, e) ∈ signedFactors p q)
    (hc : u.natAbs.Coprime v.natAbs) (hw : w ^ 2 = d * u ^ 4 + 8 * e * v ^ 4)
    (hm8 : (d : ZMod 8) = 1) : d = 1 := by
  have ⟨hp2, hq2⟩ := cases_ne_two h
  have hpz : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  have hqz : 0 < (q : ℤ) := by exact_mod_cast hq.pos
  have hpqz : 0 < (p : ℤ) * q := mul_pos hpz hqz
  have hpq' : ¬(p : ℤ) ∣ (q : ℤ) :=
    mt Int.natCast_dvd_natCast.mp (mt (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq)
  simp only [signedFactors, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hm
  rcases hm with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact h1.1
  · omega
  · obtain ⟨rfl, rfl⟩ := h3
    rw [Int.cast_natCast] at hm8
    have hmod : p % 8 = 1 := by
      have hh := congrArg ZMod.val hm8
      rwa [ZMod.val_natCast, show (1 : ZMod 8).val = 1 by decide] at hh
    have hJacobi : jacobiSym p q = -1 := by
      rcases h with hpairs | ⟨_, _, hj⟩
      · simp [hmod] at hpairs
      · exact hj
    have h8q : ¬(q : ℤ) ∣ (8 : ℤ) := by
      change ¬(q : ℤ) ∣ ((2 : ℕ) : ℤ) ^ 3
      rw [← Int.natCast_pow, Int.natCast_dvd_natCast]
      exact mt hq.dvd_of_dvd_pow (mt (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2)
    have hs := quartic_square_mod hq h8q hc.symm
      (show w ^ 2 = ((q : ℤ) * 8) * v ^ 4 + (p : ℤ) * u ^ 4 from by
        linear_combination hw)
    exact (ZMod.nonsquare_of_jacobiSym_eq_neg_one hJacobi hs).elim
  · omega
  · obtain ⟨rfl, rfl⟩ := h5
    rw [Int.cast_natCast] at hm8
    have hmod : q % 8 = 1 := by
      have hh := congrArg ZMod.val hm8
      rwa [ZMod.val_natCast, show (1 : ZMod 8).val = 1 by decide] at hh
    simp [Cases, hmod] at h
  · omega
  · obtain ⟨rfl, rfl⟩ := h7
    let : Fact p.Prime := ⟨hp⟩
    have hs8 : IsSquare ((8 : ℤ) : ZMod p) := by
      exact quartic_square_mod hp hpq' hc (by simpa using hw)
    have htwo : (2 : ZMod p) ≠ 0 := by
      change ((2 : ℕ) : ZMod p) ≠ 0
      exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
        (mt (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
    have hs2 : IsSquare (2 : ZMod p) := by
      obtain ⟨z, hz⟩ := hs8
      norm_cast at hz
      refine ⟨z / 2, ?_⟩
      field_simp
      linear_combination hz
    have hpmod := (ZMod.exists_sq_eq_two_iff hp2).mp hs2
    simp only [Cases, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
    push_cast at hm8
    rcases h with h | ⟨hp8, hq8, _⟩
    · rcases h with h | h | h | h | h <;> omega
    · rcases hq8 with hq8 | hq8 | hq8 <;>
        rw [cast_mod8 hp8, cast_mod8 hq8] at hm8 <;>
        exact ((by decide : ¬ _ = _) hm8).elim
  · omega

private lemma dual_squares {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : Cases p q) {x y : ℚ} (hx : x ≠ 0) (hxy : OnCurve (8 * p * q) x y) :
    IsSquare x ∨ IsSquare (8 * p * q / x : ℚ) := by
  have ⟨hp2, hq2⟩ := cases_ne_two h
  have hprec : OnCurve ((8 * (p : ℤ) * q : ℤ) : ℚ) x y := by push_cast; exact hxy
  obtain ⟨d, e, u, v, w, s, he, hm, hc, hw, hds⟩ :=
    normalized_point hp hq hp2 hq2 (.inr rfl) hx hprec
  have hB : 0 < (8 * p * q : ℚ) :=
    mul_pos (mul_pos (by norm_num) (by exact_mod_cast hp.pos)) (by exact_mod_cast hq.pos)
  have hx' : 0 < x := by
    have hpos : 0 < x ^ 2 + (8 * p * q : ℚ) := add_pos_of_nonneg_of_pos (sq_nonneg x) hB
    have hy : 0 ≤ x * (x ^ 2 + (8 * p * q : ℚ)) := hxy ▸ sq_nonneg y
    exact lt_of_le_of_ne (nonneg_of_mul_nonneg_left hy hpos) hx.symm
  push_cast at hds
  have hd : 0 < d := by
    have hs : 0 < (d : ℚ) * s ^ 2 := by
      rcases hds with hh | hh
      · exact hh ▸ hx'
      · exact hh ▸ div_pos hB hx'
    have := pos_of_mul_pos_left hs (sq_nonneg s)
    exact_mod_cast this
  have ⟨hdodd, heodd⟩ := odd_factors (odd_prime hp hp2) (odd_prime hq hq2) he
  have hd1 := dual_pair hp hq hpq h hd hm hc hw (dual_admissible hdodd heodd hc hw)
  simpa [hd1, pow_two, IsSquare] using
    (hds.imp (fun hh ↦ ⟨s, hh⟩) (fun hh ↦ ⟨s, hh⟩) :
      (∃ t : ℚ, x = (d : ℚ) * t ^ 2) ∨ (∃ t : ℚ, (8 * p * q : ℚ) / x = (d : ℚ) * t ^ 2))

private lemma lift_x {B d y : ℚ} (hB : B ≠ 0) (hd : d ≠ 0)
    (h : OnCurve (-4 * B) (d ^ 2) y) :
    ∃ x : ℚ, x ≠ 0 ∧ OnCurve B x (d * x) ∧ x + B / x = d ^ 2 := by
  have hh : d ^ 4 - (y / d) ^ 2 = 4 * B := by
    unfold OnCurve at h
    field_simp
    linear_combination -h
  let x := (d ^ 2 + y / d) / 2
  have hprod : x * ((d ^ 2 - y / d) / 2) = B := by
    dsimp [x]
    linear_combination hh / 4
  have hx : x ≠ 0 := left_ne_zero_of_mul (hprod ▸ hB)
  have hquad : x ^ 2 - d ^ 2 * x + B = 0 := by
    rw [← hprod]
    dsimp [x]
    ring
  refine ⟨x, hx, ?_, ?_⟩
  · unfold OnCurve
    linear_combination -x * hquad
  · field_simp
    linear_combination hquad

-- Lift twice through the two-isogeny formulas. The companion curve's square classes
-- allow the first lift to be chosen with square x-coordinate.
private lemma square_x_double {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (h : Cases p q) {X Y : ℚ} (hX : X ≠ 0)
    (hXY : OnCurve (-(2 * p * q : ℚ)) X Y) (hs : IsSquare X) :
    ∃ x y : ℚ, x ≠ 0 ∧ y ≠ 0 ∧ OnCurve (-(2 * p * q : ℚ)) x y ∧
      X = (x ^ 2 + 2 * p * q) ^ 2 / (4 * y ^ 2) := by
  let B : ℚ := -(2 * p * q)
  let D : ℚ := 8 * p * q
  have hBD : -4 * B = D := by dsimp [B, D]; ring
  have hB : B ≠ 0 := neg_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hp.ne_zero))
      (Nat.cast_ne_zero.mpr hq.ne_zero))
  have hD : D ≠ 0 := hBD ▸ mul_ne_zero (by norm_num) hB
  obtain ⟨d, hd⟩ := hs
  rw [← pow_two] at hd
  have hd0 : d ≠ 0 := by rintro rfl; simp [hd] at hX
  have hd' : (2 * d) ^ 2 = 4 * X := by rw [hd]; ring
  have hscaled : OnCurve (-4 * D) ((2 * d) ^ 2) (8 * Y) := by
    rw [hd', ← hBD]
    unfold OnCurve at hXY ⊢
    change Y ^ 2 = X * (X ^ 2 + B) at hXY
    linear_combination 64 * hXY
  obtain ⟨Q, hQ, hQD, hQX⟩ := lift_x hD (mul_ne_zero (by norm_num) hd0) hscaled
  have hnorm : ∃ U V : ℚ, U ≠ 0 ∧ IsSquare U ∧ OnCurve D U V ∧ U + D / U = 4 * X := by
    rw [hd'] at hQX
    rcases dual_squares hp hq hpq h hQ hQD with hs | hs
    · exact ⟨Q, _, hQ, hs, hQD, hQX⟩
    · refine ⟨D / Q, _, div_ne_zero hD hQ, hs, invert_x hQ hQD, ?_⟩
      have hdd : D / (D / Q) = Q := by field_simp
      rwa [hdd, add_comm]
  obtain ⟨U, V, hU, ⟨r, hr⟩, hUV, hUX⟩ := hnorm
  rw [← pow_two] at hr
  have hr0 : r ≠ 0 := by rintro rfl; simp [hr] at hU
  have hUV' : OnCurve (-4 * B) (r ^ 2) V := by rwa [hBD, ← hr]
  obtain ⟨x, hx, hxy, hxU⟩ := lift_x hB hr0 hUV'
  refine ⟨x, r * x, hx, mul_ne_zero hr0 hx, hxy, ?_⟩
  have hval : U = (x ^ 2 + B) / x := by
    rw [hr, ← hxU]
    field_simp
  change (r * x) ^ 2 = x * (x ^ 2 + B) at hxy
  have hsum : x ^ 2 + B ≠ 0 :=
    right_ne_zero_of_mul (hxy ▸ pow_ne_zero 2 (mul_ne_zero hr0 hx))
  have hcalc : U + D / U = (x ^ 2 - B) ^ 2 / (x * (x ^ 2 + B)) := by
    rw [hval, ← hBD]
    field_simp
    ring
  rw [hcalc, ← hxy] at hUX
  have hnum : x ^ 2 + (2 * p * q : ℚ) = x ^ 2 - B := by simp [B, sub_neg_eq_add]
  rw [hnum, mul_comm (4 : ℚ), ← div_div, eq_div_iff (by norm_num : (4 : ℚ) ≠ 0),
    mul_comm X, hUX]


open WeierstrassCurve

private abbrev Curve (B : ℚ) : WeierstrassCurve ℚ := ⟨0, 0, 0, B, 0⟩

private lemma equation_iff {B x y : ℚ} :
    (Curve B).toAffine.Equation x y ↔ OnCurve B x y := by
  rw [Affine.equation_iff]
  simp only [zero_mul, add_zero]
  unfold OnCurve
  ring_nf

private lemma nonsingular_of_onCurve {B x y : ℚ} (hB : B ≠ 0) (h : OnCurve B x y) :
    (Curve B).toAffine.Nonsingular x y := by
  rw [Affine.nonsingular_iff, equation_iff, and_iff_right h]
  change 0 * y ≠ 3 * x ^ 2 + 2 * 0 * x + B ∨ y ≠ -y - 0 * x - 0
  by_cases hy : y = 0
  · left
    unfold OnCurve at h
    rw [hy] at h
    have hh : x * (x ^ 2 + B) = 0 := by linarith
    rcases mul_eq_zero.mp hh with rfl | hh
    · simpa using Ne.symm hB
    · intro hn
      have hx : x ^ 2 = 0 := by linarith
      exact hB (by linarith)
  · right
    intro hn
    apply hy
    linarith

private def torsionPoint {B : ℚ} (hB : B ≠ 0) : (Curve B).toAffine.Point :=
  .some 0 0 (nonsingular_of_onCurve hB (by simp [OnCurve]))

private lemma torsion_add_self {B : ℚ} (hB : B ≠ 0) :
    torsionPoint hB + torsionPoint hB = 0 :=
  Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])

private lemma point_of_x_zero {B : ℚ} (hB : B ≠ 0) {x y : ℚ}
    (hy : (Curve B).toAffine.Nonsingular x y) (hx : x = 0) :
    Affine.Point.some x y hy = torsionPoint hB := by
  subst x
  have hh := equation_iff.mp hy.1
  have : y = 0 := by simpa [OnCurve] using hh
  subst y
  rfl

private abbrev SquareClasses := ℚˣ ⧸ Subgroup.square ℚˣ

private noncomputable def squareClass (x : ℚ) : SquareClasses :=
  if hx : x ≠ 0 then QuotientGroup.mk (Units.mk0 x hx) else 1

private lemma squareClass_mul {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    squareClass (x * y) = squareClass x * squareClass y := by
  simp only [squareClass, dite_eq_left hx, dite_eq_left hy, dite_eq_left (mul_ne_zero hx hy)]
  rw [← QuotientGroup.mk_mul]
  congr 1
  ext
  rfl

private lemma squareClasses_mul_self (c : SquareClasses) : c * c = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_square]
  exact ⟨u, rfl⟩

private lemma squareClass_eq_one {x : ℚ} (hx : x ≠ 0) :
    squareClass x = 1 ↔ IsSquare x := by
  simp only [squareClass, dite_eq_left hx, QuotientGroup.eq_one_iff, Subgroup.mem_square]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, congrArg Units.val hu⟩
  · rintro ⟨u, hu⟩
    have hu0 : u ≠ 0 := left_ne_zero_of_mul (hu ▸ hx)
    exact ⟨Units.mk0 u hu0, Units.ext hu⟩

private lemma squareClass_div {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    squareClass (x / y) = squareClass x * squareClass y := by
  have he := squareClass_mul (div_ne_zero hx hy) hy
  rw [div_mul_cancel₀ _ hy] at he
  rw [he, mul_assoc, squareClasses_mul_self, mul_one]

private lemma squareClass_mul_sq {x s : ℚ} (hx : x ≠ 0) (hs : s ≠ 0) :
    squareClass (x * s ^ 2) = squareClass x := by
  rw [squareClass_mul hx (pow_ne_zero 2 hs),
    (squareClass_eq_one (pow_ne_zero 2 hs)).mpr (IsSquare.sq _), mul_one]

private noncomputable def pointClass {B : ℚ} : (Curve B).toAffine.Point → SquareClasses
  | .zero => 1
  | .some x _ _ => if x = 0 then squareClass B else squareClass x

private lemma pointClass_neg {B : ℚ} (P : (Curve B).toAffine.Point) :
    pointClass (-P) = pointClass P := by
  cases P with
  | zero => rfl
  | some x y hy => rw [Affine.Point.neg_some]; rfl

private lemma pointClass_torsion {B : ℚ} (hB : B ≠ 0) :
    pointClass (torsionPoint hB) = squareClass B := by simp [pointClass, torsionPoint]

private lemma pointClass_torsion_add {B : ℚ} (hB : B ≠ 0) (P : (Curve B).toAffine.Point) :
    pointClass (torsionPoint hB + P) = squareClass B * pointClass P := by
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, add_zero, pointClass_torsion]
    change squareClass B = squareClass B * 1
    rw [mul_one]
  | some x y hy =>
    by_cases hx : x = 0
    · subst x
      rw [point_of_x_zero hB hy rfl, torsion_add_self, pointClass_torsion, squareClasses_mul_self]
      rfl
    · have hh : (Curve B).toAffine.addX 0 x ((Curve B).toAffine.slope 0 x 0 y) = B / x := by
        rw [Affine.slope_of_X_ne (Ne.symm hx)]
        simp [Affine.addX]
        have hxy := equation_iff.mp hy.1
        unfold OnCurve at hxy
        field_simp
        linear_combination hxy
      rw [torsionPoint, Affine.Point.add_of_X_ne (Ne.symm hx)]
      change (if _ = 0 then squareClass B else squareClass _) =
        squareClass B * (if x = 0 then squareClass B else squareClass x)
      rw [hh, ite_eq_right (div_ne_zero hB hx), ite_eq_right hx, squareClass_div hB hx]

private lemma pointClass_add {B : ℚ} (hB : B ≠ 0) (P Q : (Curve B).toAffine.Point) :
    pointClass (P + Q) = pointClass P * pointClass Q := by
  by_cases hz : P + Q = 0
  · have hq : Q = -P := eq_neg_of_add_eq_zero_right hz
    rw [hz, hq, pointClass_neg, squareClasses_mul_self]
    rfl
  by_cases ht : P + Q = torsionPoint hB
  · have hq : Q = torsionPoint hB + -P := by rw [← ht]; abel
    rw [ht, hq, pointClass_torsion_add, pointClass_neg, pointClass_torsion,
      mul_left_comm, squareClasses_mul_self, mul_one]
  cases P with
  | zero => simp [← Affine.Point.zero_def, pointClass]
  | some x y hy =>
    cases Q with
    | zero => simp [← Affine.Point.zero_def, pointClass]
    | some u v hv =>
      by_cases hx : x = 0
      · subst x
        rw [point_of_x_zero hB hy rfl, pointClass_torsion_add, pointClass_torsion]
      by_cases hu : u = 0
      · subst u
        rw [point_of_x_zero hB hv rfl, add_comm, pointClass_torsion_add,
          pointClass_torsion, mul_comm]
      have hxy : ¬(x = u ∧ y = (Curve B).toAffine.negY u v) :=
        fun hh ↦ hz (Affine.Point.add_of_Y_eq hh.1 hh.2)
      let W := (Curve B).toAffine
      let l := W.slope x u y v
      let z := W.addX x u l
      have hz' : z ≠ 0 := by
        intro he
        apply ht
        rw [Affine.Point.add_some hxy]
        exact point_of_x_zero hB _ he
      have hid : x * u * z = (y - l * x) ^ 2 := by
        have hh := congrArg (fun f : Polynomial ℚ ↦ f.eval 0)
          (Affine.addPolynomial_slope hy.1 hv.1 hxy)
        change (W.addPolynomial x y l).eval 0 =
          (-((Polynomial.X - Polynomial.C x) * (Polynomial.X - Polynomial.C u) *
            (Polynomial.X - Polynomial.C z))).eval 0 at hh
        rw [Affine.addPolynomial_eq] at hh
        simp [Cubic.toPoly, W] at hh
        linear_combination -hh
      have hprod : (squareClass x * squareClass u) * squareClass z = 1 := by
        rw [← squareClass_mul hx hu, ← squareClass_mul (mul_ne_zero hx hu) hz']
        exact (squareClass_eq_one (mul_ne_zero (mul_ne_zero hx hu) hz')).mpr
          (hid ▸ IsSquare.sq (y - l * x))
      rw [Affine.Point.add_some hxy]
      change (if z = 0 then squareClass B else squareClass z) =
        (if x = 0 then squareClass B else squareClass x) *
        (if u = 0 then squareClass B else squareClass u)
      simp only [ite_eq_right hz', ite_eq_right hx, ite_eq_right hu]
      calc
        squareClass z = (squareClass x * squareClass u) *
            ((squareClass x * squareClass u) * squareClass z) := by
          rw [← mul_assoc, squareClasses_mul_self, one_mul]
        _ = _ := by rw [hprod, mul_one]

private noncomputable def descentMap {B : ℚ} (hB : B ≠ 0) :
    (Curve B).toAffine.Point →+ Additive SquareClasses where
  toFun P := Additive.ofMul (pointClass P)
  map_zero' := rfl
  map_add' := pointClass_add hB


private lemma isDouble_of_square {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : Cases p q) (hB : (-(2 * p * q : ℚ)) ≠ 0) {X Y : ℚ}
    (hXY : (Curve (-(2 * p * q : ℚ))).toAffine.Nonsingular X Y)
    (hX : X ≠ 0) (hs : IsSquare X) :
    Affine.Point.some X Y hXY ∈ (nsmulAddMonoidHom 2).range := by
  obtain ⟨x, y, _, hy, hxy, he⟩ := square_x_double hp hq hpq h hX (equation_iff.mp hXY.1) hs
  let B := -(2 * p * q : ℚ)
  let W := (Curve B).toAffine
  have hns : W.Nonsingular x y := nonsingular_of_onCurve hB hxy
  let P : W.Point := .some x y hns
  have hyn : y ≠ W.negY x y := by
    intro hn
    have hh : y = -y := by simpa [Affine.negY, W] using hn
    exact hy (by linarith)
  have hd := Affine.Point.xRep_add_self_of_Y_ne hns hyn
  change (P + P).xRep = _ at hd
  have hd' : (P + P).xRep = ![X, 1] := by
    rw [hd, he]
    congr 1
    have hnum : x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (x ^ 2 + 2 * p * q) ^ 2 := by
      simp [W, B, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    have hden : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 4 * y ^ 2 := by
      change y ^ 2 = x * (x ^ 2 + B) at hxy
      simp [W, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      linear_combination -4 * hxy
    rw [hnum, hden]
  rcases Affine.Point.xRep_eq_xRep_iff.mp
    ((Affine.Point.xRep_some hXY).trans hd'.symm) with he | he
  · exact ⟨P, by simpa [two_nsmul] using he.symm⟩
  · exact ⟨-P, by simpa [two_nsmul] using he.symm⟩

private lemma descentMap_ker {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : Cases p q) (hB : (-(2 * p * q : ℚ)) ≠ 0) (hBn : ¬IsSquare (-(2 * p * q : ℚ))) :
    (descentMap hB).ker = (nsmulAddMonoidHom 2).range := by
  ext P
  constructor
  · intro hp
    cases P with
    | zero => exact ⟨0, by simp [← Affine.Point.zero_def]⟩
    | some x y hy =>
      change pointClass (.some x y hy) = 1 at hp
      by_cases hx : x = 0
      · subst x
        change squareClass (-(2 * p * q : ℚ)) = 1 at hp
        exact (hBn ((squareClass_eq_one hB).mp hp)).elim
      · exact isDouble_of_square ‹p.Prime› hq hpq h hB hy hx
          ((squareClass_eq_one hx).mp (by simpa [pointClass, hx] using hp))
  · intro hP
    obtain ⟨Q, hQ⟩ := AddMonoidHom.mem_range.mp hP
    change 2 • Q = P at hQ
    change descentMap hB P = 0
    rw [← hQ, two_nsmul, map_add]
    exact squareClasses_mul_self (pointClass Q)

private lemma descentMap_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : Cases p q) (hB : (-(2 * p * q : ℚ)) ≠ 0) :
    Finite (descentMap hB).range ∧ Nat.card (descentMap hB).range ≤ 8 := by
  classical
  let B := -(2 * p * q : ℚ)
  let values (de : ℤ × ℤ) : List (Additive SquareClasses) :=
    [Additive.ofMul (squareClass (de.1 : ℚ)), Additive.ofMul (squareClass (B * de.1))]
  let l := (originalReps p q).flatMap values
  have hsubset (v : (descentMap hB).range) : (v : Additive SquareClasses) ∈ l.toFinset := by
    obtain ⟨P, hP⟩ := v.prop
    rw [← hP, List.mem_toFinset, List.mem_flatMap]
    have hbase : ((1 : ℤ), (p : ℤ) * q) ∈ originalReps p q := by
      simp [originalReps, signedFactors, admissible]
    have hbase' : (0 : Additive SquareClasses) ∈ values (1, (p : ℤ) * q) := by
      have h1 := (squareClass_eq_one (by norm_num : (1 : ℚ) ≠ 0)).mpr (by
        simp)
      change Additive.ofMul (1 : SquareClasses) ∈ _
      simp [values, h1]
    have hbase'' : Additive.ofMul (squareClass B) ∈ values (1, (p : ℤ) * q) := by
      simp [values]
    cases P with
    | zero => exact ⟨_, hbase, hbase'⟩
    | some x y hy =>
      by_cases hx : x = 0
      · subst x
        exact ⟨_, hbase, hbase''⟩
      · have ⟨hp2, hq2⟩ := cases_ne_two h
        have heB : ((-2 * (p : ℤ) * q : ℤ) : ℚ) = B := by push_cast; dsimp [B]; ring
        have hxy : OnCurve (((-2 : ℤ) * (p : ℤ) * q : ℤ) : ℚ) x y := by
          rw [heB]
          exact equation_iff.mp hy.1
        obtain ⟨d, e, u, v, w, s, he, hm, hc, hw, hs⟩ :=
          normalized_point hp hq hp2 hq2 (.inl rfl) hx hxy
        have ⟨hdodd, heodd⟩ := odd_factors (odd_prime hp hp2) (odd_prime hq hq2) he
        have hloc := original_admissible hdodd heodd hc hw
        have hm' : (d, e) ∈ originalReps p q := by simpa [originalReps, hloc] using hm
        have hd0 : (d : ℚ) ≠ 0 := by
          exact_mod_cast (show d ≠ 0 from fun h ↦ hdodd (h ▸ dvd_zero _))
        rw [heB] at hs
        have hs0 : s ≠ 0 := by
          rintro rfl
          rcases hs with hs | hs
          · exact hx (by simpa using hs)
          · exact div_ne_zero (show B ≠ 0 from hB) hx
              (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hs)
        refine ⟨(d, e), hm', ?_⟩
        change Additive.ofMul (if x = 0 then squareClass B else squareClass x) ∈ values (d, e)
        rw [ite_eq_right hx]
        rcases hs with hs | hs
        · have hcls := congrArg squareClass hs
          rw [squareClass_mul_sq hd0 hs0] at hcls
          simp [values, hcls]
        · have hcls := congrArg squareClass hs
          rw [squareClass_div hB hx, squareClass_mul_sq hd0 hs0] at hcls
          have hcls' : squareClass x = squareClass (B * (d : ℚ)) := by
            rw [squareClass_mul hB hd0, ← hcls, ← mul_assoc, squareClasses_mul_self, one_mul]
          simp [values, hcls']
  let f : (descentMap hB).range → l.toFinset := fun v ↦ ⟨v.val, hsubset v⟩
  have hf : Function.Injective f := fun a b hab ↦
    Subtype.ext (congrArg (fun v : l.toFinset ↦ (v : Additive SquareClasses)) hab)
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  have hlen (m : List (ℤ × ℤ)) : (m.flatMap values).length = 2 * m.length := by
    induction m with
    | nil => rfl
    | cons a m ih => simp [values, ih, Nat.mul_succ]
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  refine (List.toFinset_card_le l).trans ?_
  exact (hlen _).trans_le (by have := originalReps_length h; omega)

-- Reduction modulo two on the free quotient has a nontrivial kernel, witnessed by T.
private lemma rank_le_two {G : Type*} [AddCommGroup G] [Module.Finite ℤ G] {T : G}
    (hT : 2 • T = 0) (hT' : T ∉ (nsmulAddMonoidHom (α := G) 2).range)
    [Finite (G ⧸ (nsmulAddMonoidHom (α := G) 2).range)]
    (hcard : Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) 2).range) ≤ 8) :
    Module.finrank ℤ G ≤ 2 := by
  classical
  let S := Submodule.torsion ℤ G
  let r := Module.finrank ℤ G
  let e : (G ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ) :=
    (Module.finBasisOfFinrankEq ℤ (G ⧸ S)
      (finrank_quotient_eq_of_le_torsion le_rfl)).equivFun
  let cast : (Fin r → ℤ) →+ (Fin r → ZMod 2) :=
    AddMonoidHom.pi fun i ↦ (Int.castAddHom (ZMod 2)).comp (Pi.evalAddMonoidHom _ i)
  let f := cast.comp (e.toAddEquiv.toAddMonoidHom.comp S.mkQ.toAddMonoidHom)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x, hx⟩ := S.mkQ_surjective (e.symm fun i ↦ (a i).val)
    refine ⟨x, funext fun i ↦ ?_⟩
    change ((e (S.mkQ x) i : ℤ) : ZMod 2) = a i
    rw [hx, e.apply_symm_apply]
    simp
  let D := (nsmulAddMonoidHom (α := G) 2).range
  have hD : D ≤ f.ker := by
    intro y hy
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hy
    change 2 • x = y at hx
    change f y = 0
    rw [← hx, map_nsmul]
    ext i
    change (2 : ℕ) • f x i = 0
    rw [nsmul_eq_mul, show ((2 : ℕ) : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
  let F : G ⧸ D →+ (Fin r → ZMod 2) := QuotientAddGroup.lift D f hD
  have hF : Function.Surjective F := by
    intro a
    obtain ⟨x, rfl⟩ := hf a
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  have hT0 : S.mkQ T = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨2, by norm_num⟩, ?_⟩
    change (2 : ℤ) • T = 0
    exact_mod_cast hT
  have hTk : (QuotientAddGroup.mk T : G ⧸ D) ∈ F.ker := by
    change f T = 0
    simp [f, hT0]
  have hne : (⟨QuotientAddGroup.mk T, hTk⟩ : F.ker) ≠ 0 := by
    intro he
    apply hT'
    exact (QuotientAddGroup.eq_zero_iff T).mp (congrArg Subtype.val he)
  have ht : 2 ≤ Nat.card F.ker := by
    have : Nontrivial F.ker := ⟨⟨_, 0, hne⟩⟩
    exact Finite.one_lt_card
  have hmul := AddSubgroup.card_ker_mul_card_range F
  rw [AddMonoidHom.range_eq_top_of_surjective _ hF, AddSubgroup.card_top] at hmul
  have hpow : Nat.card (Fin r → ZMod 2) = 2 ^ r := by simp
  rw [hpow] at hmul
  have h8 : 2 * 2 ^ r ≤ 8 := (Nat.mul_le_mul_right _ ht).trans (hmul.trans_le hcard)
  by_contra! hr
  have hc : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr
  omega


private lemma rank_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : Cases p q) : Module.finrank ℤ (Curve (-(2 * p * q : ℚ))).toAffine.Point ≤ 2 := by
  let B := -(2 * p * q : ℚ)
  let W := (Curve B).toAffine
  have hBneg : B < 0 := neg_neg_of_pos
    (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hp.pos)) (by exact_mod_cast hq.pos))
  have hB := hBneg.ne
  have hBn : ¬IsSquare B := fun hs ↦ hBneg.not_ge hs.nonneg
  have hk := descentMap_ker hp hq hpq h hB hBn
  obtain ⟨hfin, hcard⟩ := descentMap_bound hp hq h hB
  let e : W.Point ⧸ (nsmulAddMonoidHom 2).range ≃+ (descentMap hB).range :=
    hk ▸ QuotientAddGroup.quotientKerEquivRange (descentMap hB)
  let : Finite (W.Point ⧸ (nsmulAddMonoidHom 2).range) := Finite.of_equiv _ e.symm.toEquiv
  have hcard' : Nat.card (W.Point ⧸ (nsmulAddMonoidHom 2).range) ≤ 8 :=
    (Nat.card_congr e.toEquiv).trans_le hcard
  let : W.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
    have hD : W.Δ = -64 * B ^ 3 := by
      simp [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [hD]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hB)
  obtain ⟨C, hC⟩ := Affine.approx_parallelogram_law W
  have hindex : (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex :=
    AddSubgroup.finiteIndex_of_finite_quotient
  let : AddGroup.FG W.Point := AddCommGroup.fg_of_descent' (h := Affine.Point.naiveHeight)
    hindex (fun P ↦ P.naiveHeight_eq_logHeight.symm ▸ Height.logHeight_nonneg P.xRep) hC
  let : Module.Finite ℤ W.Point := Module.Finite.iff_addGroup_fg.mpr inferInstance
  refine rank_le_two (T := torsionPoint hB) (by rw [two_nsmul, torsion_add_self]) ?_ hcard'
  intro ht
  rw [← hk] at ht
  change pointClass (torsionPoint hB) = 1 at ht
  exact hBn ((squareClass_eq_one hB).mp (pointClass_torsion hB ▸ ht))

end MetaMathlibExt.finrank_point_two_mul_mul_eq_one

namespace MetaMathlibExt

open WeierstrassCurve finrank_point_two_mul_mul_eq_one in
/-- **Odd-rank curves y² = x³ − 2pqx: rank one cases.** Let $p \ne q$ be primes and let $E$ be
the elliptic curve $y^2 = x^3 - 2pqx$ over $\mathbb{Q}$. Suppose that
$(p \bmod 8, q \bmod 8)$ is one of $(3, 3)$, $(3, 5)$, $(3, 7)$, $(5, 5)$, $(5, 7)$, or that
$p \equiv 1 \pmod 8$, $q \equiv 3, 5$ or $7 \pmod 8$ and the Legendre symbol
$\left(\frac{p}{q}\right)$ equals $-1$. If the rank of the group $E(\mathbb{Q})$ of rational
points is odd, then it equals $1$.

The odd-rank hypothesis stands for the parity conjecture for $E$. The case with $p$ and $q$
interchanged is the same curve.

Source: Renz Jimwel Mina and Jerico Bacani, *Rank of the Elliptic Curve y^2=x^3-2pqx*,
INTEGERS 26 (2026), Article A51, Theorem 1 (i) (`integers-2026-A51-thm-1`). -/
public theorem finrank_point_two_mul_mul_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (E : WeierstrassCurve ℚ)
    (hE : E = ⟨0, 0, 0, -(2 * p * q : ℚ), 0⟩)
    (hcase : (p % 8, q % 8) ∈ [(3, 3), (3, 5), (3, 7), (5, 5), (5, 7)] ∨
      (p % 8 = 1 ∧ q % 8 ∈ [3, 5, 7] ∧ jacobiSym p q = -1))
    (hparity : Odd (Module.finrank ℤ E.toProjective.Point)) :
    Module.finrank ℤ E.toProjective.Point = 1 := by
  subst E
  have erank := (Projective.Point.toAffineAddEquiv
    (Curve (-(2 * p * q : ℚ))).toProjective).toIntLinearEquiv.finrank_eq
  rw [erank] at hparity ⊢
  have hle := rank_bound hp hq hpq hcase
  suffices ∀ n : ℕ, n ≤ 2 → Odd n → n = 1 from this _ hle hparity
  rintro n hn ⟨k, hk⟩
  omega

end MetaMathlibExt
