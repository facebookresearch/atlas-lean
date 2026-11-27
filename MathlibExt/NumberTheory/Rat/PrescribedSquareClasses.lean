/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import MathlibExt.NumberTheory.Padics.HilbertSymbol.OddFormula
public import MathlibExt.NumberTheory.Padics.HilbertSymbol.TwoFormula
public import MathlibExt.NumberTheory.Rat.Place

@[expose] public section

/-!
# Rational numbers in prescribed square classes at finitely many places

Let `S` be a finite set of places of `ℚ` and let `x_v ∈ ℚ_v^×` for `v ∈ S`. We find a nonzero
rational number `q` and a prime `p₀` with `p₀ ∉ S` such that `q ∈ x_v ℚ_v^{×2}` for every
`v ∈ S` and `|q|_p = 1` for every prime `p ∉ S` with `p ≠ p₀`.

The proof follows the source: put `y = ± ∏_{p ∈ S} p^{v_p(x_p)}`, so that `y = u_p x_p` with
`u_p ∈ ℤ_p^×`; choose by the Chinese remainder theorem an integer `z ≡ u_p mod p^{e_p}`
(`e_p = 1` for odd `p`, `e_2 = 3`), then by Dirichlet's theorem a prime `p₀ ≡ z mod ∏ p^{e_p}`
larger than every prime of `S`, and take `q = p₀ y`. A unit of `ℤ_p` congruent to `1` modulo
`p^{e_p}` is a square (Hensel's lemma), which gives the square classes.

Source: A. V. Sutherland, *Introduction to Arithmetic Geometry*, MIT 18.782 (Fall 2013),
Lecture 11, Lemma 11.11 (statement on p. 3, proof on p. 4),
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>.
-/

namespace Rat.Place

/-- The exponent `e_p` with `e_2 = 3` and `e_p = 1` for `p ≠ 2`: a unit of `ℤ_p` congruent to `1`
modulo `p^{e_p}` is a square. -/
private def sqExp (p : ℕ) : ℕ := if p = 2 then 3 else 1

/-- If the residue of a natural number `n` modulo `p^{e_p}` is that of a unit `u` of `ℤ_p`, then
`n = u t²` for some `t ∈ ℤ_p`. -/
private theorem exists_natCast_eq_unit_mul_sq (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) (n : ℕ)
    (hn : (n : ZMod (p ^ sqExp p)) = PadicInt.toZModPow (sqExp p) (u : ℤ_[p])) :
    ∃ t : ℤ_[p], (n : ℤ_[p]) = u * t ^ 2 := by
  set b : ℤ_[p] := (n : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) with hb
  have hb1 : PadicInt.toZModPow (sqExp p) b = 1 := by
    rw [hb, map_mul, map_natCast, hn, ← map_mul, Units.mul_inv, map_one]
  have hsq : IsSquare b := by
    by_cases hp2 : p = 2
    · subst hp2
      exact PadicInt.isSquare_of_toZModPow_three_eq_one hb1
    · have hmem : b - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := p) (sqExp p)) := by
        rw [RingHom.mem_ker, map_sub, hb1, map_one, sub_self]
      rw [PadicInt.ker_toZModPow, show sqExp p = 1 by simp [sqExp, hp2], pow_one] at hmem
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
      have h0 : PadicInt.toZMod (b - 1) = 0 := by
        rw [← hc, map_mul, map_natCast, ZMod.natCast_self, mul_zero]
      have hb1' : PadicInt.toZMod b = 1 := by
        rwa [map_sub, map_one, sub_eq_zero] at h0
      exact PadicInt.isSquare_of_isSquare_toZMod hp2 (by rw [hb1']; exact one_ne_zero)
        (by rw [hb1']; exact ⟨1, (mul_one 1).symm⟩)
  obtain ⟨s, hs⟩ := hsq
  refine ⟨s, ?_⟩
  calc (n : ℤ_[p]) = b * u := by rw [hb, mul_assoc, Units.inv_mul, mul_one]
    _ = u * s ^ 2 := by rw [hs]; ring

/-- The `l`-adic norm of a prime `p ≠ l` is `1`. -/
private theorem norm_natCast_prime_of_ne {l p : ℕ} [Fact l.Prime] (hp : p.Prime) (h : p ≠ l) :
    ‖(p : ℚ_[l])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.2 <|
    (Nat.coprime_primes (Fact.out : l.Prime) hp).2 (Ne.symm h)

/-- The `l`-adic norm of a product of integer powers of primes. -/
private theorem norm_prod_zpow (l : ℕ) [Fact l.Prime] (P : Finset Nat.Primes)
    (k : Nat.Primes → ℤ) :
    ‖(((∏ p ∈ P, (p.1 : ℚ) ^ k p : ℚ)) : ℚ_[l])‖ = ∏ p ∈ P, ‖(p.1 : ℚ_[l])‖ ^ k p := by
  push_cast
  rw [norm_prod]
  simp [norm_zpow]

/-- The `l`-adic norm of a sign `±1` is `1`. -/
private theorem norm_sign (l : ℕ) [Fact l.Prime] (c : Prop) [Decidable c] :
    ‖(((if c then -1 else 1 : ℚ)) : ℚ_[l])‖ = 1 := by
  split_ifs <;> simp

/-- **A rational number in prescribed square classes at finitely many places.** Let `S` be a
finite set of places of `ℚ` and, for each `v ∈ S`, let `x v` be a unit of the completion `ℚ_v`.
Then there are a rational number `q ≠ 0` and a prime `p₀` whose finite place is not in `S` such
that, for every `v ∈ S`, the image of `q` in `ℚ_v` equals `x v * y ^ 2` for some `y ∈ ℚ_v`
(that is, `q ∈ x_v ℚ_v^{×2}`), and `|q|_p = 1` for every prime `p ≠ p₀` whose finite place is
not in `S`.

Source: A. V. Sutherland, MIT 18.782 (Fall 2013), Lecture 11, Lemma 11.11 (p. 3) and its proof
(p. 4), <https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>. -/
theorem exists_mem_squareClass (S : Finset Place) (x : (v : S) → (CompletedField v.1)ˣ) :
    ∃ (q : ℚ) (p₀ : Nat.Primes), q ≠ 0 ∧ Place.finite p₀ ∉ S ∧
      (∀ v : S, ∃ y : CompletedField v.1, embedding v.1 q = x v * y ^ 2) ∧
      ∀ p : Nat.Primes, Place.finite p ∉ S → p ≠ p₀ → (Place.finite p).absoluteValue q = 1 := by
  classical
  -- the primes of `S`
  let P : Finset Nat.Primes := S.preimage Place.finite (fun _ _ _ _ h => Place.finite.inj h)
  have hP : ∀ p, p ∈ P ↔ Place.finite p ∈ S := fun p => Finset.mem_preimage
  -- the exponents `v_p(x_p)`
  let k : Nat.Primes → ℤ := fun p =>
    if h : Place.finite p ∈ S then
      letI : Fact p.1.Prime := ⟨p.2⟩
      Padic.valuation (p := p.1) ((x ⟨Place.finite p, h⟩ : CompletedField (Place.finite p)))
    else 0
  -- the sign
  let neg : Prop := ∃ h : Place.infinite ∈ S,
    ((x ⟨Place.infinite, h⟩ : CompletedField Place.infinite) : ℝ) < 0
  let y : ℚ := (if neg then -1 else 1) * ∏ p ∈ P, (p.1 : ℚ) ^ k p
  have hprod_pos : (0 : ℚ) < ∏ p ∈ P, (p.1 : ℚ) ^ k p :=
    Finset.prod_pos fun p _ => zpow_pos (by exact_mod_cast p.2.pos) _
  have hy0 : y ≠ 0 := by
    refine mul_ne_zero ?_ hprod_pos.ne'
    split_ifs <;> norm_num
  -- the local data at each prime of `S`
  have key : ∀ p : Nat.Primes, p ∈ P → ∃ r : ℕ, IsUnit (r : ZMod (p.1 ^ sqExp p.1)) ∧
      ∀ n : ℕ, (n : ZMod (p.1 ^ sqExp p.1)) = r → ∀ hp : Place.finite p ∈ S,
        ∃ t : CompletedField (Place.finite p),
          embedding (Place.finite p) ((n : ℚ) * y) = x ⟨Place.finite p, hp⟩ * t ^ 2 := by
    intro p hpP
    have hpS := (hP p).1 hpP
    let _ : Fact p.1.Prime := ⟨p.2⟩
    have : NeZero (p.1 ^ sqExp p.1) := ⟨pow_ne_zero _ p.2.ne_zero⟩
    set xp : ℚ_[p.1] := (x ⟨Place.finite p, hpS⟩ : CompletedField (Place.finite p)) with hxp
    have hxp0 : xp ≠ 0 := (x ⟨Place.finite p, hpS⟩).ne_zero
    have hnormy : ‖(y : ℚ_[p.1])‖ = ‖xp‖ := by
      have hk : k p = xp.valuation := by rw [hxp]; simp [k, hpS]
      rw [Padic.norm_eq_zpow_neg_valuation hxp0, ← hk]
      simp only [y]
      rw [Rat.cast_mul, norm_mul, norm_sign, one_mul, norm_prod_zpow,
        Finset.prod_eq_single p]
      · rw [← norm_zpow]
        exact Padic.norm_p_zpow _
      · intro q _ hqp
        rw [norm_natCast_prime_of_ne q.2 (fun h => hqp (Subtype.ext h)), one_zpow]
      · exact fun h => absurd hpP h
    have hu : ‖(y : ℚ_[p.1]) / xp‖ = 1 := by
      rw [norm_div, hnormy, div_self (norm_ne_zero_iff.2 hxp0)]
    set u : ℤ_[p.1]ˣ := PadicInt.mkUnits hu with hudef
    have huy : ((u : ℤ_[p.1]) : ℚ_[p.1]) * xp = y := by
      rw [hudef, PadicInt.mkUnits_eq, div_mul_cancel₀ _ hxp0]
    refine ⟨(PadicInt.toZModPow (sqExp p.1) (u : ℤ_[p.1])).val, ?_, ?_⟩
    · rw [ZMod.natCast_zmod_val]
      exact u.isUnit.map _
    · intro n hn _
      rw [ZMod.natCast_zmod_val] at hn
      obtain ⟨t, ht⟩ := exists_natCast_eq_unit_mul_sq p.1 u n hn
      refine ⟨((u : ℤ_[p.1]) : ℚ_[p.1]) * (t : ℚ_[p.1]), ?_⟩
      change (((n : ℚ) * y : ℚ) : ℚ_[p.1]) = xp * _
      have ht' : (n : ℚ_[p.1]) = ((u : ℤ_[p.1]) : ℚ_[p.1]) * (t : ℚ_[p.1]) ^ 2 := by
        exact_mod_cast congrArg (fun z : ℤ_[p.1] => (z : ℚ_[p.1])) ht
      rw [Rat.cast_mul, Rat.cast_natCast, ht', ← huy]
      ring
  choose! r hr using key
  -- Chinese remainder theorem
  obtain ⟨z, hz⟩ := Nat.chineseRemainderOfFinset r (fun p : Nat.Primes => p.1 ^ sqExp p.1) P
    (fun p _ => pow_ne_zero _ p.2.ne_zero)
    (fun p _ q _ hpq => Nat.Coprime.pow _ _
      ((Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)))
  let m : ℕ := ∏ p ∈ P, p.1 ^ sqExp p.1
  have : NeZero m := ⟨Finset.prod_ne_zero_iff.2 fun p _ => pow_ne_zero _ p.2.ne_zero⟩
  have hzmod : ∀ p ∈ P, (z : ZMod (p.1 ^ sqExp p.1)) = r p := fun p hp =>
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (hz p hp)
  have hzunit : IsUnit (z : ZMod m) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.prod_right fun p hp => ?_
    rw [← ZMod.isUnit_iff_coprime, hzmod p hp]
    exact (hr p hp).1
  -- Dirichlet's theorem
  obtain ⟨p₀, hp₀gt, hp₀, hp₀mod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod hzunit (∑ p ∈ P, p.1)
  have hp₀modp : ∀ p ∈ P, (p₀ : ZMod (p.1 ^ sqExp p.1)) = r p := by
    intro p hp
    rw [← hzmod p hp, ZMod.natCast_eq_natCast_iff]
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).1 hp₀mod).of_dvd
      (Finset.dvd_prod_of_mem (fun q : Nat.Primes => q.1 ^ sqExp q.1) hp)
  have hp₀notP : ∀ p ∈ P, p.1 ≠ p₀ := by
    intro p hp h
    have : p.1 ≤ ∑ p ∈ P, p.1 := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
    omega
  refine ⟨(p₀ : ℚ) * y, ⟨p₀, hp₀⟩, mul_ne_zero (by exact_mod_cast hp₀.ne_zero) hy0, ?_, ?_, ?_⟩
  · intro h
    exact hp₀notP _ ((hP _).2 h) rfl
  · rintro ⟨v, hv⟩
    cases v with
    | infinite =>
      set xi : ℝ := (x ⟨Place.infinite, hv⟩ : CompletedField Place.infinite) with hxi
      have hxi0 : xi ≠ 0 := (x ⟨Place.infinite, hv⟩).ne_zero
      have hpos : (0 : ℝ) < (p₀ : ℝ) * ((∏ p ∈ P, (p.1 : ℚ) ^ k p : ℚ) : ℝ) :=
        mul_pos (by exact_mod_cast hp₀.pos) (by exact_mod_cast hprod_pos)
      have hdiv : 0 ≤ (((p₀ : ℚ) * y : ℚ) : ℝ) / xi := by
        by_cases hneg : xi < 0
        · have hn : neg := ⟨hv, hneg⟩
          have : (((p₀ : ℚ) * y : ℚ) : ℝ) = -((p₀ : ℝ) * ((∏ p ∈ P, (p.1 : ℚ) ^ k p : ℚ) : ℝ)) := by
            simp only [y, hn, ↓reduceIte]
            push_cast
            ring
          rw [this]
          exact (div_pos_iff.2 (Or.inr ⟨by linarith, hneg⟩)).le
        · have hn : ¬ neg := fun ⟨_, h⟩ => hneg h
          have hxpos : 0 < xi := lt_of_le_of_ne (not_lt.1 hneg) (Ne.symm hxi0)
          have : (((p₀ : ℚ) * y : ℚ) : ℝ) = (p₀ : ℝ) * ((∏ p ∈ P, (p.1 : ℚ) ^ k p : ℚ) : ℝ) := by
            simp only [y, hn, ↓reduceIte]
            push_cast
            ring
          rw [this]
          exact (div_pos hpos hxpos).le
      refine ⟨Real.sqrt ((((p₀ : ℚ) * y : ℚ) : ℝ) / xi), ?_⟩
      change (((p₀ : ℚ) * y : ℚ) : ℝ) = xi * _
      rw [Real.sq_sqrt hdiv, mul_div_cancel₀ _ hxi0]
    | finite p =>
      have hpP : p ∈ P := (hP p).2 hv
      exact (hr p hpP).2 p₀ (hp₀modp p hpP) hv
  · intro l hl hl₀
    let _ : Fact l.1.Prime := ⟨l.2⟩
    rw [← embedding_norm_eq_absoluteValue]
    change ‖((((p₀ : ℚ) * y : ℚ)) : ℚ_[l.1])‖ = 1
    simp only [y]
    rw [Rat.cast_mul, Rat.cast_mul, norm_mul, norm_mul, norm_sign, Rat.cast_natCast,
      norm_natCast_prime_of_ne hp₀ (fun h => hl₀ (Subtype.ext h.symm)), norm_prod_zpow,
      Finset.prod_eq_one]
    · ring
    · intro p hp
      rw [norm_natCast_prime_of_ne p.2 (fun h => hl (by
        rw [show l = p from Subtype.ext h.symm]; exact (hP p).1 hp)), one_zpow]

end Rat.Place
