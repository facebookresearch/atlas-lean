/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Units with equal Jacobi and Legendre symbols

Let `n` be odd and `p` a prime divisor of `n`. The map `u ↦ (u/n) (u/p)` is a homomorphism from
the units of `ℤ/nℤ` to `{±1}`, and its kernel is `L(n;p) = {u : (u/n) = (u/p)}`. Writing
`n = ∏ q ^ e_q`, the homomorphism is `(u/p) ^ (e_p + 1) ∏_{q ≠ p} (u/q) ^ e_q`, so it is onto
exactly when `e_p` is even or some other prime has odd exponent; then `L(n;p)` has index two.
This is Proposition 26 of Mondal, Paul and Paul, *Zero-Sum Constants Related to the Jacobi
Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7; the preprint arXiv:2111.14477
numbers its results differently.
-/

namespace MetaMathlibExt
namespace jacobi_eq_legendre_index_two

private theorem jacobiSym_congr {a b n : ℕ} (h : a ≡ b [MOD n]) :
    jacobiSym a n = jacobiSym b n :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr h)

/-- The Jacobi symbol modulo a divisor `m` of `n` of the least nonnegative representative of a
residue `x` modulo `n` only depends on `x`. -/
private theorem jacobiSym_val_eq {n m : ℕ} [NeZero n] (hm : m ∣ n) (x : ZMod n) (a : ℤ)
    (ha : (a : ZMod n) = x) : jacobiSym ((x.val : ℕ) : ℤ) m = jacobiSym a m := by
  have h : ((x.val : ℕ) : ℤ) ≡ a [ZMOD n] := by
    rw [← ZMod.intCast_eq_intCast_iff, ha, Int.cast_natCast, ZMod.natCast_zmod_val]
  exact jacobiSym.mod_left' (h.of_dvd (Int.natCast_dvd_natCast.mpr hm))

/-- For a prime divisor `q` of an odd `n` there is a residue that is a nonresidue modulo `q` and
`1` modulo the part of `n` coprime to `q`. -/
private theorem exists_nonresidue {n q : ℕ} (hn : Odd n) (hq : q.Prime) (hqn : q ∣ n) :
    ∃ a : ℕ, jacobiSym a q = -1 ∧ a ≡ 1 [MOD ordCompl[q] n] ∧
      jacobiSym a n = (-1) ^ n.factorization q := by
  have hq2 : q ≠ 2 := hn.ne_two_of_dvd_nat hqn
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare ((ZMod.ringChar_zmod_n q).trans_ne hq2)
  have hb' : jacobiSym b.val q = -1 := by
    apply ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hb
  obtain ⟨a, haq, ham⟩ := Nat.chineseRemainder (Nat.coprime_ordCompl hq hn.pos.ne') b.val 1
  have haq' : jacobiSym a q = -1 := by rw [jacobiSym_congr haq, hb']
  refine ⟨a, haq', ham, ?_⟩
  calc
    jacobiSym a n = jacobiSym a (ordProj[q] n * ordCompl[q] n) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
    _ = jacobiSym a q ^ n.factorization q * jacobiSym a (ordCompl[q] n) := by
      rw [jacobiSym.mul_right' _ (Nat.ordProj_pos n q).ne' (Nat.ordCompl_pos q hn.pos.ne').ne',
        jacobiSym.pow_right]
    _ = (-1) ^ n.factorization q := by
      rw [haq', jacobiSym_congr ham, Nat.cast_one, jacobiSym.one_left, mul_one]

/-- A residue whose Jacobi symbols modulo `n` and modulo `p` differ. -/
private theorem exists_jacobiSym_mul_eq_neg_one {n p : ℕ} (hn : Odd n) (hp : p.Prime)
    (hpn : p ∣ n)
    (hnot : ¬ (Odd (n.factorization p) ∧
      ∀ q ∈ n.primeFactors, Odd (n.factorization q) → q = p)) :
    ∃ a : ℕ, jacobiSym a n * jacobiSym a p = -1 := by
  by_cases he : Odd (n.factorization p)
  · have h : ¬ ∀ q ∈ n.primeFactors, Odd (n.factorization q) → q = p := fun h => hnot ⟨he, h⟩
    push Not at h
    obtain ⟨q, hq, hqo, hqp⟩ := h
    have hqP := Nat.prime_of_mem_primeFactors hq
    obtain ⟨a, -, ham, han⟩ := exists_nonresidue hn hqP (Nat.dvd_of_mem_primeFactors hq)
    have hpm : p ∣ ordCompl[q] n :=
      Nat.dvd_ordCompl_of_dvd_not_dvd hpn fun h => hqp ((Nat.prime_dvd_prime_iff_eq hqP hp).mp h)
    refine ⟨a, ?_⟩
    rw [han, hqo.neg_one_pow, jacobiSym_congr (Nat.ModEq.of_dvd hpm ham), Nat.cast_one,
      jacobiSym.one_left, mul_one]
  · obtain ⟨a, hap, -, han⟩ := exists_nonresidue hn hp hpn
    rw [Nat.not_odd_iff_even] at he
    exact ⟨a, by rw [han, he.neg_one_pow, hap, one_mul]⟩

/-- The product of the Jacobi symbols modulo `n` and modulo a divisor `p` of `n`, as a
homomorphism on the units of `ℤ/nℤ`. -/
private def jacobiProd (n p : ℕ) [NeZero n] (hpn : p ∣ n) : (ZMod n)ˣ →* ℤ where
  toFun u := jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n * jacobiSym (((u : ZMod n).val : ℕ) : ℤ) p
  map_one' := by
    rw [Units.val_one, jacobiSym_val_eq dvd_rfl 1 1 Int.cast_one,
      jacobiSym_val_eq hpn 1 1 Int.cast_one, jacobiSym.one_left, jacobiSym.one_left, mul_one]
  map_mul' u v := by
    have h : (((((u : ZMod n).val : ℕ) : ℤ) * (((v : ZMod n).val : ℕ) : ℤ) : ℤ) : ZMod n) =
        ((u * v : (ZMod n)ˣ) : ZMod n) := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, Units.val_mul]
    simp only [jacobiSym_val_eq dvd_rfl _ _ h, jacobiSym_val_eq hpn _ _ h, jacobiSym.mul_left]
    ring

end jacobi_eq_legendre_index_two

open jacobi_eq_legendre_index_two in
/-- **Units with equal Jacobi and Legendre symbols form a subgroup of index two.** Let $n$ be an
odd natural number and $p$ a prime divisor of $n$, and suppose that $p$ is not the unique prime
divisor of $n$ with odd exponent in $n$; that is, it is not the case that the exponent of $p$ in
$n$ is odd and every prime divisor of $n$ with odd exponent in $n$ equals $p$. Then the set of
units $u$ of $\mathbb{Z}/n\mathbb{Z}$ whose Jacobi symbol $\left(\frac{u}{n}\right)$ equals the
Legendre symbol $\left(\frac{u}{p}\right)$ is a subgroup of index two in the unit group of
$\mathbb{Z}/n\mathbb{Z}$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7,
Proposition 26 (`jis-2024-24.1.7-prop-26`). -/
public theorem jacobi_eq_legendre_index_two (n p : ℕ) (hn : Odd n) (hp : p.Prime)
    (hpn : p ∣ n)
    (hnot : ¬ (Odd (n.factorization p) ∧
      ∀ q ∈ n.primeFactors, Odd (n.factorization q) → q = p)) :
    ∃ H : Subgroup (ZMod n)ˣ,
      (∀ u : (ZMod n)ˣ, u ∈ H ↔
        jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = jacobiSym (((u : ZMod n).val : ℕ) : ℤ) p) ∧
      H.index = 2 := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  let g := jacobiProd n p hpn
  have hg (u : (ZMod n)ˣ) : g u = jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n *
      jacobiSym (((u : ZMod n).val : ℕ) : ℤ) p := rfl
  refine ⟨g.toHomUnits.ker, fun u => ?_, ?_⟩
  · have hcop : Nat.Coprime (u : ZMod n).val n := ZMod.val_coe_unit_coprime u
    have h1 := jacobiSym.eq_one_or_neg_one (a := (((u : ZMod n).val : ℕ) : ℤ)) (b := n)
      (by rw [Int.gcd_natCast_natCast]; exact hcop)
    have h2 := jacobiSym.eq_one_or_neg_one (a := (((u : ZMod n).val : ℕ) : ℤ)) (b := p)
      (by rw [Int.gcd_natCast_natCast]; exact hcop.coprime_dvd_right hpn)
    rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one, hg]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> decide
  · obtain ⟨a, ha⟩ := exists_jacobiSym_mul_eq_neg_one hn hp hpn hnot
    have hacop : Nat.Coprime a n := by
      by_contra h
      have h0 : jacobiSym a n = 0 :=
        jacobiSym.eq_zero_iff_not_coprime.mpr (by rwa [Int.gcd_natCast_natCast])
      rw [h0, zero_mul] at ha
      exact absurd ha (by decide)
    let u := ZMod.unitOfCoprime a hacop
    have hu : g u = -1 := by
      rw [hg, jacobiSym_val_eq dvd_rfl _ a (by simp [u]), jacobiSym_val_eq hpn _ a (by simp [u]),
        ha]
    have hrange : g.toHomUnits.range = ⊤ := by
      rw [eq_top_iff]
      rintro v -
      rcases Int.units_eq_one_or v with rfl | rfl
      · exact one_mem _
      · exact ⟨u, Units.ext (by rw [MonoidHom.coe_toHomUnits, hu, Units.val_neg, Units.val_one])⟩
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]

end MetaMathlibExt
