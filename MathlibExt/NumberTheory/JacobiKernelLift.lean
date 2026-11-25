/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Lifting units to the kernel of the Jacobi symbol

The Chinese remainder theorem lets us prescribe the Jacobi symbol on a coprime
nonsquare factor while fixing the residue on the other factor. This is the lifting
lemma of Mondal, Paul and Paul, *Zero-Sum Constants Related to the Jacobi Symbol*
(arXiv:2111.14477, Lemma 2.5).
-/

namespace MetaMathlibExt
namespace units_subset_image_jacobi_kernel

private theorem jacobiSym_congr {a b n : ℕ} (h : a ≡ b [MOD n]) :
    jacobiSym a n = jacobiSym b n :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr h)

private theorem exists_jacobiSym_neg_one {d : ℕ} (ho : Odd d) (hd : ¬ IsSquare d) :
    ∃ a : ℕ, jacobiSym a d = -1 := by
  rw [Nat.isSquare_iff_even_factorization] at hd
  push Not at hd
  obtain ⟨p, hp, he⟩ := hd
  have heOdd : Odd (d.factorization p) := he
  have hp2 := ho.ne_two_of_dvd_nat (Nat.dvd_of_factorization_pos heOdd.pos.ne')
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare ((ZMod.ringChar_zmod_n p).trans_ne hp2)
  have hb' : jacobiSym b.val p = -1 := by
    apply ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hb
  -- A nonresidue at p contributes a minus sign. The complementary factor contributes one.
  obtain ⟨a, hap, hac⟩ := Nat.chineseRemainder (Nat.coprime_ordCompl hp ho.pos.ne') b.val 1
  refine ⟨a, ?_⟩
  calc
    jacobiSym a d = jacobiSym a (ordProj[p] d * ordCompl[p] d) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
    _ = jacobiSym a p ^ d.factorization p * jacobiSym a (ordCompl[p] d) := by
      rw [jacobiSym.mul_right' _ (Nat.ordProj_pos d p).ne' (Nat.ordCompl_pos p ho.pos.ne').ne',
        jacobiSym.pow_right]
    _ = -1 := by
      rw [jacobiSym_congr hap, jacobiSym_congr hac, hb', heOdd.neg_one_pow]
      simp

end units_subset_image_jacobi_kernel

open units_subset_image_jacobi_kernel in
/-- **Units lift to the kernel of the Jacobi symbol across a non-square coprime factor.** Let $d$
and $n'$ be coprime natural numbers such that $d n'$ is odd and $d$ is not a perfect square, and
put $n = d n'$. Then every unit $y$ of $\mathbb{Z}/n'\mathbb{Z}$ is the reduction modulo $n'$ of a
unit $x$ of $\mathbb{Z}/n\mathbb{Z}$ whose least nonnegative representative $v$ has Jacobi symbol
$\left(\frac{v}{n}\right) = 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 14
(`jis-2024-24.1.7-lem-14`). -/
public theorem units_subset_image_jacobi_kernel (d n' : ℕ) (hn : Odd (d * n'))
    (hd : ¬ IsSquare d) (hcop : Nat.Coprime d n') (y : ZMod n') (hy : IsUnit y) :
    ∃ x ∈ {x : ZMod (d * n') | IsUnit x ∧ jacobiSym ((x.val : ℕ) : ℤ) (d * n') = 1},
      ZMod.castHom (dvd_mul_left n' d) (ZMod n') x = y := by
  obtain ⟨hdo, hno⟩ := Nat.odd_mul.mp hn
  have : NeZero n' := ⟨hno.pos.ne'⟩
  have : NeZero (d * n') := ⟨hn.pos.ne'⟩
  have hycop : (y.val : ℤ).gcd n' = 1 := by
    simpa only [Int.gcd_natCast_natCast, IsUnit.unit_spec] using ZMod.val_coe_unit_coprime hy.unit
  obtain ⟨a, ha⟩ : ∃ a : ℕ, jacobiSym a d = jacobiSym y.val n' := by
    rcases jacobiSym.eq_one_or_neg_one hycop with h | h
    · exact ⟨1, by rw [h, Nat.cast_one, jacobiSym.one_left]⟩
    · rw [h]
      exact exists_jacobiSym_neg_one hdo hd
  let x := Nat.chineseRemainder hcop a y.val
  have hx : jacobiSym (x : ℕ) (d * n') = 1 := by
    rw [jacobiSym.mul_right' _ hdo.pos.ne' hno.pos.ne', jacobiSym_congr x.prop.1,
      jacobiSym_congr x.prop.2, ha, ← pow_two, jacobiSym.sq_one hycop]
  refine ⟨((x : ℕ) : ZMod (d * n')), ⟨?_, ?_⟩, ?_⟩
  · apply (ZMod.isUnit_iff_coprime ..).mpr
    by_contra h
    exact one_ne_zero (hx.symm.trans (jacobiSym.eq_zero_iff_not_coprime.mpr h))
  · rwa [ZMod.val_natCast_of_lt (Nat.chineseRemainder_lt_mul hcop _ _ hdo.pos.ne' hno.pos.ne')]
  · rw [map_natCast, (ZMod.natCast_eq_natCast_iff ..).mpr x.prop.2, ZMod.natCast_zmod_val]

end MetaMathlibExt
