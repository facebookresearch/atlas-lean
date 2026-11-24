/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The kernel of the Jacobi symbol on units

For odd `n`, let `S(n)` be the set of units of `ℤ/nℤ` whose least nonnegative representative `a`
has Jacobi symbol `(a/n) = 1`.

The Chinese remainder theorem lets us prescribe the Jacobi symbol on a coprime nonsquare factor
while fixing the residue on the other factor, so units modulo the other factor lift to `S(n)`.

The Jacobi symbol of the representative is multiplicative and takes the values `±1` on units, so
`S(n)` is the kernel of a homomorphism from the unit group to `ℤˣ`. If `n` is not a perfect
square, some residue has Jacobi symbol `-1`, so this homomorphism is onto and `S(n)` has index
two. If `n` is a perfect square, every unit lies in `S(n)`.

## Main statements

* `MetaMathlibExt.units_subset_image_jacobi_kernel`: units lift to `S(n)` across a coprime
  nonsquare factor of `n`.
* `MetaMathlibExt.jacobi_kernel_index_two`: `S(n)` has index two in the unit group if `n` is not
  a perfect square, and contains every unit if `n` is a perfect square.

## References

* Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to the Jacobi
  Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Proposition 11 and Lemma 14
  (arXiv:2111.14477v3, Proposition 2.2 and Lemma 2.5).
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

namespace jacobi_kernel_index_two

open units_subset_image_jacobi_kernel

/-- The Jacobi symbol modulo `n` of the least nonnegative representative, as a monoid
homomorphism on `ZMod n`. -/
private def jacobiHom (n : ℕ) : ZMod n →* ℤ where
  toFun a := jacobiSym (a.val : ℤ) n
  map_one' := by
    rw [ZMod.val_one_eq_one_mod, jacobiSym_congr (Nat.mod_modEq 1 n), Nat.cast_one,
      jacobiSym.one_left]
  map_mul' a b := by
    rw [ZMod.val_mul, jacobiSym_congr (Nat.mod_modEq _ n), Nat.cast_mul, jacobiSym.mul_left]

private theorem jacobiHom_apply (n : ℕ) (a : ZMod n) :
    jacobiHom n a = jacobiSym (a.val : ℤ) n :=
  rfl

end jacobi_kernel_index_two

open units_subset_image_jacobi_kernel jacobi_kernel_index_two in
/-- **The index of the Jacobi symbol kernel.** Let $n$ be an odd natural number, let $U(n)$
be the group of units of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$, and let
$S(n) = \{u \in U(n) : (u/n) = 1\}$, where $(u/n)$ is the Jacobi symbol $(a/n)$ of the
representative $0 \le a < n$ of $u$. If $n$ is not a perfect square, then $S(n)$ is a subgroup of
$U(n)$ of index $2$. If $n$ is a perfect square, then $S(n) = U(n)$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7,
Proposition 11 (`jis-2024-24.1.7-prop-11`). -/
public theorem jacobi_kernel_index_two (n : ℕ) (hn : Odd n) :
    (¬ IsSquare n → ∃ H : Subgroup (ZMod n)ˣ,
      (∀ u : (ZMod n)ˣ, u ∈ H ↔ jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = 1) ∧
        H.index = 2) ∧
    (IsSquare n → ∀ u : (ZMod n)ˣ, jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = 1) := by
  refine ⟨fun hsq => ?_, fun hsq u => ?_⟩
  · -- `S(n)` is the kernel of the Jacobi symbol, viewed as a homomorphism `U(n) →* ℤˣ`.
    refine ⟨(Units.map (jacobiHom n)).ker, fun u => ?_, ?_⟩
    · rw [MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one, jacobiHom_apply]
    -- As `n` is not a square, some `a` has Jacobi symbol `-1`. This symbol is not `0`, so `a` is
    -- coprime to `n`; its class is a unit, and the homomorphism is onto `ℤˣ = {1, -1}`.
    obtain ⟨a, ha⟩ := exists_jacobiSym_neg_one hn hsq
    have : NeZero n := ⟨hn.pos.ne'⟩
    have hcop : a.Coprime n := by
      by_contra h
      have h0 : jacobiSym a n = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr h
      exact absurd (h0.symm.trans ha) (by decide)
    have hsurj : Function.Surjective (Units.map (jacobiHom n)) := by
      intro v
      rcases Int.units_eq_one_or v with rfl | rfl
      · exact ⟨1, map_one _⟩
      · refine ⟨ZMod.unitOfCoprime a hcop, Units.ext ?_⟩
        rw [Units.coe_map, ZMod.coe_unitOfCoprime, jacobiHom_apply, ZMod.val_natCast,
          jacobiSym_congr (Nat.mod_modEq a n), ha, Units.val_neg, Units.val_one]
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  · -- For `n = m * m`, the symbol is the square of the symbol modulo `m`, which is `±1`.
    obtain ⟨m, hm⟩ := hsq
    have hcop : ((u : ZMod n).val).Coprime m :=
      (ZMod.val_coe_unit_coprime u).coprime_dvd_right ⟨m, hm⟩
    rw [congrArg (jacobiSym _) hm, ← sq, jacobiSym.pow_right,
      jacobiSym.sq_one ((Int.gcd_natCast_natCast _ _).trans hcop)]

end MetaMathlibExt
