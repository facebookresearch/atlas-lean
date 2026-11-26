/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Units modulo a prime divisor lift into the Jacobi agreement set

Let `n` be odd and `p'` a prime divisor of `n` coprime to `n' = n / p'`. For a unit `z` of
`ℤ/p'ℤ`, the Chinese remainder theorem gives a residue `x` modulo `n` with `x ≡ 1 [MOD n']` and
`x ≡ z [MOD p']`. It is a unit modulo `n`, and since the Jacobi symbol is multiplicative in the
modulus, `(x/n) = (x/n') (x/p') = (1/n') (x/p') = (x/p')`. So `x` lies in the set `L(n;p')` of
units whose Jacobi symbols modulo `n` and modulo `p'` agree, and it reduces to `z` modulo `p'`.

This is Lemma 29 of Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants
Related to the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7. The
arXiv preprint (arXiv:2111.14477) numbers its results differently.
-/

namespace MetaMathlibExt
namespace units_prime_subset_image_jacobi_eq_legendre

/-- The Jacobi symbol of a natural number only depends on its residue class. -/
private theorem jacobiSym_congr {a b n : ℕ} (h : a ≡ b [MOD n]) :
    jacobiSym a n = jacobiSym b n :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr h)

end units_prime_subset_image_jacobi_eq_legendre

open units_prime_subset_image_jacobi_eq_legendre in
/-- **Units modulo a prime divisor lift to units where the Jacobi and Legendre symbols agree.**
Let $n$ be odd and let $p'$ be a prime dividing $n$ such that $p'$ is coprime to $n/p'$. Write
$L(n;p')$ for the set of units $x$ of $\mathbb{Z}/n\mathbb{Z}$ whose least nonnegative
representative $v$ satisfies $\left(\frac{v}{n}\right) = \left(\frac{v}{p'}\right)$, where both
are Jacobi symbols. Then every unit $z$ of $\mathbb{Z}/p'\mathbb{Z}$ is the reduction modulo $p'$
of some element of $L(n;p')$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 29
(`jis-2024-24.1.7-lem-29`). -/
public theorem units_prime_subset_image_jacobi_eq_legendre (n p' : ℕ) (hn : Odd n)
    (hp' : p'.Prime) (hp'n : p' ∣ n) (hcop : Nat.Coprime p' (n / p')) (z : ZMod p')
    (hz : IsUnit z) :
    ∃ x ∈ {x : ZMod n | IsUnit x ∧
        jacobiSym ((x.val : ℕ) : ℤ) n = jacobiSym ((x.val : ℕ) : ℤ) p'},
      ZMod.castHom hp'n (ZMod p') x = z := by
  have hp0 : p' ≠ 0 := hp'.ne_zero
  have hm : n / p' * p' = n := Nat.div_mul_cancel hp'n
  have hm0 : n / p' ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hp'n).mpr ⟨hn.pos.ne', hp0⟩
  have : NeZero p' := ⟨hp0⟩
  have hcop' : Nat.Coprime (n / p') p' := hcop.symm
  have hzcop : Nat.Coprime z.val p' := by
    simpa using ZMod.val_coe_unit_coprime hz.unit
  -- The Chinese remainder lift of `(1, z)`, taken below `n`.
  obtain ⟨c, hcn, hc1, hcz⟩ : ∃ c : ℕ, c < n ∧ c ≡ 1 [MOD n / p'] ∧ c ≡ z.val [MOD p'] :=
    ⟨_, (Nat.chineseRemainder_lt_mul hcop' _ _ hm0 hp0).trans_eq hm,
      (Nat.chineseRemainder hcop' 1 z.val).prop⟩
  refine ⟨(c : ZMod n), ⟨?_, ?_⟩, ?_⟩
  · rw [ZMod.isUnit_iff_coprime, ← hm]
    exact Nat.Coprime.mul_right ((Nat.ModEq.gcd_eq hc1).trans (Nat.coprime_one_left _))
      ((Nat.ModEq.gcd_eq hcz).trans hzcop)
  · -- The factor `n / p'` contributes `(1 / (n / p')) = 1`.
    have hmul := jacobiSym.mul_right' (c : ℤ) hm0 hp0
    rw [hm] at hmul
    rw [ZMod.val_natCast_of_lt hcn, hmul, jacobiSym_congr hc1, Nat.cast_one, jacobiSym.one_left,
      one_mul]
  · rw [map_natCast, (ZMod.natCast_eq_natCast_iff ..).mpr hcz, ZMod.natCast_zmod_val]

end MetaMathlibExt
