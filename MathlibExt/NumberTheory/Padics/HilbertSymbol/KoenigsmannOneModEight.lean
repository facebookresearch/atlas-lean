/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.TwoFormula

/-!
# Hilbert symbols in Koenigsmann's case $p \equiv 1 \pmod 8$

Two computations of local Hilbert symbols from the proof of Proposition 16 of
J. Koenigsmann, "Defining $\mathbb{Z}$ in $\mathbb{Q}$", Ann. of Math. 183 (2016), 73–93, p. 85:

* for $p \equiv 1$ and $q \equiv 3 \pmod{8\mathbb{Z}_{(2)}}$, the $2$-adic symbols are
  $(2p, q)_2 = -1$ and $(-2p, q)_2 = 1$;
* at an odd prime $\ell$, $(-1, q)_\ell = 1$ when $\ell \equiv 1 \pmod 8$ or $v_\ell(q)$ is even.

Both are read off the formulas for the Hilbert symbol (`padicHilbertSymbol.eq_formula_two` and
`padicHilbertSymbol.eq_formula_of_ne_two`). Here $\mathbb{Z}_{(2)}$ is the ring of rationals with
odd denominator, and $p \equiv c \pmod{8\mathbb{Z}_{(2)}}$ means $p - c \in 8\mathbb{Z}_{(2)}$.
-/

set_option autoImplicit false

public section

namespace padicHilbertSymbol

/-- A nonzero $p$-adic number is $p^{v_p(x)}$ times a unit of $\mathbb{Z}_p$. -/
private theorem exists_unit_eq_zpow_valuation_mul {p : ℕ} [Fact p.Prime] (b : ℚ_[p]ˣ) :
    ∃ v : ℤ_[p]ˣ, (b : ℚ_[p]) = (p : ℚ_[p]) ^ (b : ℚ_[p]).valuation * ((v : ℤ_[p]) : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  set β := (b : ℚ_[p]).valuation
  have hnorm : ‖(b : ℚ_[p]) * (p : ℚ_[p]) ^ (-β)‖ = 1 := by
    rw [norm_mul, norm_zpow, Padic.norm_eq_zpow_neg_valuation b.ne_zero, Padic.norm_p, inv_zpow',
      ← zpow_add₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)]
    simp [β]
  let w : ℤ_[p] := ⟨(b : ℚ_[p]) * (p : ℚ_[p]) ^ (-β), hnorm.le⟩
  have hw : IsUnit w := PadicInt.isUnit_iff.2 hnorm
  refine ⟨hw.unit, ?_⟩
  rw [IsUnit.unit_spec]
  change (b : ℚ_[p]) = (p : ℚ_[p]) ^ β * ((b : ℚ_[p]) * (p : ℚ_[p]) ^ (-β))
  rw [mul_left_comm, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero, mul_one]

/-- **The Hilbert symbol $(-1, b)_\ell$ at an odd prime.** Let $\ell$ be an odd prime and let
$b \in \mathbb{Q}_\ell$ be nonzero. Then $(-1, b)_\ell = 1$ if and only if $\ell \equiv 1 \pmod 4$
or the $\ell$-adic valuation $v_\ell(b)$ is even.

This is the case $a = -1$ of the formula for the Hilbert symbol at an odd prime
(`padicHilbertSymbol.eq_formula_of_ne_two`): with $b = \ell^\beta v$, it gives
$(-1, b)_\ell = \left(\frac{-1}{\ell}\right)^\beta$, and
$\left(\frac{-1}{\ell}\right) = (-1)^{(\ell - 1)/2}$ (`legendreSym.at_neg_one`). It is the step
"These two conditions imply $(-1,q)_l = 1$" of the proof of Proposition 16(a) of J. Koenigsmann,
"Defining $\mathbb{Z}$ in $\mathbb{Q}$", Ann. of Math. 183 (2016), 73–93, p. 85, in a form for
every nonzero $\ell$-adic $b$; `padicHilbertSymbol.neg_one_left_eq_one_of_rat` states it as
Koenigsmann uses it. -/
theorem neg_one_left_eq_one_iff {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (b : ℚ_[ℓ]ˣ) :
    padicHilbertSymbol ℓ (-1) b = 1 ↔ ℓ % 4 = 1 ∨ Even (b : ℚ_[ℓ]).valuation := by
  obtain ⟨v, hv⟩ := exists_unit_eq_zpow_valuation_mul b
  rw [eq_formula_of_ne_two hℓ (-1) b 0 _ (-1) v (by simp) hv]
  simp only [zero_mul, Int.natAbs_zero, pow_zero, one_mul, mul_one, Units.val_neg,
    Units.val_one, map_neg, map_one]
  have hleg : legendreSym ℓ ((-1 : ZMod ℓ).val : ℤ) = ZMod.χ₄ ℓ := by
    rw [← legendreSym.at_neg_one hℓ, legendreSym, legendreSym, Int.cast_natCast,
      ZMod.natCast_zmod_val, Int.cast_neg, Int.cast_one]
  rw [hleg, ← Int.natAbs_even]
  have hodd : ℓ % 2 = 1 := Nat.odd_iff.1 ((Fact.out : ℓ.Prime).odd_of_ne_two hℓ)
  rcases (by omega : ℓ % 4 = 1 ∨ ℓ % 4 = 3) with h | h
  · simp [ZMod.χ₄_nat_one_mod_four h, h]
  · rw [ZMod.χ₄_nat_three_mod_four h, neg_one_pow_eq_one_iff_even (by decide)]
    simp [h]

/-- **Koenigsmann: $(-1, q)_\ell = 1$.** Let $q$ be a nonzero rational number and let $\ell$ be
an odd prime. If $\ell \equiv 1 \pmod 8$ or the $\ell$-adic valuation $v_\ell(q)$ is even, then
the $\ell$-adic Hilbert symbol of $-1$ and the image of $q$ in $\mathbb{Q}_\ell$ is
$(-1, q)_\ell = 1$. Here `b` is the unit of $\mathbb{Q}_\ell$ with value $q$.

Koenigsmann's step also assumes $\ell \equiv 1$ or $3 \pmod 8$; the statement holds without that
hypothesis, so it is dropped. In his notation, the hypothesis says $\ell \notin \mathbb{P}^{[3]}(q)$
for an $\ell \equiv 1$ or $3 \pmod 8$, where $\mathbb{P}^{[3]}(q)$ is the set of primes
$\ell \equiv 3 \pmod 8$ with $v_\ell(q)$ odd (Definition 9, p. 80).

Source: J. Koenigsmann, "Defining $\mathbb{Z}$ in $\mathbb{Q}$", Ann. of Math. 183 (2016), 73–93,
proof of Proposition 16(a), p. 85: "These two conditions imply $(-1,q)_l = 1$". -/
theorem neg_one_left_eq_one_of_rat {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (q : ℚ) (b : ℚ_[ℓ]ˣ)
    (hb : (b : ℚ_[ℓ]) = q) (h : ℓ % 8 = 1 ∨ Even (padicValRat ℓ q)) :
    padicHilbertSymbol ℓ (-1) b = 1 := by
  rw [neg_one_left_eq_one_iff hℓ, hb, Padic.valuation_ratCast]
  rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- The value of the $2$-adic formula for $(2u, v)_2$ in terms of the residues of $u$ and $v$
modulo $8$. -/
private theorem two_mul_left_eq (a b : ℚ_[2]ˣ) (u v : ℤ_[2]ˣ)
    (ha : (a : ℚ_[2]) = 2 * ((u : ℤ_[2]) : ℚ_[2])) (hb : (b : ℚ_[2]) = ((v : ℤ_[2]) : ℚ_[2])) :
    padicHilbertSymbol 2 a b =
      (-1) ^ (((PadicInt.toZModPow 3 (u : ℤ_[2])).val - 1) / 2 *
            (((PadicInt.toZModPow 3 (v : ℤ_[2])).val - 1) / 2) +
          ((PadicInt.toZModPow 3 (v : ℤ_[2])).val ^ 2 - 1) / 8) := by
  rw [eq_formula_two a b 1 0 u v (by rw [ha]; simp) (by rw [hb]; simp)]
  simp

/-- **The $2$-adic symbols $(2u, v)_2$ and $(-2u, v)_2$ for $u \equiv 1$ and $v \equiv 3$.** Let
$u, v$ be units of $\mathbb{Z}_2$ with $u \equiv 1$ and $v \equiv 3 \pmod 8$. Then the $2$-adic
Hilbert symbols are $(2u, v)_2 = -1$ and $(-2u, v)_2 = 1$. Here `a`, `a'` and `b` are the units of
$\mathbb{Q}_2$ with values $2u$, $-2u$ and $v$.

By the formula for the $2$-adic Hilbert symbol (`padicHilbertSymbol.eq_formula_two`),
$(2u, v)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \omega(v)} = (-1)^{0 + 1}$ and
$(-2u, v)_2 = (-1)^{\varepsilon(-u)\varepsilon(v) + \omega(v)} = (-1)^{1 + 1}$. -/
theorem two_mul_left_of_one_three {u v : ℤ_[2]ˣ}
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 1) (hv : PadicInt.toZModPow 3 (v : ℤ_[2]) = 3)
    (a a' b : ℚ_[2]ˣ) (ha : (a : ℚ_[2]) = 2 * ((u : ℤ_[2]) : ℚ_[2]))
    (ha' : (a' : ℚ_[2]) = -2 * ((u : ℤ_[2]) : ℚ_[2])) (hb : (b : ℚ_[2]) = ((v : ℤ_[2]) : ℚ_[2])) :
    padicHilbertSymbol 2 a b = -1 ∧ padicHilbertSymbol 2 a' b = 1 := by
  refine ⟨?_, ?_⟩
  · rw [two_mul_left_eq a b u v ha hb, hu, hv]
    decide
  · have ha'' : (a' : ℚ_[2]) = 2 * (((-u : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) := by
      rw [ha']; push_cast; ring
    have hnu : PadicInt.toZModPow 3 ((-u : ℤ_[2]ˣ) : ℤ_[2]) = -1 := by
      rw [Units.val_neg, map_neg, hu]
    rw [two_mul_left_eq a' b (-u) v ha'' hb, hnu, hv]
    decide

/-- A rational $c + 8x$ with $c \in \mathbb{Z}$ odd and $x \in \mathbb{Z}_{(2)}$ is a unit of
$\mathbb{Z}_2$ congruent to $c$ modulo $8$. -/
private theorem exists_unit_of_odd_den (c : ℤ) (hc : Odd c) (x : ℚ) (hx : Odd x.den) :
    ∃ u : ℤ_[2]ˣ, (((c + 8 * x : ℚ)) : ℚ_[2]) = ((u : ℤ_[2]) : ℚ_[2]) ∧
      PadicInt.toZModPow 3 (u : ℤ_[2]) = c := by
  have hx1 : ‖(x : ℚ_[2])‖ ≤ 1 :=
    Padic.norm_rat_le_one (fun h => by
      rw [Nat.odd_iff] at hx
      omega)
  let x' : ℤ_[2] := ⟨(x : ℚ_[2]), hx1⟩
  set w : ℤ_[2] := (c : ℤ_[2]) + 8 * x' with hw
  have hc1 : ‖(c : ℤ_[2])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd c).1 h
    obtain ⟨k, hk⟩ := hc
    omega
  have h8 : ‖(8 : ℤ_[2]) * x'‖ < 1 := by
    rw [norm_mul]
    have : ‖(8 : ℤ_[2])‖ = 1 / 8 := by
      have := PadicInt.norm_p_pow (p := 2) 3
      norm_num at this
      exact this
    rw [this]
    nlinarith [PadicInt.norm_le_one x', norm_nonneg x']
  have hwn : ‖w‖ = 1 := by
    rw [hw, PadicInt.norm_add_eq_max_of_ne (by rw [hc1]; exact h8.ne'), hc1]
    exact max_eq_left h8.le
  refine ⟨(PadicInt.isUnit_iff.2 hwn).unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, hw]
    push_cast
    rfl
  · rw [IsUnit.unit_spec, hw, map_add, map_mul, map_intCast,
      show PadicInt.toZModPow 3 (8 : ℤ_[2]) = 0 by
        rw [show (8 : ℤ_[2]) = ((8 : ℕ) : ℤ_[2]) by norm_num, map_natCast]
        decide]
    simp

/-- **Koenigsmann: $(2p, q)_2 = -1$ and $(-2p, q)_2 = 1$.** Let $p, q$ be rational numbers with
$p \equiv 1$ and $q \equiv 3 \pmod{8\mathbb{Z}_{(2)}}$, that is, $p = 1 + 8x$ and $q = 3 + 8y$ for
rationals $x, y$ with odd denominators. Then the $2$-adic Hilbert symbols of the images in
$\mathbb{Q}_2$ are $(2p, q)_2 = -1$ and $(-2p, q)_2 = 1$. Here `a`, `a'` and `b` are the units of
$\mathbb{Q}_2$ with values $2p$, $-2p$ and $q$.

The source takes $p, q \in \mathbb{Q}^\times$; the congruences already force $p, q \neq 0$, so that
hypothesis is not stated.

Source: J. Koenigsmann, "Defining $\mathbb{Z}$ in $\mathbb{Q}$", Ann. of Math. 183 (2016), 73–93,
proof of Proposition 16(a), p. 85: "Since $p \equiv 1 \pmod{8\mathbb{Z}_{(2)}}$ and
$q \equiv 3 \pmod{8\mathbb{Z}_{(2)}}$, we have, by Observation 5, $(2p,q)_2 = -1$"; the value
$(-2p, q)_2 = 1$ gives $2 \notin \mathbb{P}(p, q) = \Delta_{-2p,q} \cap \Delta_{2p,q}$
(Definition 9(c), p. 80), as Proposition 16(b) uses with Lemma 14 (p. 83). -/
theorem two_mul_left_of_rat_one_three (p q : ℚ) (hp : ∃ x : ℚ, Odd x.den ∧ p = 1 + 8 * x)
    (hq : ∃ y : ℚ, Odd y.den ∧ q = 3 + 8 * y) (a a' b : ℚ_[2]ˣ)
    (ha : (a : ℚ_[2]) = 2 * (p : ℚ_[2])) (ha' : (a' : ℚ_[2]) = -2 * (p : ℚ_[2]))
    (hb : (b : ℚ_[2]) = q) :
    padicHilbertSymbol 2 a b = -1 ∧ padicHilbertSymbol 2 a' b = 1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, rfl⟩ := hq
  obtain ⟨u, hu, hu8⟩ := exists_unit_of_odd_den 1 odd_one x hx
  obtain ⟨v, hv, hv8⟩ := exists_unit_of_odd_den 3 (by decide) y hy
  push_cast at hu hv hu8 hv8
  refine two_mul_left_of_one_three hu8 hv8 a a' b ?_ ?_ ?_
  · rw [ha, ← hu]; push_cast; ring
  · rw [ha', ← hu]; push_cast; ring
  · rw [hb, ← hv]; push_cast; ring

end padicHilbertSymbol
