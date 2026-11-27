/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.TwoFormula

/-!
# Bilinearity and nondegeneracy of the $p$-adic Hilbert symbol

For every prime $p$, the $p$-adic Hilbert symbol is a nondegenerate bilinear form on the
$\mathbb{F}_2$-vector space $\mathbb{Q}_p^\times / \mathbb{Q}_p^{\times 2}$
(J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 2, p. 20, the case
$k = \mathbb{Q}_p$). This file proves, for all nonzero $a, a', b, b' \in \mathbb{Q}_p$:

* $(a a', b)_p = (a, b)_p (a', b)_p$ and $(a, b b')_p = (a, b)_p (a, b')_p$;
* if $(a, b)_p = 1$ for every nonzero $a \in \mathbb{Q}_p$, then $b$ is a square in
  $\mathbb{Q}_p^\times$, and conversely.

The symmetry $(a, b)_p = (b, a)_p$ is `hilbertSymbol.comm`, and the invariance under squares is
`hilbertSymbol.mul_sq_left`.

Both statements are derived from the formulas of Theorem 1 of the same section
(`padicHilbertSymbol.eq_formula_of_ne_two` and `padicHilbertSymbol.eq_formula_two`). Writing
$a = p^\alpha u$ with $u$ a unit of $\mathbb{Z}_p$, the product $a a'$ is
$p^{\alpha + \alpha'} u u'$. For odd $p$ the Legendre symbol is multiplicative; for $p = 2$ the
classes $\varepsilon$ and $\omega$ are additive on units, which is a check modulo $8$.
Nondegeneracy evaluates the symbol against a nonsquare unit and $p$ when $p$ is odd, and against
$5$, $-1$ and $2$ when $p = 2$.
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbol

variable {p : ℕ} [hp : Fact p.Prime]

private theorem bil_p_ne_zero : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero

/-- Every nonzero $p$-adic number is $p^\alpha u$ with $u$ a unit of $\mathbb{Z}_p$. -/
private theorem exists_zpow_mul_unit (a : ℚ_[p]ˣ) :
    ∃ (α : ℤ) (u : ℤ_[p]ˣ), (a : ℚ_[p]) = (p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p]) := by
  have ha : (a : ℚ_[p]) ≠ 0 := a.ne_zero
  have hn : ‖(p : ℚ_[p]) ^ (-(a : ℚ_[p]).valuation) * (a : ℚ_[p])‖ = 1 := by
    rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation ha, neg_neg,
      ← zpow_add₀ (Nat.cast_ne_zero.2 hp.out.ne_zero), add_neg_cancel, zpow_zero]
  refine ⟨(a : ℚ_[p]).valuation, PadicInt.mkUnits hn, ?_⟩
  rw [PadicInt.mkUnits_eq, ← mul_assoc, ← zpow_add₀ bil_p_ne_zero, add_neg_cancel, zpow_zero,
    one_mul]

private theorem coe_mul_units (u u' : ℤ_[p]ˣ) :
    (((u * u' : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * ((u' : ℤ_[p]) : ℚ_[p]) := by
  rw [Units.val_mul, PadicInt.coe_mul]

private theorem decomp_mul {a a' : ℚ_[p]ˣ} {α α' : ℤ} {u u' : ℤ_[p]ˣ}
    (ha : (a : ℚ_[p]) = (p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p]))
    (ha' : (a' : ℚ_[p]) = (p : ℚ_[p]) ^ α' * ((u' : ℤ_[p]) : ℚ_[p])) :
    ((a * a' : ℚ_[p]ˣ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (α + α') * (((u * u' : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
  rw [Units.val_mul, ha, ha', coe_mul_units, zpow_add₀ bil_p_ne_zero]
  ring

/-- A sign raised to the absolute value of an integer only depends on its parity. -/
private theorem pow_natAbs_eq_ite {M : Type*} [Monoid M] {s : M} (hs : s ^ 2 = 1) (n : ℤ) :
    s ^ n.natAbs = if Even n then 1 else s := by
  split_ifs with h
  · obtain ⟨k, hk⟩ := Int.natAbs_even.2 h
    rw [hk, ← two_mul, pow_mul, hs, one_pow]
  · have h' : ¬Even n.natAbs := fun h' => h (Int.natAbs_even.1 h')
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 h'
    rw [hk, pow_succ, pow_mul, hs, one_pow, one_mul]

private theorem pow_natAbs_add {M : Type*} [Monoid M] {s : M} (hs : s ^ 2 = 1) (m n : ℤ) :
    s ^ (m + n).natAbs = s ^ m.natAbs * s ^ n.natAbs := by
  rw [pow_natAbs_eq_ite hs, pow_natAbs_eq_ite hs, pow_natAbs_eq_ite hs]
  by_cases hm : Even m <;> by_cases hn : Even n
  · simp [hm, hn, Even.add hm hn]
  · have : ¬Even (m + n) := by rw [Int.even_add]; tauto
    simp [hm, hn, this]
  · have : ¬Even (m + n) := by rw [Int.even_add]; tauto
    simp [hm, hn, this]
  · have : Even (m + n) := by rw [Int.even_add]; tauto
    simp only [hm, hn, this, ite_true, ite_false]
    rw [← pow_two, hs]

private theorem legendreSym_toZMod_val' (x : ZMod p) :
    legendreSym p (x.val : ℤ) = quadraticChar (ZMod p) x := by
  rw [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem legendreSym_mul_units (u u' : ℤ_[p]ˣ) :
    legendreSym p (PadicInt.toZMod ((u * u' : ℤ_[p]ˣ) : ℤ_[p])).val =
      legendreSym p (PadicInt.toZMod (u : ℤ_[p])).val *
        legendreSym p (PadicInt.toZMod (u' : ℤ_[p])).val := by
  rw [legendreSym_toZMod_val', legendreSym_toZMod_val', legendreSym_toZMod_val', Units.val_mul,
    map_mul, map_mul]

private theorem legendreSym_unit_sq (u : ℤ_[p]ˣ) :
    legendreSym p (PadicInt.toZMod (u : ℤ_[p])).val ^ 2 = 1 := by
  rw [legendreSym_toZMod_val']
  exact quadraticChar_sq_one (RingHom.isUnit_map _ u.isUnit).ne_zero

/-- Multiplicativity in the first argument for odd $p$. -/
private theorem mul_left_of_ne_two (hp2 : p ≠ 2) (a a' b : ℚ_[p]ˣ) :
    padicHilbertSymbol p (a * a') b = padicHilbertSymbol p a b * padicHilbertSymbol p a' b := by
  obtain ⟨α, u, ha⟩ := exists_zpow_mul_unit a
  obtain ⟨α', u', ha'⟩ := exists_zpow_mul_unit a'
  obtain ⟨β, v, hb⟩ := exists_zpow_mul_unit b
  rw [padicHilbertSymbol.eq_formula_of_ne_two hp2 _ _ _ _ _ _ (decomp_mul ha ha') hb,
    padicHilbertSymbol.eq_formula_of_ne_two hp2 _ _ _ _ _ _ ha hb,
    padicHilbertSymbol.eq_formula_of_ne_two hp2 _ _ _ _ _ _ ha' hb,
    legendreSym_mul_units, add_mul, add_mul, pow_natAbs_add (by norm_num),
    pow_natAbs_add (legendreSym_unit_sq v), mul_pow]
  ring

/-- Residues modulo $8$ of units of $\mathbb{Z}_2$. -/
private def OddRes8 (r : ZMod 8) : Prop :=
  r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7

private theorem oddRes8_of_isUnit {w : ℤ_[2]} (hw : IsUnit w) :
    OddRes8 (PadicInt.toZModPow 3 w) := by
  obtain ⟨t, ht⟩ := (hw.map (PadicInt.toZModPow 3)).exists_right_inv
  have key : ∀ r t : ZMod 8, r * t = 1 → OddRes8 r := by
    unfold OddRes8
    decide
  exact key _ _ ht

/-- The class $\varepsilon$ is additive on units, modulo $2$. -/
private theorem eps_mul {r s : ZMod 8} (hr : OddRes8 r) (hs : OddRes8 s) :
    ((((r * s).val - 1) / 2 : ℕ) : ZMod 2) = (((r.val - 1) / 2 : ℕ) : ZMod 2) +
      (((s.val - 1) / 2 : ℕ) : ZMod 2) := by
  unfold OddRes8 at hr hs
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;> decide

/-- The class $\omega$ is additive on units, modulo $2$. -/
private theorem omega_mul {r s : ZMod 8} (hr : OddRes8 r) (hs : OddRes8 s) :
    ((((r * s).val ^ 2 - 1) / 8 : ℕ) : ZMod 2) = (((r.val ^ 2 - 1) / 8 : ℕ) : ZMod 2) +
      (((s.val ^ 2 - 1) / 8 : ℕ) : ZMod 2) := by
  unfold OddRes8 at hr hs
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;> decide

private theorem natAbs_cast_zmod_two (n : ℤ) : ((n.natAbs : ℕ) : ZMod 2) = (n : ZMod 2) := by
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq n with h | h
  · rw [← h]
  · conv_rhs => rw [h]
    rw [Int.cast_neg, ZMod.neg_eq_self_mod_two]

/-- A power of $-1$ only depends on the parity of the exponent. -/
private theorem neg_one_pow_eq_of_cast_eq {m n : ℕ} (h : (m : ZMod 2) = (n : ZMod 2)) :
    (-1 : ℤ) ^ m = (-1 : ℤ) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two m, neg_one_pow_eq_pow_mod_two n,
    (ZMod.natCast_eq_natCast_iff' m n 2).1 h]

/-- Multiplicativity in the first argument for $p = 2$. -/
private theorem mul_left_two (a a' b : ℚ_[2]ˣ) :
    padicHilbertSymbol 2 (a * a') b = padicHilbertSymbol 2 a b * padicHilbertSymbol 2 a' b := by
  obtain ⟨α, u, ha⟩ := exists_zpow_mul_unit a
  obtain ⟨α', u', ha'⟩ := exists_zpow_mul_unit a'
  obtain ⟨β, v, hb⟩ := exists_zpow_mul_unit b
  have ha2 : (a : ℚ_[2]) = (2 : ℚ_[2]) ^ α * ((u : ℤ_[2]) : ℚ_[2]) := by exact_mod_cast ha
  have ha2' : (a' : ℚ_[2]) = (2 : ℚ_[2]) ^ α' * ((u' : ℤ_[2]) : ℚ_[2]) := by exact_mod_cast ha'
  have hb2 : (b : ℚ_[2]) = (2 : ℚ_[2]) ^ β * ((v : ℤ_[2]) : ℚ_[2]) := by exact_mod_cast hb
  have hmul : ((a * a' : ℚ_[2]ˣ) : ℚ_[2]) =
      (2 : ℚ_[2]) ^ (α + α') * (((u * u' : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) := by
    exact_mod_cast decomp_mul ha ha'
  rw [padicHilbertSymbol.eq_formula_two _ _ _ _ _ _ hmul hb2,
    padicHilbertSymbol.eq_formula_two _ _ _ _ _ _ ha2 hb2,
    padicHilbertSymbol.eq_formula_two _ _ _ _ _ _ ha2' hb2, ← pow_add]
  apply neg_one_pow_eq_of_cast_eq
  have hu := oddRes8_of_isUnit u.isUnit
  have hu' := oddRes8_of_isUnit u'.isUnit
  have hmu : PadicInt.toZModPow 3 ((u * u' : ℤ_[2]ˣ) : ℤ_[2]) =
      PadicInt.toZModPow 3 (u : ℤ_[2]) * PadicInt.toZModPow 3 (u' : ℤ_[2]) := by
    rw [Units.val_mul, map_mul]
  rw [hmu]
  push_cast
  rw [eps_mul hu hu', omega_mul hu hu', natAbs_cast_zmod_two, natAbs_cast_zmod_two,
    natAbs_cast_zmod_two, natAbs_cast_zmod_two]
  push_cast
  ring

end HilbertSymbol

open HilbertSymbol

namespace padicHilbertSymbol

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The $p$-adic Hilbert symbol is multiplicative in its first argument.** For every prime $p$
and all nonzero $a, a', b \in \mathbb{Q}_p$, the $p$-adic Hilbert symbol satisfies

$$(a a', b)_p = (a, b)_p \, (a', b)_p.$$

Source: J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
Chapter III, §1.1, formula v), p. 20, which Theorem 2 of §1.2, p. 20, states as bilinearity
(the case $k = \mathbb{Q}_p$). -/
theorem mul_left (a a' b : ℚ_[p]ˣ) :
    padicHilbertSymbol p (a * a') b = padicHilbertSymbol p a b * padicHilbertSymbol p a' b := by
  by_cases hp2 : p = 2
  · subst hp2
    exact mul_left_two a a' b
  · exact mul_left_of_ne_two hp2 a a' b

/-- **The $p$-adic Hilbert symbol is multiplicative in its second argument.** For every prime $p$
and all nonzero $a, b, b' \in \mathbb{Q}_p$, the $p$-adic Hilbert symbol satisfies

$$(a, b b')_p = (a, b)_p \, (a, b')_p.$$

Source: J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
Chapter III, §1.2, Theorem 2, p. 20 (bilinearity, the case $k = \mathbb{Q}_p$), from formula v)
of §1.1 and the symmetry $(a, b) = (b, a)$ of Proposition 2 i), p. 19. -/
theorem mul_right (a b b' : ℚ_[p]ˣ) :
    padicHilbertSymbol p a (b * b') = padicHilbertSymbol p a b * padicHilbertSymbol p a b' := by
  have h := mul_left b b' a
  unfold padicHilbertSymbol at h ⊢
  rw [hilbertSymbol.comm a (b * b'), h, hilbertSymbol.comm b a, hilbertSymbol.comm b' a]

end padicHilbertSymbol

namespace HilbertSymbol

variable {p : ℕ} [hp : Fact p.Prime]

private theorem isSquare_units_of_isSquare {b : ℚ_[p]ˣ} (h : IsSquare (b : ℚ_[p])) :
    IsSquare b := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact b.ne_zero (by rw [hc, mul_zero])
  exact ⟨Units.mk0 c hc0, Units.ext (by rw [Units.val_mul, Units.val_mk0, hc])⟩

/-- $p^\beta v$ is a square when $\beta$ is even and the unit $v$ is a square. -/
private theorem isSquare_of_even_of_isSquare {b : ℚ_[p]ˣ} {β : ℤ} {v : ℤ_[p]ˣ}
    (hb : (b : ℚ_[p]) = (p : ℚ_[p]) ^ β * ((v : ℤ_[p]) : ℚ_[p])) (hβ : Even β)
    (hv : IsSquare (v : ℤ_[p])) : IsSquare b := by
  apply isSquare_units_of_isSquare
  obtain ⟨k, hk⟩ := hβ
  obtain ⟨s, hs⟩ := hv
  refine ⟨(p : ℚ_[p]) ^ k * (s : ℚ_[p]), ?_⟩
  rw [hb, hk, zpow_add₀ bil_p_ne_zero, hs, PadicInt.coe_mul]
  ring

/-- The unit of $\mathbb{Q}_p$ given by a unit of $\mathbb{Z}_p$. -/
private theorem coe_unitZpToQp (u : ℤ_[p]ˣ) :
    (unitZpToQp u : ℚ_[p]) = (p : ℚ_[p]) ^ (0 : ℤ) * ((u : ℤ_[p]) : ℚ_[p]) := by
  rw [unitZpToQp_coe, zpow_zero, one_mul]

private theorem coe_p_unit :
    (Units.mk0 (p : ℚ_[p]) bil_p_ne_zero : ℚ_[p]) =
      (p : ℚ_[p]) ^ (1 : ℤ) * (((1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
  rw [Units.val_mk0, zpow_one, Units.val_one, PadicInt.coe_one, mul_one]

/-- Nondegeneracy for odd $p$. -/
private theorem isSquare_of_forall_of_ne_two (hp2 : p ≠ 2) {b : ℚ_[p]ˣ}
    (h : ∀ a : ℚ_[p]ˣ, padicHilbertSymbol p a b = 1) : IsSquare b := by
  obtain ⟨β, v, hb⟩ := exists_zpow_mul_unit b
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  -- A unit of `ℤ_[p]` whose residue is not a square.
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare hchar
  obtain ⟨w, hw⟩ := ZMod.ringHom_surjective PadicInt.toZMod n
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn ⟨0, by rw [mul_zero]⟩
  have hwu : IsUnit w := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, hw]
    exact hn0
  -- `β` is even.
  have hβ : Even β := by
    have h1 := h (unitZpToQp hwu.unit)
    rw [padicHilbertSymbol.eq_formula_of_ne_two hp2 _ _ _ _ _ _ (coe_unitZpToQp _) hb,
      IsUnit.unit_spec, hw, legendreSym_toZMod_val', quadraticChar_neg_one_iff_not_isSquare.2 hn]
      at h1
    simp only [zero_mul, Int.natAbs_zero, pow_zero, one_mul, mul_one] at h1
    have h2 := (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)).1 h1
    exact Int.natAbs_even.1 h2
  -- The residue of `v` is a square.
  have hv : IsSquare (PadicInt.toZMod (v : ℤ_[p])) := by
    have h1 := h (Units.mk0 (p : ℚ_[p]) bil_p_ne_zero)
    rw [padicHilbertSymbol.eq_formula_of_ne_two hp2 _ _ _ _ _ _ coe_p_unit hb,
      pow_natAbs_eq_ite (by norm_num), pow_natAbs_eq_ite (legendreSym_unit_sq 1)] at h1
    have hev : Even (β * (((p - 1) / 2 : ℕ) : ℤ)) := by
      rw [Int.even_mul]
      exact Or.inl hβ
    simp only [one_mul, hev, hβ, ↓reduceIte, Int.natAbs_one, pow_one, mul_one] at h1
    rw [legendreSym_toZMod_val'] at h1
    exact (quadraticChar_one_iff_isSquare (RingHom.isUnit_map _ v.isUnit).ne_zero).1 h1
  exact isSquare_of_even_of_isSquare hb hβ
    (PadicInt.isSquare_of_isSquare_toZMod hp2 (RingHom.isUnit_map _ v.isUnit).ne_zero hv)

private theorem isUnit_five : IsUnit (5 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
  have h' : ‖((5 : ℤ) : ℤ_[2])‖ < 1 := by exact_mod_cast h
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
  omega

/-- Nondegeneracy for $p = 2$. -/
private theorem isSquare_of_forall_two {b : ℚ_[2]ˣ}
    (h : ∀ a : ℚ_[2]ˣ, padicHilbertSymbol 2 a b = 1) : IsSquare b := by
  obtain ⟨β, v, hb⟩ := exists_zpow_mul_unit b
  have hb2 : (b : ℚ_[2]) = (2 : ℚ_[2]) ^ β * ((v : ℤ_[2]) : ℚ_[2]) := by exact_mod_cast hb
  have hv := oddRes8_of_isUnit v.isUnit
  set rv : ZMod 8 := PadicInt.toZModPow 3 (v : ℤ_[2]) with hrv
  have even_of : ∀ n : ℕ, (-1 : ℤ) ^ n = 1 → Even n := fun n hn =>
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)).1 hn
  have h0 : ∀ u : ℤ_[2]ˣ, (unitZpToQp u : ℚ_[2]) = (2 : ℚ_[2]) ^ (0 : ℤ) * ((u : ℤ_[2]) : ℚ_[2]) :=
    fun u => by exact_mod_cast coe_unitZpToQp u
  -- Against `5`: `β` is even.
  have hβ : Even β.natAbs := by
    have h1 := h (unitZpToQp isUnit_five.unit)
    rw [padicHilbertSymbol.eq_formula_two _ _ _ _ _ _ (h0 _) hb2, IsUnit.unit_spec] at h1
    have h2 := even_of _ h1
    have h5 : (PadicInt.toZModPow 3 (5 : ℤ_[2])).val = 5 := by
      rw [map_ofNat]
      rfl
    rw [h5] at h2
    simp only [Int.natAbs_zero, zero_mul, add_zero] at h2
    rw [Nat.even_iff] at h2 ⊢
    norm_num at h2
    omega
  -- Against `-1`: `ε(v) = 0`.
  have he : Even ((rv.val - 1) / 2) := by
    have h1 := h (unitZpToQp (-1 : ℤ_[2]ˣ))
    rw [padicHilbertSymbol.eq_formula_two _ _ _ _ _ _ (h0 _) hb2] at h1
    have h2 := even_of _ h1
    have h7 : (PadicInt.toZModPow 3 (((-1 : ℤ_[2]ˣ) : ℤ_[2]))).val = 7 := by
      rw [Units.val_neg, Units.val_one, map_neg, map_one]
      rfl
    rw [h7, ← hrv] at h2
    simp only [Int.natAbs_zero, zero_mul, add_zero] at h2
    rw [Nat.even_iff] at h2 ⊢
    norm_num at h2
    omega
  -- Against `2`: `ω(v) = 0`.
  have hw : Even ((rv.val ^ 2 - 1) / 8) := by
    have h1 := h (Units.mk0 (2 : ℚ_[2]) two_ne_zero)
    have hc : (Units.mk0 (2 : ℚ_[2]) two_ne_zero : ℚ_[2]) =
        (2 : ℚ_[2]) ^ (1 : ℤ) * (((1 : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) := by
      rw [Units.val_mk0, zpow_one, Units.val_one, PadicInt.coe_one, mul_one]
    rw [padicHilbertSymbol.eq_formula_two _ _ _ _ _ _ hc hb2, Units.val_one, map_one] at h1
    have h2 := even_of _ h1
    have hone : (1 : ZMod 8).val = 1 := rfl
    rw [hone, ← hrv] at h2
    simpa using h2
  have hv1 : rv = 1 := by
    clear_value rv
    unfold OddRes8 at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd he (by decide)
    · exact absurd hw (by decide)
    · exact absurd he (by decide)
  exact isSquare_of_even_of_isSquare hb (Int.natAbs_even.1 hβ)
    (PadicInt.isSquare_of_toZModPow_three_eq_one hv1)

end HilbertSymbol

namespace padicHilbertSymbol

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The $p$-adic Hilbert symbol is nondegenerate.** Let $p$ be a prime and let
$b \in \mathbb{Q}_p$ be nonzero. Then $(a, b)_p = 1$ for every nonzero $a \in \mathbb{Q}_p$ if and
only if $b$ is a square in $\mathbb{Q}_p^\times$.

Source: J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
Chapter III, §1.2, Theorem 2, p. 20: "if $b \in k^*$ is such that $(a, b) = 1$ for all
$a \in k^*$, one has $b \in k^{*2}$", in the case $k = \mathbb{Q}_p$. The converse is
Proposition 2 i), p. 19. -/
theorem forall_eq_one_iff_isSquare (b : ℚ_[p]ˣ) :
    (∀ a : ℚ_[p]ˣ, padicHilbertSymbol p a b = 1) ↔ IsSquare b := by
  constructor
  · intro h
    by_cases hp2 : p = 2
    · subst hp2
      exact isSquare_of_forall_two h
    · exact isSquare_of_forall_of_ne_two hp2 h
  · rintro ⟨c, rfl⟩ a
    unfold padicHilbertSymbol
    have hc : c * c = 1 * c ^ 2 := by rw [one_mul, pow_two]
    rw [hilbertSymbol.comm, hc, hilbertSymbol.mul_sq_left, hilbertSymbol.eq_one_iff]
    exact ⟨1, 0, by simp⟩

end padicHilbertSymbol
