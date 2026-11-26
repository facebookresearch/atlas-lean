/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.Units
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The formula for the $p$-adic Hilbert symbol at an odd prime

For an odd prime $p$, write nonzero $a, b \in \mathbb{Q}_p$ as $a = p^\alpha u$ and
$b = p^\beta v$ with $\alpha, \beta \in \mathbb{Z}$ and $u, v$ units of $\mathbb{Z}_p$. Then
$$(a, b)_p = (-1)^{\alpha \beta \varepsilon(p)} \left(\frac{\bar u}{p}\right)^{\beta}
  \left(\frac{\bar v}{p}\right)^{\alpha},$$
where $\varepsilon(p)$ is the class of $(p - 1)/2$ modulo $2$ and $\bar u, \bar v$ are the
residues of $u, v$ modulo $p$ (J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2,
Theorem 1, p. 20).

The proof reduces $\alpha$ and $\beta$ modulo $2$, as the symbol only depends on square classes,
and computes the four remaining cases directly: $(u, v)_p = 1$, $(pu, v)_p = (\bar v / p)$,
$(u, pv)_p = (\bar u / p)$ and $(pu, pv)_p = (-\bar u \bar v / p)$. The negative directions clear
denominators and descend modulo $p$; the positive ones use that a unit of $\mathbb{Z}_p$ whose
residue is a square is a square (Hensel's lemma), and that a binary form which represents $0$
nontrivially represents $1$.

On the way it records that the Hilbert symbol is symmetric, only depends on square classes, and
agrees with Serre's definition through nontrivial zeros of $z^2 - a x^2 - b y^2$.
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbol

variable {F : Type*} [Field F]

/-- Solvability of $A x^2 + B y^2 = 1$ for elements of a field, not necessarily nonzero. -/
private def Sol (A B : F) : Prop :=
  ∃ x y : F, A * x ^ 2 + B * y ^ 2 = 1

private theorem sol_comm {A B : F} : Sol A B ↔ Sol B A :=
  ⟨fun ⟨x, y, h⟩ => ⟨y, x, by linear_combination h⟩,
    fun ⟨x, y, h⟩ => ⟨y, x, by linear_combination h⟩⟩

private theorem sol_mul_sq {A B c : F} (hc : c ≠ 0) : Sol (A * c ^ 2) B ↔ Sol A B := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨c * x, y, by linear_combination h⟩
  · rintro ⟨x, y, h⟩
    refine ⟨x / c, y, ?_⟩
    have : A * c ^ 2 * (x / c) ^ 2 = A * x ^ 2 := by field_simp
    linear_combination h + this

/-- A binary form that represents `0` through `t ≠ 0` represents `1`. -/
private theorem sol_of_eq_neg_mul_sq {A B t : F} (h2 : (2 : F) ≠ 0) (hA : A ≠ 0) (ht : t ≠ 0)
    (hB : B = -(A * t ^ 2)) : Sol A B := by
  refine ⟨(1 + A⁻¹) / 2, (A⁻¹ - 1) / (2 * t), ?_⟩
  subst hB
  field_simp
  ring

end HilbertSymbol

open HilbertSymbol

namespace hilbertSymbol

variable {F : Type*} [Field F]

private theorem eq_iff_isSolvable_iff {a b a' b' : Fˣ}
    (h : HilbertSymbol.IsSolvable F a b ↔ HilbertSymbol.IsSolvable F a' b') :
    hilbertSymbol F a b = hilbertSymbol F a' b' := by
  by_cases hs : HilbertSymbol.IsSolvable F a b
  · rw [eq_one_iff.2 hs, eq_one_iff.2 (h.1 hs)]
  · rw [eq_neg_one_iff.2 hs, eq_neg_one_iff.2 (fun h' => hs (h.2 h'))]

theorem comm (a b : Fˣ) : hilbertSymbol F a b = hilbertSymbol F b a :=
  eq_iff_isSolvable_iff sol_comm

theorem mul_sq_left (a b c : Fˣ) : hilbertSymbol F (a * c ^ 2) b = hilbertSymbol F a b := by
  refine eq_iff_isSolvable_iff ?_
  change Sol _ _ ↔ Sol _ _
  rw [Units.val_mul, Units.val_pow_eq_pow_val]
  exact sol_mul_sq c.ne_zero

/-- **The Hilbert symbol through nontrivial zeros of a ternary form.** Let $F$ be a field in which
$2 \neq 0$ and let $a, b \in F$ be nonzero. Then the Hilbert symbol $(a, b)_F$ equals $1$ if and
only if $z^2 - a x^2 - b y^2 = 0$ for some $(z, x, y) \in F^3$ other than $(0, 0, 0)$. -/
theorem eq_one_iff_exists_ternary_eq_zero (h2 : (2 : F) ≠ 0) (a b : Fˣ) :
    hilbertSymbol F a b = 1 ↔
      ∃ z x y : F, ¬(z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
  rw [eq_one_iff]
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨1, x, y, fun h' => one_ne_zero h'.1, by linear_combination -h⟩
  · rintro ⟨z, x, y, hne, h⟩
    have ha : (a : F) ≠ 0 := a.ne_zero
    have hb : (b : F) ≠ 0 := b.ne_zero
    by_cases hz : z = 0
    · subst hz
      have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by
          have : (a : F) * x ^ 2 = 0 := by linear_combination -h
          simpa [ha] using this
        exact hne ⟨rfl, hx, rfl⟩
      have hx : x ≠ 0 := by
        rintro rfl
        have : (b : F) * y ^ 2 = 0 := by linear_combination -h
        simp [hb, hy] at this
      refine sol_of_eq_neg_mul_sq (t := x / y) h2 ha (div_ne_zero hx hy) ?_
      field_simp
      linear_combination -h
    · refine ⟨x / z, y / z, ?_⟩
      field_simp
      linear_combination -h

end hilbertSymbol

namespace HilbertSymbol

variable {p : ℕ} [hp : Fact p.Prime]

private theorem norm_lt_one_iff_toZMod_eq_zero (x : ℤ_[p]) :
    ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton,
    ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]

private theorem norm_eq_one_of_toZMod_ne_zero {x : ℤ_[p]} (hx : PadicInt.toZMod x ≠ 0) :
    ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one x)
    (not_lt.1 fun h => hx ((norm_lt_one_iff_toZMod_eq_zero x).1 h))

private theorem exists_eq_p_mul_of_toZMod_eq_zero {x : ℤ_[p]} (hx : PadicInt.toZMod x = 0) :
    ∃ y : ℤ_[p], x = p * y := by
  have := (norm_lt_one_iff_toZMod_eq_zero x).2 hx
  exact (PadicInt.norm_lt_one_iff_dvd x).1 this

private theorem toZMod_p : PadicInt.toZMod (p : ℤ_[p]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

private theorem p_ne_zero : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero

private theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := hp.out.two_le
  omega

end HilbertSymbol

namespace PadicInt

open HilbertSymbol

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Units of $\mathbb{Z}_p$ with square residues are squares, for odd $p$.** Let $p$ be an odd
prime and let $w \in \mathbb{Z}_p$ have a nonzero residue $\bar w$ modulo $p$. If $\bar w$ is a
square in $\mathbb{Z}/p\mathbb{Z}$, then $w$ is a square in $\mathbb{Z}_p$. -/
theorem isSquare_of_isSquare_toZMod (hp2 : p ≠ 2) {w : ℤ_[p]}
    (hw0 : PadicInt.toZMod w ≠ 0) (hw : IsSquare (PadicInt.toZMod w)) : IsSquare w := by
  obtain ⟨s, hs⟩ := hw
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective PadicInt.toZMod s
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hw0 (by simpa using hs)
  have ha1 : ‖a‖ = 1 := norm_eq_one_of_toZMod_ne_zero (by rw [ha]; exact hs0)
  have h21 : ‖(2 : ℤ_[p])‖ = 1 :=
    norm_eq_one_of_toZMod_ne_zero (by rw [map_ofNat]; exact two_ne_zero_zmod hp2)
  open Polynomial in
  have h_eval : Polynomial.aeval a (X ^ 2 - C w) = a ^ 2 - w := by simp [aeval_def]
  open Polynomial in
  have h_der : Polynomial.aeval a (Polynomial.derivative (X ^ 2 - C w)) = 2 * a := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul,
      Nat.cast_ofNat, map_ofNat]
    simp
  open Polynomial in
  have hhyp : ‖Polynomial.aeval a (X ^ 2 - C w)‖ <
      ‖Polynomial.aeval a (Polynomial.derivative (X ^ 2 - C w))‖ ^ 2 := by
    rw [h_eval, h_der, norm_mul, h21, ha1, one_mul, one_pow,
      norm_lt_one_iff_toZMod_eq_zero, map_sub, map_pow, ha, hs]
    ring
  open Polynomial in
  obtain ⟨z, hz, -⟩ := hensels_lemma hhyp
  refine ⟨z, ?_⟩
  simp [aeval_def] at hz
  linear_combination -hz

end PadicInt

namespace HilbertSymbol

variable {p : ℕ} [hp : Fact p.Prime]

/-- Clearing denominators of two $p$-adic numbers by a common power of $p$. -/
private theorem exists_pow_mul_mem (x y : ℚ_[p]) :
    ∃ (N : ℕ) (X Y : ℤ_[p]), (X : ℚ_[p]) = (p : ℚ_[p]) ^ N * x ∧
      (Y : ℚ_[p]) = (p : ℚ_[p]) ^ N * y := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max ‖x‖ ‖y‖) hp1
  have hpos : (0 : ℝ) < (p : ℝ) ^ N := pow_pos (by linarith) N
  have key : ∀ q : ℚ_[p], ‖q‖ ≤ max ‖x‖ ‖y‖ → ‖(p : ℚ_[p]) ^ N * q‖ ≤ 1 := by
    intro q hq
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    rw [inv_mul_le_iff₀ hpos, mul_one]
    linarith
  exact ⟨N, ⟨_, key x (le_max_left _ _)⟩, ⟨_, key y (le_max_right _ _)⟩, rfl, rfl⟩

/-- Descent for $(pu, v)_p$: an integral solution of $p u X^2 + v Y^2 = p^{2N}$ forces $\bar v$ to
be a square. -/
private theorem isSquare_of_p_mul_sq_add_sq (u v : ℤ_[p]ˣ) :
    ∀ (N : ℕ) (X Y : ℤ_[p]),
      (p : ℤ_[p]) * u * X ^ 2 + v * Y ^ 2 = (p : ℤ_[p]) ^ (2 * N) →
        IsSquare (PadicInt.toZMod (v : ℤ_[p])) := by
  have hv0 : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 := (RingHom.isUnit_map _ v.isUnit).ne_zero
  have hu0 : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := (RingHom.isUnit_map _ u.isUnit).ne_zero
  intro N
  induction N with
  | zero =>
    intro X Y h
    have h' := congrArg PadicInt.toZMod h
    simp only [map_add, map_mul, map_pow, toZMod_p, mul_zero, pow_zero, map_one,
      zero_mul, zero_add] at h'
    have hY : PadicInt.toZMod Y ≠ 0 := by
      rintro hY
      rw [hY] at h'
      simp at h'
    refine ⟨(PadicInt.toZMod Y)⁻¹, ?_⟩
    field_simp
    linear_combination h'
  | succ N ih =>
    intro X Y h
    have h' := congrArg PadicInt.toZMod h
    simp only [map_add, map_mul, map_pow, toZMod_p, zero_mul, zero_add] at h'
    rw [zero_pow (by omega)] at h'
    have hY : PadicInt.toZMod Y = 0 := by
      simpa [hv0] using h'
    obtain ⟨Y', rfl⟩ := exists_eq_p_mul_of_toZMod_eq_zero hY
    have h2 : (p : ℤ_[p]) * (u * X ^ 2) = (p : ℤ_[p]) * ((p : ℤ_[p]) ^ (2 * N + 1) -
        p * v * Y' ^ 2) := by
      linear_combination h
    have h3 := mul_left_cancel₀ p_ne_zero h2
    have h3' := congrArg PadicInt.toZMod h3
    simp only [map_sub, map_mul, map_pow, toZMod_p, zero_mul, sub_zero] at h3'
    rw [zero_pow (by omega)] at h3'
    have hX : PadicInt.toZMod X = 0 := by
      simpa [hu0] using h3'
    obtain ⟨X', rfl⟩ := exists_eq_p_mul_of_toZMod_eq_zero hX
    refine ih X' Y' (mul_left_cancel₀ (pow_ne_zero 2 p_ne_zero) ?_)
    linear_combination h

/-- Descent for $(pu, pv)_p$: an integral solution of $p u X^2 + p v Y^2 = p^{2N}$ forces
$-\bar u \bar v$ to be a square. -/
private theorem isSquare_of_p_mul_sq_add_p_mul_sq (u v : ℤ_[p]ˣ) :
    ∀ (N : ℕ) (X Y : ℤ_[p]),
      (p : ℤ_[p]) * u * X ^ 2 + p * v * Y ^ 2 = (p : ℤ_[p]) ^ (2 * N) →
        IsSquare (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p]))) := by
  have hu0 : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := (RingHom.isUnit_map _ u.isUnit).ne_zero
  intro N
  induction N with
  | zero =>
    intro X Y h
    have h' := congrArg PadicInt.toZMod h
    simp at h'
  | succ N ih =>
    intro X Y h
    have h2 : (p : ℤ_[p]) * (u * X ^ 2 + v * Y ^ 2) = (p : ℤ_[p]) * (p : ℤ_[p]) ^ (2 * N + 1) := by
      linear_combination h
    have h3 := mul_left_cancel₀ p_ne_zero h2
    have h3' := congrArg PadicInt.toZMod h3
    simp only [map_add, map_mul, map_pow, toZMod_p] at h3'
    rw [zero_pow (by omega)] at h3'
    by_cases hY : PadicInt.toZMod Y = 0
    · have hX : PadicInt.toZMod X = 0 := by
        rw [hY] at h3'
        simpa [hu0] using h3'
      obtain ⟨X', rfl⟩ := exists_eq_p_mul_of_toZMod_eq_zero hX
      obtain ⟨Y', rfl⟩ := exists_eq_p_mul_of_toZMod_eq_zero hY
      refine ih X' Y' (mul_left_cancel₀ (pow_ne_zero 2 p_ne_zero) ?_)
      linear_combination h
    · refine ⟨PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod X / PadicInt.toZMod Y, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hY hY)]
      linear_combination (-PadicInt.toZMod (u : ℤ_[p])) * h3'

private theorem coe_unit_ne_zero (u : ℤ_[p]ˣ) : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 :=
  PadicInt.coe_ne_zero.2 u.ne_zero

private theorem p_ne_zero' : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero

/-- The case $(u, v)_p$. -/
private theorem sol_units (hp2 : p ≠ 2) (u v : ℤ_[p]ˣ) :
    Sol ((u : ℤ_[p]) : ℚ_[p]) ((v : ℤ_[p]) : ℚ_[p]) := by
  have h := hilbert_symbol_units_eq_one_of_odd p hp2 u v
  rw [padicHilbertSymbol.eq_one_iff, unitZpToQp_coe, unitZpToQp_coe] at h
  exact h

/-- The case $(pu, v)_p$. -/
private theorem sol_p_mul_iff (hp2 : p ≠ 2) (u v : ℤ_[p]ˣ) :
    Sol ((p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p])) ((v : ℤ_[p]) : ℚ_[p]) ↔
      IsSquare (PadicInt.toZMod (v : ℤ_[p])) := by
  constructor
  · rintro ⟨x, y, h⟩
    obtain ⟨N, X, Y, hX, hY⟩ := exists_pow_mul_mem x y
    refine isSquare_of_p_mul_sq_add_sq u v N X Y ?_
    have hQ : (p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) * (X : ℚ_[p]) ^ 2 +
        ((v : ℤ_[p]) : ℚ_[p]) * (Y : ℚ_[p]) ^ 2 = (p : ℚ_[p]) ^ (2 * N) := by
      rw [hX, hY]
      linear_combination (p : ℚ_[p]) ^ (2 * N) * h
    apply PadicInt.ext
    push_cast
    exact hQ
  · intro hsq
    have hv0 : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 := (RingHom.isUnit_map _ v.isUnit).ne_zero
    obtain ⟨w, hw⟩ := PadicInt.isSquare_of_isSquare_toZMod hp2 hv0 hsq
    have hwQ : ((v : ℤ_[p]) : ℚ_[p]) = (w : ℚ_[p]) * (w : ℚ_[p]) := by
      rw [hw]; push_cast; ring
    have hw0 : (w : ℚ_[p]) ≠ 0 := by
      intro h0
      exact coe_unit_ne_zero v (by rw [hwQ, h0, zero_mul])
    refine ⟨0, (w : ℚ_[p])⁻¹, ?_⟩
    rw [hwQ]
    field_simp
    ring

/-- The case $(pu, pv)_p$. -/
private theorem sol_p_mul_p_mul_iff (hp2 : p ≠ 2) (u v : ℤ_[p]ˣ) :
    Sol ((p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p])) ((p : ℚ_[p]) * ((v : ℤ_[p]) : ℚ_[p])) ↔
      IsSquare (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p]))) := by
  have hu0 : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := (RingHom.isUnit_map _ u.isUnit).ne_zero
  have hv0 : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 := (RingHom.isUnit_map _ v.isUnit).ne_zero
  constructor
  · rintro ⟨x, y, h⟩
    obtain ⟨N, X, Y, hX, hY⟩ := exists_pow_mul_mem x y
    refine isSquare_of_p_mul_sq_add_p_mul_sq u v N X Y ?_
    have hQ : (p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) * (X : ℚ_[p]) ^ 2 +
        (p : ℚ_[p]) * ((v : ℤ_[p]) : ℚ_[p]) * (Y : ℚ_[p]) ^ 2 = (p : ℚ_[p]) ^ (2 * N) := by
      rw [hX, hY]
      linear_combination (p : ℚ_[p]) ^ (2 * N) * h
    apply PadicInt.ext
    push_cast
    exact hQ
  · intro hsq
    -- `-v/u` is a square in `ℤ_[p]`.
    set w : ℤ_[p] := -((v : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) with hw_def
    have huinv : PadicInt.toZMod ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * PadicInt.toZMod (u : ℤ_[p]) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hw0 : PadicInt.toZMod w ≠ 0 := by
      rw [hw_def, map_neg, map_mul, neg_ne_zero]
      exact mul_ne_zero hv0 (left_ne_zero_of_mul_eq_one huinv)
    have hwsq : IsSquare (PadicInt.toZMod w) := by
      obtain ⟨r, hr⟩ := hsq
      refine ⟨r * PadicInt.toZMod ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
      rw [hw_def, map_neg, map_mul]
      linear_combination (PadicInt.toZMod ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) ^ 2 * hr +
        PadicInt.toZMod (v : ℤ_[p]) * PadicInt.toZMod ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * huinv
    obtain ⟨t, ht⟩ := PadicInt.isSquare_of_isSquare_toZMod hp2 hw0 hwsq
    have hvt : (v : ℤ_[p]) = -((u : ℤ_[p]) * t ^ 2) := by
      have h1 : (u : ℤ_[p]) * w = -(v : ℤ_[p]) := by
        rw [hw_def]
        have := u.mul_inv
        linear_combination (-(v : ℤ_[p])) * this
      rw [ht] at h1
      linear_combination h1
    have ht0 : (t : ℚ_[p]) ≠ 0 := by
      intro h0
      apply coe_unit_ne_zero v
      have : ((v : ℤ_[p]) : ℚ_[p]) = -(((u : ℤ_[p]) : ℚ_[p]) * (t : ℚ_[p]) ^ 2) := by
        rw [hvt]; push_cast; ring
      rw [this, h0]; ring
    refine sol_of_eq_neg_mul_sq (t := (t : ℚ_[p])) ?_
      (mul_ne_zero p_ne_zero' (coe_unit_ne_zero u)) ht0 ?_
    · exact_mod_cast (two_ne_zero : (2 : ℚ_[p]) ≠ 0)
    · have : ((v : ℤ_[p]) : ℚ_[p]) = -(((u : ℤ_[p]) : ℚ_[p]) * (t : ℚ_[p]) ^ 2) := by
        rw [hvt]; push_cast; ring
      rw [this]; ring

/-- Reduction of the exponent modulo `2`. -/
private theorem zpow_eq_mul_sq (α : ℤ) :
    (p : ℚ_[p]) ^ α = (p : ℚ_[p]) ^ (α % 2) * ((p : ℚ_[p]) ^ (α / 2)) ^ 2 := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ p_ne_zero']
  congr 1
  push_cast
  omega

private theorem sol_reduce (α β : ℤ) (u v : ℤ_[p]ˣ) :
    Sol ((p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p])) ((p : ℚ_[p]) ^ β * ((v : ℤ_[p]) : ℚ_[p])) ↔
      Sol ((p : ℚ_[p]) ^ (α % 2) * ((u : ℤ_[p]) : ℚ_[p]))
        ((p : ℚ_[p]) ^ (β % 2) * ((v : ℤ_[p]) : ℚ_[p])) := by
  have hα : (p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (α % 2) * ((u : ℤ_[p]) : ℚ_[p]) * ((p : ℚ_[p]) ^ (α / 2)) ^ 2 := by
    rw [zpow_eq_mul_sq α]; ring
  have hβ : (p : ℚ_[p]) ^ β * ((v : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (β % 2) * ((v : ℤ_[p]) : ℚ_[p]) * ((p : ℚ_[p]) ^ (β / 2)) ^ 2 := by
    rw [zpow_eq_mul_sq β]; ring
  rw [hα, hβ, sol_mul_sq (zpow_ne_zero _ p_ne_zero'), sol_comm,
    sol_mul_sq (zpow_ne_zero _ p_ne_zero'), sol_comm]

/-- A sign raised to the absolute value of an integer only depends on its parity. -/
private theorem pow_natAbs_eq {s : ℤ} (hs : s ^ 2 = 1) (n : ℤ) :
    s ^ n.natAbs = if Even n then 1 else s := by
  split_ifs with h
  · obtain ⟨k, hk⟩ := Int.natAbs_even.2 h
    rw [hk, ← two_mul, pow_mul, hs, one_pow]
  · have h' : ¬Even n.natAbs := fun h' => h (Int.natAbs_even.1 h')
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 h'
    rw [hk, pow_succ, pow_mul, hs, one_pow, one_mul]

private theorem legendreSym_toZMod_val (x : ZMod p) :
    legendreSym p (x.val : ℤ) = quadraticChar (ZMod p) x := by
  rw [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val]

end HilbertSymbol

open HilbertSymbol

namespace padicHilbertSymbol

/-- **Formula for the $p$-adic Hilbert symbol at an odd prime.** Let $p$ be an odd prime and let
$a, b \in \mathbb{Q}_p$ be nonzero. Write $a = p^\alpha u$ and $b = p^\beta v$ with
$\alpha, \beta \in \mathbb{Z}$ and $u, v$ units of $\mathbb{Z}_p$, and let $\bar u, \bar v$ be the
residues of $u, v$ modulo $p$. Then the $p$-adic Hilbert symbol satisfies
$$(a, b)_p = (-1)^{\alpha \beta \varepsilon(p)} \left(\frac{\bar u}{p}\right)^{\beta}
  \left(\frac{\bar v}{p}\right)^{\alpha},$$
where $\varepsilon(p)$ is the class of $(p - 1)/2$ modulo $2$ and $\left(\frac{\cdot}{p}\right)$
is the Legendre symbol.
As these signs are $\pm 1$, the exponents $\alpha \beta \varepsilon(p)$, $\beta$ and $\alpha$ are
taken in absolute value, and the Legendre symbol of a residue is evaluated at its representative
in $\{0, \dots, p - 1\}$.

Source: J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
Chapter III, §1.2, Theorem 1, p. 20 (the case $p \neq 2$). Serre defines $(a, b) = 1$ by a nonzero
zero of $z^2 - a x^2 - b y^2$; this agrees with the definition used here by
`hilbertSymbol.eq_one_iff_exists_ternary_eq_zero`. -/
theorem eq_formula_of_ne_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (a b : ℚ_[p]ˣ) (α β : ℤ) (u v : ℤ_[p]ˣ)
    (ha : (a : ℚ_[p]) = (p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p]))
    (hb : (b : ℚ_[p]) = (p : ℚ_[p]) ^ β * ((v : ℤ_[p]) : ℚ_[p])) :
    padicHilbertSymbol p a b =
      (-1) ^ (α * β * ((p - 1) / 2 : ℕ)).natAbs *
        legendreSym p (PadicInt.toZMod (u : ℤ_[p])).val ^ β.natAbs *
        legendreSym p (PadicInt.toZMod (v : ℤ_[p])).val ^ α.natAbs := by
  set ub := PadicInt.toZMod (u : ℤ_[p]) with hub
  set vb := PadicInt.toZMod (v : ℤ_[p]) with hvb
  have hu0 : ub ≠ 0 := (RingHom.isUnit_map _ u.isUnit).ne_zero
  have hv0 : vb ≠ 0 := (RingHom.isUnit_map _ v.isUnit).ne_zero
  have hχu := quadraticChar_sq_one hu0
  have hχv := quadraticChar_sq_one hv0
  rw [legendreSym_toZMod_val, legendreSym_toZMod_val,
    pow_natAbs_eq (by norm_num) (α * β * ((p - 1) / 2 : ℕ)), pow_natAbs_eq hχu β,
    pow_natAbs_eq hχv α]
  -- The value of `(-1 / p)`.
  have hneg : quadraticChar (ZMod p) (-1) = if Even ((p - 1) / 2) then 1 else -1 := by
    have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
    have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_eq_neg_one_pow hodd]
    have : p / 2 = (p - 1) / 2 := by omega
    rw [this]
    split_ifs with h
    · exact h.neg_one_pow
    · exact (Nat.not_even_iff_odd.1 h).neg_one_pow
  -- Reduce to the value of `Sol`.
  have key : ∀ R : ℤ, (R = 1 ∨ R = -1) →
      (Sol (a : ℚ_[p]) (b : ℚ_[p]) ↔ R = 1) → padicHilbertSymbol p a b = R := by
    intro R hR hiff
    by_cases hs : Sol (a : ℚ_[p]) (b : ℚ_[p])
    · rw [(padicHilbertSymbol.eq_one_iff).2 hs, (hiff.1 hs)]
    · rw [(padicHilbertSymbol.eq_neg_one_iff).2 hs]
      rcases hR with hR | hR
      · exact absurd (hiff.2 hR) hs
      · exact hR.symm
  have hχ : ∀ x : ZMod p, x ≠ 0 →
      (quadraticChar (ZMod p) x = 1 ∨ quadraticChar (ZMod p) x = -1) := fun x hx =>
    quadraticChar_dichotomy hx
  have hsq : ∀ x : ZMod p, x ≠ 0 → (IsSquare x ↔ quadraticChar (ZMod p) x = 1) :=
    fun x hx => (quadraticChar_one_iff_isSquare hx).symm
  apply key
  · have pm_mul : ∀ x y : ℤ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) →
        (x * y = 1 ∨ x * y = -1) := by
      rintro x y (rfl | rfl) (rfl | rfl) <;> norm_num
    have pm_ite : ∀ (P : Prop) [Decidable P] (y : ℤ), (y = 1 ∨ y = -1) →
        ((if P then 1 else y) = 1 ∨ (if P then 1 else y) = -1) := by
      intro P _ y hy
      split_ifs
      · exact Or.inl rfl
      · exact hy
    exact pm_mul _ _ (pm_mul _ _ (pm_ite _ _ (Or.inr rfl)) (pm_ite _ _ (hχ _ hu0)))
      (pm_ite _ _ (hχ _ hv0))
  · rw [ha, hb, sol_reduce]
    have hαe : Even α ↔ α % 2 = 0 := Int.even_iff
    have hβe : Even β ↔ β % 2 = 0 := Int.even_iff
    rcases Int.emod_two_eq α with hα | hα <;> rcases Int.emod_two_eq β with hβ | hβ
    · -- `(u, v)`
      have hea : Even α := hαe.2 hα
      have heb : Even β := hβe.2 hβ
      simp only [hα, hβ, zpow_zero, one_mul, Int.even_mul, hea, heb, true_or, ite_true,
        mul_one, iff_true]
      exact sol_units hp2 u v
    · -- `(u, pv)`
      have hea : Even α := hαe.2 hα
      have heb : ¬Even β := by rw [hβe, hβ]; decide
      simp only [hα, hβ, zpow_zero, zpow_one, one_mul, Int.even_mul, hea, heb, true_or,
        ite_true, ite_false, one_mul, mul_one]
      rw [sol_comm, sol_p_mul_iff hp2 v u, hsq _ hu0]
    · -- `(pu, v)`
      have hea : ¬Even α := by rw [hαe, hα]; decide
      have heb : Even β := hβe.2 hβ
      simp only [hα, hβ, zpow_zero, zpow_one, one_mul, Int.even_mul, hea, heb, true_or,
        or_true, ite_true, ite_false, one_mul]
      rw [sol_p_mul_iff hp2 u v, hsq _ hv0]
    · -- `(pu, pv)`
      have hea : ¬Even α := by rw [hαe, hα]; decide
      have heb : ¬Even β := by rw [hβe, hβ]; decide
      simp only [hα, hβ, zpow_one, Int.even_mul, hea, heb, false_or, ite_false,
        Int.even_natCast]
      rw [sol_p_mul_p_mul_iff hp2 u v, hsq _ (neg_ne_zero.2 (mul_ne_zero hu0 hv0)),
        neg_eq_neg_one_mul, map_mul, map_mul, hneg]
      rcases hχ ub hu0 with h1 | h1 <;> rcases hχ vb hv0 with h2 | h2 <;>
        simp only [h1, h2] <;> split_ifs <;> norm_num

end padicHilbertSymbol
