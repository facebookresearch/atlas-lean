/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Hilbert symbols of p-adic integer units

For an odd prime p, the p-adic Hilbert symbol is trivial on p-adic integer units. The proof finds
a solution modulo p by Chevalley-Warning and lifts it using Hensel lemma.
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbol

/-- **Inclusion of $p$-adic integer units.** For a prime $p$, this is the map from the units of
$\mathbb{Z}_p$ to the units of $\mathbb{Q}_p$ induced by the inclusion
$\mathbb{Z}_p \subseteq \mathbb{Q}_p$. -/
noncomputable def unitZpToQp {p : ℕ} [Fact (Nat.Prime p)]
    (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom u

/-- **Value of the inclusion of $p$-adic integer units.** For a prime $p$ and a unit $u$ of
$\mathbb{Z}_p$, the image of $u$ under the inclusion of the units of $\mathbb{Z}_p$ into the units
of $\mathbb{Q}_p$, viewed as an element of $\mathbb{Q}_p$, equals $u$ viewed as an element of
$\mathbb{Q}_p$. -/
lemma unitZpToQp_coe {p : ℕ} [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ) :
    (unitZpToQp u : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) := by
  rw [unitZpToQp, Units.coe_map]
  exact PadicInt.Coe.ringHom_apply (u : ℤ_[p])

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **For odd $p$, a binary unit form over $\mathbb{Z}_p$ represents a unit square.** Let $p$ be an
odd prime and let $u, v$ be units of $\mathbb{Z}_p$. Then there are $x_0, y_0 \in \mathbb{Z}_p$ and
a unit $z_0$ of $\mathbb{Z}_p$ with $z_0^2 = u x_0^2 + v y_0^2$.

Source: Lemma 10.5, key step. -/
theorem chevalley_warning_hensel_lift (p : ℕ) [Fact p.Prime]
    (hp_odd : p ≠ 2) (u v : ℤ_[p]ˣ) :
    ∃ (x₀ y₀ : ℤ_[p]) (z₀ : ℤ_[p]ˣ),
      (z₀ : ℤ_[p]) ^ 2 = (u : ℤ_[p]) * x₀ ^ 2 + (v : ℤ_[p]) * y₀ ^ 2 := by
  have hp := Fact.out (p := Nat.Prime p)
  have hu_unit : IsUnit (PadicInt.toZMod (u : ℤ_[p])) :=
    RingHom.isUnit_map PadicInt.toZMod u.isUnit
  have hv_unit : IsUnit (PadicInt.toZMod (v : ℤ_[p])) :=
    RingHom.isUnit_map PadicInt.toZMod v.isUnit
  set u_bar := hu_unit.unit
  set v_bar := hv_unit.unit
  have hu_bar_val : (u_bar : ZMod p) = PadicInt.toZMod (u : ℤ_[p]) := by
    simp [u_bar, IsUnit.unit_spec]
  have hv_bar_val : (v_bar : ZMod p) = PadicInt.toZMod (v : ℤ_[p]) := by
    simp [v_bar, IsUnit.unit_spec]
  open Polynomial in
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card p]
    exact Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp hp_odd)
  have hu_ne : (u_bar : ZMod p) ≠ 0 := Units.ne_zero _
  have hv_ne : (v_bar : ZMod p) ≠ 0 := Units.ne_zero _
  open Polynomial in
  have hf : (C (u_bar : ZMod p) * X ^ 2 - C 1).degree = 2 := by
    rw [degree_sub_eq_left_of_degree_lt]
    · simp [degree_C_mul_X_pow 2 hu_ne]
    · rw [degree_C_mul_X_pow 2 hu_ne]; simp
  open Polynomial in
  have hg : (C (v_bar : ZMod p) * X ^ 2).degree = 2 := by
    simp [degree_C_mul_X_pow 2 hv_ne]
  open Polynomial in
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  open Polynomial in
  have hab' : (u_bar : ZMod p) * a ^ 2 + (v_bar : ZMod p) * b ^ 2 = 1 := by
    have : (u_bar : ZMod p) * a ^ 2 - 1 + (v_bar : ZMod p) * b ^ 2 = 0 := by
      convert hab using 1
      simp [eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination this
  obtain ⟨a_lift, ha_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod a
  obtain ⟨b_lift, hb_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod b
  set c := (u : ℤ_[p]) * a_lift ^ 2 + (v : ℤ_[p]) * b_lift ^ 2 with hc_def
  have hc_mod : PadicInt.toZMod c = 1 := by
    simp only [hc_def, map_add, map_mul, map_pow, ha_lift, hb_lift,
      ← hu_bar_val, ← hv_bar_val]
    exact hab'
  have hnorm_1_sub_c : ‖(1 : ℤ_[p]) - c‖ < 1 := by
    have hmem : (1 - c) ∈ RingHom.ker PadicInt.toZMod :=
      show PadicInt.toZMod (1 - c) = 0 by simp [map_sub, map_one, hc_mod]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hmem
    exact (PadicInt.norm_lt_one_iff_dvd _).2 hmem
  have hnorm_two : ‖(2 : ℤ_[p])‖ = 1 := by
    have h1 : ‖(2 : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ¬ (‖(2 : ℤ_[p])‖ < 1) := by
      rw [show (2 : ℤ_[p]) = ((2 : ℤ) : ℤ_[p]) from by push_cast; ring]
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      intro hdvd
      have h3 : p ∣ 2 := by exact_mod_cast hdvd
      have h4 := Nat.le_of_dvd (by norm_num) h3
      have h5 := hp.two_le
      omega
    linarith
  open Polynomial in
  have h_aeval : Polynomial.aeval (1 : ℤ_[p]) (X ^ 2 - C c) = 1 - c := by
    simp [aeval_def]
  open Polynomial in
  have h_deriv : Polynomial.aeval (1 : ℤ_[p])
      (Polynomial.derivative (X ^ 2 - C c)) = 2 := by
    simp [derivative_sub, derivative_pow, derivative_C, derivative_X,
      aeval_def]
  open Polynomial in
  have hensel_hyp : ‖Polynomial.aeval (1 : ℤ_[p]) (X ^ 2 - C c)‖ <
      ‖Polynomial.aeval (1 : ℤ_[p])
        (Polynomial.derivative (X ^ 2 - C c))‖ ^ 2 := by
    rw [h_aeval, h_deriv, hnorm_two, one_pow]
    exact hnorm_1_sub_c
  open Polynomial in
  obtain ⟨z₀, hz₀_eval, hz₀_close, _, _⟩ := hensels_lemma hensel_hyp
  open Polynomial in
  have hz₀_sq : z₀ ^ 2 = c := by
    simp [aeval_def] at hz₀_eval
    linear_combination hz₀_eval
  open Polynomial in
  have hz₀_close' : ‖z₀ - 1‖ < 1 := by
    have : ‖z₀ - 1‖ < ‖Polynomial.aeval (1 : ℤ_[p])
        (Polynomial.derivative (X ^ 2 - C c))‖ := hz₀_close
    rw [h_deriv, hnorm_two] at this
    exact this
  have hz₀_unit : IsUnit z₀ := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖(1 : ℤ_[p])‖ = 1 := by simp
    have hne : ‖z₀ - 1‖ ≠ ‖(1 : ℤ_[p])‖ := by
      rw [h1]; exact ne_of_lt hz₀_close'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    rw [sub_add_cancel] at this
    rw [this, h1, max_eq_right (le_of_lt hz₀_close')]
  refine ⟨a_lift, b_lift, hz₀_unit.unit, ?_⟩
  rw [IsUnit.unit_spec, hz₀_sq]

/-- **The Hilbert symbol of two $p$-adic units is trivial for odd $p$.** Let $p$ be an odd prime
and let $u, v$ be units of $\mathbb{Z}_p$. Then the $p$-adic Hilbert symbol of $u$ and $v$, viewed
as units of $\mathbb{Q}_p$, equals $1$.

Source: Lemma 10.5. -/
theorem hilbert_symbol_units_eq_one_of_odd (p : ℕ) [Fact p.Prime]
    (hp_odd : p ≠ 2) (u v : ℤ_[p]ˣ) :
    padicHilbertSymbol p (unitZpToQp u) (unitZpToQp v) = 1 := by
  rw [padicHilbertSymbol.eq_one_iff]
  obtain ⟨x₀, y₀, z₀, hz⟩ := chevalley_warning_hensel_lift p hp_odd u v
  have hz_qp : ((z₀ : ℤ_[p]) : ℚ_[p]) ^ 2 =
      ((u : ℤ_[p]) : ℚ_[p]) * ((x₀ : ℚ_[p])) ^ 2 +
      ((v : ℤ_[p]) : ℚ_[p]) * ((y₀ : ℚ_[p])) ^ 2 := by
    have := congrArg (PadicInt.Coe.ringHom (p := p)) hz
    simp only [map_pow, map_mul, map_add] at this
    exact this
  have hz_ne : ((z₀ : ℤ_[p]) : ℚ_[p]) ≠ 0 := by simp [z₀.ne_zero]
  refine ⟨↑x₀ / ↑(z₀ : ℤ_[p]), ↑y₀ / ↑(z₀ : ℤ_[p]), ?_⟩
  rw [unitZpToQp_coe, unitZpToQp_coe,
    div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
    div_eq_one_iff_eq (pow_ne_zero 2 hz_ne)]
  exact hz_qp.symm

end HilbertSymbol
