/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ToggleSwitch
public import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Tactic.ComputeDegree
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Equilibrium count of the toggle switch for other Hill exponents

`MathlibExt.Biology.Dynamics.ToggleSwitch` sets up the Gardner–Cantor–Collins toggle switch

  `du/dt = α₁ / (1 + v ^ β) - u`,  `dv/dt = α₂ / (1 + u ^ γ) - v`

and counts its equilibria only for `β = 1`, `γ = 2` (the cubic `cubic a b`). This file treats two
further families of Hill exponents, writing `a = α₁ > 0`, `b = α₂ > 0`.

## `β = 1`, any `γ`

Eliminating `v = b / (1 + u ^ γ)` from `u (1 + v) = a`, the equilibria are in bijection with the
**positive** real roots of

  `equilibriumPolyOne a b γ = X ^ (γ + 1) - a X ^ γ + (1 + b) X - a`

(`isEquilibrium_one_iff`, `ncard_equilibria_one`); every equilibrium has `u > 0`. For odd `γ` the
polynomial can have negative roots, which are not equilibria. For `γ ≥ 1` it is monic of degree
`γ + 1` (`monic_equilibriumPolyOne`, `natDegree_equilibriumPolyOne`), and for `γ = 2` it is
T195's `cubic a b` (`eval_equilibriumPolyOne_two`). Hence:

* `one_le_ncard_equilibria_one`: there is at least one equilibrium (every `γ`);
* `ncard_equilibria_one_le_degree`: at most `γ + 1` equilibria (`γ ≥ 1`), the degree bound;
* `ncard_equilibria_one_le_three`: at most `3` equilibria (every `γ`), by Descartes' rule of
  signs (`Polynomial.roots_countP_pos_le_signVariations`): the polynomial has at most four nonzero
  coefficients, hence at most three sign changes. For `γ ≥ 3` this is sharper than the degree;
* `ncard_equilibria_one_one`: for `γ = 1` the equilibrium is unique.

## `β = γ = 2`

Eliminating `v = b / (1 + u²)` from `u (1 + v²) = a`, the equilibria are in bijection with the
positive real roots of the quintic

  `equilibriumPolyTwo a b = X⁵ - a X⁴ + 2 X³ - 2a X² + (1 + b²) X - a`

(`isEquilibrium_two_iff`, `ncard_equilibria_two`), monic of degree `5`
(`monic_equilibriumPolyTwo`, `natDegree_equilibriumPolyTwo`). Every real root is positive. Hence
there are between `1` and `5` equilibria (`one_le_ncard_equilibria_two`,
`ncard_equilibria_two_le_five`). The quintic has five sign changes, so Descartes' rule gives
nothing beyond the degree; whether four or five equilibria can actually occur is not decided here.

Stability of the equilibria for these exponents, the mirror family (`γ = 1`, any `β`, which
follows by swapping `u` and `v`) and other exponent pairs are not treated.

## References

* T. S. Gardner, C. R. Cantor and J. J. Collins, *Construction of a genetic toggle switch in
  Escherichia coli*, Nature 403 (2000) 339–342.
-/

@[expose] public section

open Set Polynomial

namespace MathlibExt.Biology.Dynamics.ToggleSwitch

/-! ### Positive roots of a real polynomial -/

section PositiveRoots

/-- The positive real roots of a nonzero polynomial form the finite set of positive elements of
its root multiset. -/
theorem setOf_pos_isRoot_eq {p : ℝ[X]} (hp : p ≠ 0) [DecidablePred (fun u : ℝ ↦ 0 < u)] :
    {u : ℝ | 0 < u ∧ p.IsRoot u} = ↑(p.roots.filter (fun u ↦ 0 < u)).toFinset := by
  classical
  ext u
  simp [mem_roots hp, and_comm]

theorem finite_setOf_pos_isRoot {p : ℝ[X]} (hp : p ≠ 0) :
    {u : ℝ | 0 < u ∧ p.IsRoot u}.Finite := by
  classical
  rw [setOf_pos_isRoot_eq hp]
  exact Finset.finite_toSet _

theorem ncard_setOf_pos_isRoot_le_natDegree {p : ℝ[X]} (hp : p ≠ 0) :
    {u : ℝ | 0 < u ∧ p.IsRoot u}.ncard ≤ p.natDegree := by
  classical
  rw [setOf_pos_isRoot_eq hp, ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans
    ((Multiset.card_le_card (Multiset.filter_le _ _)).trans (card_roots' p))

theorem ncard_setOf_pos_isRoot_le_signVariations {p : ℝ[X]} (hp : p ≠ 0) :
    {u : ℝ | 0 < u ∧ p.IsRoot u}.ncard ≤ p.signVariations := by
  classical
  refine le_trans ?_ (roots_countP_pos_le_signVariations p)
  rw [Multiset.countP_eq_card_filter, setOf_pos_isRoot_eq hp, ncard_coe_finset]
  exact Multiset.toFinset_card_le _

/-- A nonzero polynomial has fewer sign changes than nonzero coefficients. -/
theorem signVariations_add_one_le_card_support {p : ℝ[X]} (hp : p ≠ 0) :
    p.signVariations + 1 ≤ p.support.card := by
  induction hn : p.support.card generalizing p with
  | zero => exact absurd (card_support_eq_zero.1 hn) hp
  | succ n ih =>
    rw [signVariations_eq_eraseLead_add_ite hp]
    by_cases he : p.eraseLead = 0
    · have hl : SignType.sign p.leadingCoeff ≠ 0 := by simp [hp]
      simp [he, hl]
    · have hcard : p.eraseLead.support.card = n := by
        have := card_support_eraseLead_add_one hp
        omega
      have := ih he hcard
      split_ifs <;> omega

end PositiveRoots

/-! ### The case `β = 1`, any `γ` -/

section BetaOne

variable {a b : ℝ} {γ : ℕ}

/-- The equilibrium polynomial `X ^ (γ + 1) - a X ^ γ + (1 + b) X - a` of the `β = 1` toggle
switch. -/
noncomputable def equilibriumPolyOne (a b : ℝ) (γ : ℕ) : ℝ[X] :=
  X ^ (γ + 1) - C a * X ^ γ + C (1 + b) * X - C a

theorem eval_equilibriumPolyOne (a b : ℝ) (γ : ℕ) (u : ℝ) :
    (equilibriumPolyOne a b γ).eval u = u ^ (γ + 1) - a * u ^ γ + (1 + b) * u - a := by
  simp [equilibriumPolyOne]

/-- For `γ = 2` the equilibrium polynomial is the cubic of `ToggleSwitch`. -/
theorem eval_equilibriumPolyOne_two (a b u : ℝ) :
    (equilibriumPolyOne a b 2).eval u = cubic a b u := by
  rw [eval_equilibriumPolyOne]
  unfold cubic
  ring

theorem equilibriumPolyOne_ne_zero (ha : 0 < a) (b : ℝ) (γ : ℕ) : equilibriumPolyOne a b γ ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  rw [eval_equilibriumPolyOne, zero_pow (Nat.succ_ne_zero γ), eval_zero] at this
  nlinarith [mul_nonneg ha.le (pow_nonneg (le_refl (0 : ℝ)) γ)]

theorem natDegree_equilibriumPolyOne_sub_le (a b : ℝ) (hγ : 0 < γ) :
    (C a * X ^ γ - C (1 + b) * X + C a : ℝ[X]).natDegree ≤ γ := by
  have h1 : (C (1 + b) * X : ℝ[X]).natDegree ≤ γ :=
    ((natDegree_C_mul_le _ _).trans natDegree_X_le).trans hγ
  exact natDegree_add_le_of_degree_le
    ((natDegree_sub_le _ _).trans (max_le (natDegree_C_mul_X_pow_le a γ) h1))
    ((natDegree_C a).le.trans (Nat.zero_le _))

theorem equilibriumPolyOne_eq (a b : ℝ) (γ : ℕ) :
    equilibriumPolyOne a b γ = X ^ (γ + 1) - (C a * X ^ γ - C (1 + b) * X + C a) := by
  unfold equilibriumPolyOne
  ring

/-- **Degree `γ + 1`.** For `γ ≥ 1` the `β = 1` equilibrium polynomial has degree `γ + 1`. -/
theorem natDegree_equilibriumPolyOne (a b : ℝ) (hγ : 0 < γ) :
    (equilibriumPolyOne a b γ).natDegree = γ + 1 := by
  rw [equilibriumPolyOne_eq, natDegree_sub_eq_left_of_natDegree_lt] <;>
    rw [natDegree_X_pow]
  exact (natDegree_equilibriumPolyOne_sub_le a b hγ).trans_lt (Nat.lt_succ_self γ)

theorem monic_equilibriumPolyOne (a b : ℝ) (hγ : 0 < γ) : (equilibriumPolyOne a b γ).Monic := by
  rw [equilibriumPolyOne_eq]
  refine monic_X_pow_sub ?_
  exact (degree_le_of_natDegree_le (natDegree_equilibriumPolyOne_sub_le a b hγ)).trans_lt
    (by exact_mod_cast Nat.lt_succ_self γ)

/-- The `β = 1` equilibrium polynomial has at most four nonzero coefficients. -/
theorem card_support_equilibriumPolyOne_le (a b : ℝ) (γ : ℕ) :
    (equilibriumPolyOne a b γ).support.card ≤ 4 := by
  classical
  have hsub : (equilibriumPolyOne a b γ).support ⊆ {γ + 1, γ, 1, 0} := by
    intro n hn
    rw [mem_support_iff] at hn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    apply hn
    simp only [equilibriumPolyOne, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
      coeff_C]
    simp [h1, h2, h4, Ne.symm h3]
  exact (Finset.card_le_card hsub).trans Finset.card_le_four

theorem signVariations_equilibriumPolyOne_le (ha : 0 < a) (b : ℝ) (γ : ℕ) :
    (equilibriumPolyOne a b γ).signVariations ≤ 3 := by
  have := signVariations_add_one_le_card_support (equilibriumPolyOne_ne_zero ha b γ)
  have := card_support_equilibriumPolyOne_le a b γ
  omega

/-- Equilibria of the `β = 1` toggle switch are the points `(u, b / (1 + u ^ γ))` with `u` a
positive root of `equilibriumPolyOne a b γ`. -/
theorem isEquilibrium_one_iff (ha : 0 < a) (hb : 0 < b) {u v : ℝ} :
    IsEquilibrium a b 1 γ u v ↔
      0 < u ∧ (equilibriumPolyOne a b γ).IsRoot u ∧ v = b / (1 + u ^ γ) := by
  rw [IsRoot.def, eval_equilibriumPolyOne, pow_succ]
  constructor
  · rintro ⟨hu, hv, h1, h2⟩
    simp only [uDot, vDot, hill, pow_one, sub_eq_zero] at h1 h2
    have hv1 : 0 < 1 + v := by linarith
    have hug : 0 < 1 + u ^ γ := by positivity
    have hu0 : 0 < u := by rw [← h1]; positivity
    rw [div_eq_iff hv1.ne'] at h1
    refine ⟨hu0, ?_, h2.symm⟩
    rw [div_eq_iff hug.ne'] at h2
    linear_combination (-(1 + u ^ γ)) * h1 + u * h2
  · rintro ⟨hu, hr, rfl⟩
    have hug : 0 < 1 + u ^ γ := by positivity
    refine ⟨hu.le, by positivity, ?_, ?_⟩
    · simp only [uDot, hill, pow_one, sub_eq_zero]
      rw [div_eq_iff (by positivity)]
      field_simp
      linear_combination -hr
    · simp [vDot, hill]

theorem equilibria_one_eq_image (ha : 0 < a) (hb : 0 < b) :
    equilibria a b 1 γ =
      (fun u ↦ (u, b / (1 + u ^ γ))) '' {u | 0 < u ∧ (equilibriumPolyOne a b γ).IsRoot u} := by
  ext ⟨u, v⟩
  simp only [equilibria, mem_ofPred_eq, isEquilibrium_one_iff ha hb, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨hu, hr, rfl⟩
    exact ⟨u, ⟨hu, hr⟩, rfl, rfl⟩
  · rintro ⟨w, ⟨hw, hr⟩, rfl, rfl⟩
    exact ⟨hw, hr, rfl⟩

/-- The number of equilibria of the `β = 1` toggle switch is the number of positive roots of
`equilibriumPolyOne a b γ`. -/
theorem ncard_equilibria_one (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 1 γ).ncard = {u | 0 < u ∧ (equilibriumPolyOne a b γ).IsRoot u}.ncard := by
  rw [equilibria_one_eq_image ha hb]
  exact ncard_image_of_injective _ fun x y h ↦ (Prod.mk.inj h).1

/-- **At most `γ + 1` equilibria** (the degree bound). -/
theorem ncard_equilibria_one_le_degree (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ) :
    (equilibria a b 1 γ).ncard ≤ γ + 1 := by
  rw [ncard_equilibria_one ha hb, ← natDegree_equilibriumPolyOne a b hγ]
  exact ncard_setOf_pos_isRoot_le_natDegree (equilibriumPolyOne_ne_zero ha b γ)

/-- **At most three equilibria** for `β = 1` and every `γ` (Descartes' rule of signs). -/
theorem ncard_equilibria_one_le_three (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 1 γ).ncard ≤ 3 := by
  rw [ncard_equilibria_one ha hb]
  exact (ncard_setOf_pos_isRoot_le_signVariations (equilibriumPolyOne_ne_zero ha b γ)).trans
    (signVariations_equilibriumPolyOne_le ha b γ)

theorem exists_pos_isRoot_equilibriumPolyOne (ha : 0 < a) (hb : 0 < b) :
    ∃ u, 0 < u ∧ (equilibriumPolyOne a b γ).IsRoot u := by
  have h0 : (equilibriumPolyOne a b γ).eval 0 ≤ 0 := by
    rw [eval_equilibriumPolyOne, zero_pow (Nat.succ_ne_zero γ)]
    nlinarith [mul_nonneg ha.le (pow_nonneg (le_refl (0 : ℝ)) γ)]
  have h1 : 0 ≤ (equilibriumPolyOne a b γ).eval (a + 1) := by
    rw [eval_equilibriumPolyOne, pow_succ]
    have : 0 ≤ (a + 1) ^ γ := by positivity
    nlinarith
  obtain ⟨u, hmem, hu⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ a + 1)
    (equilibriumPolyOne a b γ).continuous.continuousOn ⟨h0, h1⟩
  refine ⟨u, hmem.1.lt_of_ne ?_, hu⟩
  rintro rfl
  change (equilibriumPolyOne a b γ).eval 0 = 0 at hu
  rw [eval_equilibriumPolyOne, zero_pow (Nat.succ_ne_zero γ)] at hu
  nlinarith [mul_nonneg ha.le (pow_nonneg (le_refl (0 : ℝ)) γ)]

/-- **At least one equilibrium** for `β = 1` and every `γ`. -/
theorem one_le_ncard_equilibria_one (ha : 0 < a) (hb : 0 < b) :
    1 ≤ (equilibria a b 1 γ).ncard := by
  rw [ncard_equilibria_one ha hb, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    ncard_pos (finite_setOf_pos_isRoot (equilibriumPolyOne_ne_zero ha b γ))]
  exact exists_pos_isRoot_equilibriumPolyOne ha hb

/-- **Uniqueness for `γ = 1`.** The `β = γ = 1` toggle switch has exactly one equilibrium. -/
theorem ncard_equilibria_one_one (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 1 1).ncard = 1 := by
  rw [ncard_equilibria_one ha hb]
  obtain ⟨r, hr0, hr⟩ := exists_pos_isRoot_equilibriumPolyOne (γ := 1) ha hb
  rw [ncard_eq_one]
  refine ⟨r, ?_⟩
  ext s
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hs0, hs⟩
    rw [IsRoot.def, eval_equilibriumPolyOne] at hr hs
    by_contra hsr
    have hsum : s + r + 1 + b - a = 0 := by
      have : (s - r) * (s + r + 1 + b - a) = 0 := by linear_combination hs - hr
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hsr)
    have : s * r = -a := by linear_combination r * hsum - hr
    nlinarith [mul_pos hs0 hr0]
  · rintro rfl
    exact ⟨hr0, hr⟩

end BetaOne

/-! ### The case `β = γ = 2` -/

section BetaGammaTwo

variable {a b : ℝ}

/-- The equilibrium quintic `X⁵ - a X⁴ + 2 X³ - 2a X² + (1 + b²) X - a` of the `β = γ = 2`
toggle switch. -/
noncomputable def equilibriumPolyTwo (a b : ℝ) : ℝ[X] :=
  X ^ 5 - C a * X ^ 4 + 2 * X ^ 3 - C (2 * a) * X ^ 2 + C (1 + b ^ 2) * X - C a

theorem eval_equilibriumPolyTwo (a b u : ℝ) :
    (equilibriumPolyTwo a b).eval u =
      u ^ 5 - a * u ^ 4 + 2 * u ^ 3 - 2 * a * u ^ 2 + (1 + b ^ 2) * u - a := by
  simp [equilibriumPolyTwo]

/-- **Degree `5`.** The `β = γ = 2` equilibrium polynomial has degree `5`. -/
theorem natDegree_equilibriumPolyTwo (a b : ℝ) : (equilibriumPolyTwo a b).natDegree = 5 := by
  unfold equilibriumPolyTwo
  compute_degree!

theorem monic_equilibriumPolyTwo (a b : ℝ) : (equilibriumPolyTwo a b).Monic := by
  unfold equilibriumPolyTwo
  monicity!

theorem equilibriumPolyTwo_ne_zero (a b : ℝ) : equilibriumPolyTwo a b ≠ 0 :=
  (monic_equilibriumPolyTwo a b).ne_zero

/-- Every real root of the quintic is positive. -/
theorem pos_of_isRoot_equilibriumPolyTwo (ha : 0 < a) {u : ℝ}
    (h : (equilibriumPolyTwo a b).IsRoot u) : 0 < u := by
  rw [IsRoot.def, eval_equilibriumPolyTwo] at h
  by_contra hu
  push Not at hu
  have h2 : 0 ≤ u ^ 2 := sq_nonneg u
  have h4 : 0 ≤ u ^ 4 := by positivity
  have h3 : u ^ 3 ≤ 0 := by nlinarith
  have h5 : u ^ 5 ≤ 0 := by nlinarith
  nlinarith [sq_nonneg b, mul_nonneg ha.le h4, mul_nonneg ha.le h2]

/-- Equilibria of the `β = γ = 2` toggle switch are the points `(u, b / (1 + u²))` with `u` a
root of `equilibriumPolyTwo a b` (necessarily positive). -/
theorem isEquilibrium_two_iff (ha : 0 < a) (hb : 0 < b) {u v : ℝ} :
    IsEquilibrium a b 2 2 u v ↔ (equilibriumPolyTwo a b).IsRoot u ∧ v = b / (1 + u ^ 2) := by
  constructor
  · rintro ⟨hu, hv, h1, h2⟩
    simp only [uDot, vDot, hill, sub_eq_zero] at h1 h2
    have hv1 : 0 < 1 + v ^ 2 := by positivity
    have hu2 : 0 < 1 + u ^ 2 := by positivity
    rw [div_eq_iff hv1.ne'] at h1
    refine ⟨?_, h2.symm⟩
    rw [div_eq_iff hu2.ne'] at h2
    rw [IsRoot.def, eval_equilibriumPolyTwo]
    linear_combination (-(1 + u ^ 2) ^ 2) * h1 + u * (b + v * (1 + u ^ 2)) * h2
  · rintro ⟨hr, rfl⟩
    have hu := pos_of_isRoot_equilibriumPolyTwo ha hr
    rw [IsRoot.def, eval_equilibriumPolyTwo] at hr
    have hu2 : 0 < 1 + u ^ 2 := by positivity
    refine ⟨hu.le, by positivity, ?_, ?_⟩
    · simp only [uDot, hill, sub_eq_zero]
      rw [div_eq_iff (by positivity)]
      field_simp
      linear_combination -hr
    · simp [vDot, hill]

theorem equilibria_two_eq_image (ha : 0 < a) (hb : 0 < b) :
    equilibria a b 2 2 =
      (fun u ↦ (u, b / (1 + u ^ 2))) '' {u | (equilibriumPolyTwo a b).IsRoot u} := by
  ext ⟨u, v⟩
  simp only [equilibria, mem_ofPred_eq, isEquilibrium_two_iff ha hb, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨hr, rfl⟩
    exact ⟨u, hr, rfl, rfl⟩
  · rintro ⟨w, hr, rfl, rfl⟩
    exact ⟨hr, rfl⟩

/-- The number of equilibria of the `β = γ = 2` toggle switch is the number of positive roots of
`equilibriumPolyTwo a b` (all of its real roots are positive). -/
theorem ncard_equilibria_two (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 2 2).ncard = {u | 0 < u ∧ (equilibriumPolyTwo a b).IsRoot u}.ncard := by
  rw [equilibria_two_eq_image ha hb,
    ncard_image_of_injective _ fun x y h ↦ (Prod.mk.inj h).1]
  congr 1
  ext u
  exact ⟨fun h ↦ ⟨pos_of_isRoot_equilibriumPolyTwo ha h, h⟩, fun h ↦ h.2⟩

/-- **At most five equilibria** for `β = γ = 2` (the degree bound). -/
theorem ncard_equilibria_two_le_five (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 2 2).ncard ≤ 5 := by
  rw [ncard_equilibria_two ha hb, ← natDegree_equilibriumPolyTwo a b]
  exact ncard_setOf_pos_isRoot_le_natDegree (equilibriumPolyTwo_ne_zero a b)

/-- **At least one equilibrium** for `β = γ = 2`. -/
theorem one_le_ncard_equilibria_two (ha : 0 < a) (hb : 0 < b) :
    1 ≤ (equilibria a b 2 2).ncard := by
  rw [ncard_equilibria_two ha hb, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    ncard_pos (finite_setOf_pos_isRoot (equilibriumPolyTwo_ne_zero a b))]
  have h0 : (equilibriumPolyTwo a b).eval 0 ≤ 0 := by
    simp [eval_equilibriumPolyTwo]; linarith
  have h1 : 0 ≤ (equilibriumPolyTwo a b).eval (a + 1) := by
    rw [eval_equilibriumPolyTwo]
    have : 0 ≤ (a + 1) ^ 2 := by positivity
    have : 0 ≤ (a + 1) ^ 4 := by positivity
    nlinarith [sq_nonneg b]
  obtain ⟨u, -, hu⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ a + 1)
    (equilibriumPolyTwo a b).continuous.continuousOn ⟨h0, h1⟩
  exact ⟨u, pos_of_isRoot_equilibriumPolyTwo ha hu, hu⟩

end BetaGammaTwo

end MathlibExt.Biology.Dynamics.ToggleSwitch
