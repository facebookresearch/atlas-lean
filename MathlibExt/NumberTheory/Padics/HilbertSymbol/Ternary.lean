/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.NormCriterion
public import MathlibExt.NumberTheory.Padics.HilbertSymbol.ProductFormula

/-!
# Diagonal binary and ternary forms over `ℚ_[p]` and `ℝ` through Hilbert symbols

For a field `F` with `2 ≠ 0` and nonzero `a₁, a₂, a₃ : F`, the form
`a₁ x₁² + a₂ x₂² + a₃ x₃²` has a nonzero zero exactly when the Hilbert symbol
`(-a₁ a₂, -a₁ a₃)_F` is `1` (`hilbertSymbol.exists_ternary_eq_zero_iff`).

Over `ℚ_[p]` (every prime `p`, `p = 2` included) and over `ℝ`, where the Hilbert symbol is
bilinear and nondegenerate, this file proves:

* the binary criterion: `a x² + b y² = t` is solvable exactly when `(a, b) = (t, -a b)`
  (`padicHilbertSymbol.exists_mul_sq_add_mul_sq_eq_iff`,
  `realHilbertSymbol.exists_mul_sq_add_mul_sq_eq_iff`);
* the ternary criterion: `a x² + b y² + c z²` has a nonzero zero exactly when
  `(a, b) = (-c, -a b)` (`padicHilbertSymbol.exists_ternary_eq_zero_iff`,
  `realHilbertSymbol.exists_ternary_eq_zero_iff`);
* the values of an anisotropic diagonal ternary form: it takes the nonzero value `a` exactly when
  `-a a₁ a₂ a₃` is not a square (`padicHilbertSymbol.exists_ternary_eq_iff_not_isSquare`,
  `realHilbertSymbol.exists_ternary_eq_iff_not_isSquare`);
* both local criteria for diagonal ternary forms together
  (`padicHilbertSymbol.ternary_criteria`, `realHilbertSymbol.ternary_criteria`).

The binary and ternary criteria are Lemma 11.3 and Corollary 11.4 of A. V. Sutherland,
*18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture 11, p. 1. The proofs here
derive everything from bilinearity, the first properties of the symbol and nondegeneracy.
-/

@[expose] public section

open HilbertSymbol

namespace hilbertSymbol

variable {F : Type*} [Field F]

/-- **A diagonal ternary form has a nonzero zero exactly when $(-a_1 a_2, -a_1 a_3) = 1$.** Let
$F$ be a field in which $2 \neq 0$ and let $a_1, a_2, a_3 \in F$ be nonzero. Then
$a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2 = 0$ for some $(x_1, x_2, x_3) \in F^3$ other than $(0, 0, 0)$
if and only if the Hilbert symbol $(-a_1 a_2, -a_1 a_3)_F$ equals $1$.

The fields $\mathbb{R}$ and $\mathbb{Q}_p$ ($p = 2$ included) are the cases of interest; the
statement holds over every field with $2 \neq 0$. The proof multiplies the form by $a_1$, which
turns it into $(a_1 x_1)^2 + a_1 a_2 x_2^2 + a_1 a_3 x_3^2$, and applies
`hilbertSymbol.eq_one_iff_exists_ternary_eq_zero`, the equivalence (i) ⇔ (ii) of A. V. Sutherland,
*18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture 10, Lemma 10.2, p. 1 (stated
there over $\mathbb{Q}_p$, $p \le \infty$). The reduction of a diagonal ternary form to
$z^2 - a x^2 - b y^2$ is written out here. -/
theorem exists_ternary_eq_zero_iff (h2 : (2 : F) ≠ 0) (a₁ a₂ a₃ : Fˣ) :
    (∃ x₁ x₂ x₃ : F, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
        (a₁ : F) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) ↔
      hilbertSymbol F (-(a₁ * a₂)) (-(a₁ * a₃)) = 1 := by
  rw [eq_one_iff_exists_ternary_eq_zero h2]
  have ha : (a₁ : F) ≠ 0 := a₁.ne_zero
  simp only [Units.val_neg, Units.val_mul]
  constructor
  · rintro ⟨x₁, x₂, x₃, hne, h⟩
    refine ⟨a₁ * x₁, x₂, x₃, fun h' => hne ⟨?_, h'.2.1, h'.2.2⟩, ?_⟩
    · simpa [ha] using h'.1
    · linear_combination (a₁ : F) * h
  · rintro ⟨z, x, y, hne, h⟩
    refine ⟨z / a₁, x, y, fun h' => hne ⟨?_, h'.2.1, h'.2.2⟩, ?_⟩
    · simpa [ha] using h'.1
    · field_simp
      linear_combination h

end hilbertSymbol

namespace HilbertSymbol

section Generic

variable {F : Type*} [Field F]

/-- Multiplicativity of the Hilbert symbol in its first argument, as a hypothesis. -/
private abbrev TernMul (F : Type*) [Field F] : Prop :=
  ∀ a a' b : Fˣ, hilbertSymbol F (a * a') b = hilbertSymbol F a b * hilbertSymbol F a' b

/-- Nondegeneracy of the Hilbert symbol, as a hypothesis. -/
private abbrev TernNondeg (F : Type*) [Field F] : Prop :=
  ∀ b : Fˣ, (∀ a : Fˣ, hilbertSymbol F a b = 1) → IsSquare (b : F)

private theorem tern_mul_right (hmul : TernMul F) (a b b' : Fˣ) :
    hilbertSymbol F a (b * b') = hilbertSymbol F a b * hilbertSymbol F a b' := by
  rw [hilbertSymbol.comm, hmul, hilbertSymbol.comm b, hilbertSymbol.comm b']

private theorem tern_one_left (b : Fˣ) : hilbertSymbol F 1 b = 1 := by
  rw [hilbertSymbol.eq_one_iff]
  exact ⟨1, 0, by simp⟩

private theorem tern_mul_eq_one_iff {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ↔ x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

private theorem tern_sq_eq_one {x : ℤ} (hx : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases hx with rfl | rfl <;> decide

/-- `(t, t) = (t, -1)`. -/
private theorem tern_self (h2 : (2 : F) ≠ 0) (hmul : TernMul F) (t : Fˣ) :
    hilbertSymbol F t t = hilbertSymbol F t (-1) := by
  have h := tern_mul_right hmul t (-1) (-t)
  rw [neg_one_mul, neg_neg, hilbertSymbol.self_neg h2, mul_one] at h
  exact h

/-- `(a t, b t) = (a, b) (t, -a b)`, the computation in Sutherland's proof of Lemma 11.3. -/
private theorem tern_binary_symbol (h2 : (2 : F) ≠ 0) (hmul : TernMul F) (a b t : Fˣ) :
    hilbertSymbol F (a * t) (b * t) = hilbertSymbol F a b * hilbertSymbol F t (-(a * b)) := by
  have e : -(a * b) = (-1) * a * b := by rw [neg_one_mul, neg_mul]
  rw [hmul, tern_mul_right hmul a, tern_mul_right hmul t b t, tern_self h2 hmul, e,
    tern_mul_right hmul t, tern_mul_right hmul t, hilbertSymbol.comm a t]
  ring

private theorem tern_binary (h2 : (2 : F) ≠ 0) (hmul : TernMul F) (a b t : Fˣ) :
    (∃ x y : F, (a : F) * x ^ 2 + b * y ^ 2 = t) ↔
      hilbertSymbol F a b = hilbertSymbol F t (-(a * b)) := by
  have ht : (t : F) ≠ 0 := t.ne_zero
  have key : (∃ x y : F, (a : F) * x ^ 2 + b * y ^ 2 = t) ↔
      hilbertSymbol F (a * t⁻¹) (b * t⁻¹) = 1 := by
    rw [hilbertSymbol.eq_one_iff]
    unfold HilbertSymbol.IsSolvable
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    constructor
    · rintro ⟨x, y, h⟩
      refine ⟨x, y, ?_⟩
      rw [← div_self ht, ← h]
      ring
    · rintro ⟨x, y, h⟩
      refine ⟨x, y, ?_⟩
      field_simp at h
      linear_combination h
  have hsq : hilbertSymbol F (a * t⁻¹) (b * t⁻¹) = hilbertSymbol F (a * t) (b * t) := by
    have e : ∀ c : Fˣ, c * t⁻¹ = (c * t) * t⁻¹ ^ 2 := fun c => by group
    rw [e a, e b, hilbertSymbol.mul_sq_left, hilbertSymbol.mul_sq_right]
  rw [key, hsq, tern_binary_symbol h2 hmul,
    tern_mul_eq_one_iff (hilbertSymbol.eq_one_or_neg_one _ _)
      (hilbertSymbol.eq_one_or_neg_one _ _)]

/-- `(-a b, -a c) = (a, b) (-c, -a b)`. -/
private theorem tern_ternary_symbol (h2 : (2 : F) ≠ 0) (hmul : TernMul F) (a b c : Fˣ) :
    hilbertSymbol F (-(a * b)) (-(a * c)) =
      hilbertSymbol F a b * hilbertSymbol F (-c) (-(a * b)) := by
  have e : -(a * c) = a * (-c) := by rw [mul_neg]
  rw [e, tern_mul_right hmul, hilbertSymbol.comm (-(a * b)) a,
    ← hilbertSymbol.eq_neg_mul_right h2, hilbertSymbol.comm (-(a * b)) (-c)]

private theorem tern_ternary (h2 : (2 : F) ≠ 0) (hmul : TernMul F) (a b c : Fˣ) :
    (∃ x y z : F, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ (a : F) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
      hilbertSymbol F a b = hilbertSymbol F (-c) (-(a * b)) := by
  rw [hilbertSymbol.exists_ternary_eq_zero_iff h2, tern_ternary_symbol h2 hmul,
    tern_mul_eq_one_iff (hilbertSymbol.eq_one_or_neg_one _ _)
      (hilbertSymbol.eq_one_or_neg_one _ _)]

/-- A diagonal ternary form with a nonzero zero `(x₁, x₂, x₃)`, `x₁ ≠ 0`, takes every value. -/
private theorem tern_represents_aux (h2 : (2 : F) ≠ 0) {a₁ a₂ a₃ x₁ x₂ x₃ : F} (ha : a₁ ≠ 0)
    (hx : x₁ ≠ 0) (h : a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) (a : F) :
    ∃ y₁ y₂ y₃ : F, a₁ * y₁ ^ 2 + a₂ * y₂ ^ 2 + a₃ * y₃ ^ 2 = a := by
  set l := (a - a₁) / (2 * a₁ * x₁) with hl
  have hl' : 2 * l * a₁ * x₁ = a - a₁ := by
    rw [hl]
    field_simp
  exact ⟨l * x₁ + 1, l * x₂, l * x₃, by linear_combination l ^ 2 * h + hl'⟩

/-- A diagonal ternary form with a nonzero zero takes every value. -/
private theorem tern_represents (h2 : (2 : F) ≠ 0) (a₁ a₂ a₃ : Fˣ)
    (h : ∃ x₁ x₂ x₃ : F, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      (a₁ : F) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) (a : F) :
    ∃ x₁ x₂ x₃ : F, (a₁ : F) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = a := by
  obtain ⟨x₁, x₂, x₃, hne, h⟩ := h
  by_cases h₁ : x₁ = 0
  · by_cases h₂ : x₂ = 0
    · have h₃ : x₃ ≠ 0 := fun h₃ => hne ⟨h₁, h₂, h₃⟩
      obtain ⟨y₃, y₁, y₂, hy⟩ :=
        tern_represents_aux h2 (a₁ := a₃) (a₂ := a₁) (a₃ := a₂) (x₁ := x₃) (x₂ := x₁) (x₃ := x₂)
          a₃.ne_zero h₃ (by linear_combination h) a
      exact ⟨y₁, y₂, y₃, by linear_combination hy⟩
    · obtain ⟨y₂, y₁, y₃, hy⟩ :=
        tern_represents_aux h2 (a₁ := a₂) (a₂ := a₁) (a₃ := a₃) (x₁ := x₂) (x₂ := x₁) (x₃ := x₃)
          a₂.ne_zero h₂ (by linear_combination h) a
      exact ⟨y₁, y₂, y₃, by linear_combination hy⟩
  · exact tern_represents_aux h2 a₁.ne_zero h₁ h a

/-- Two `±1`-valued multiplicative functions, with an element on which they differ and elements
on which each is `-1`, take every pair of values together. -/
private theorem tern_exists_signs {G : Type*} [Monoid G] (χ₁ χ₂ : G → ℤ)
    (h₁ : ∀ x y, χ₁ (x * y) = χ₁ x * χ₁ y) (h₂ : ∀ x y, χ₂ (x * y) = χ₂ x * χ₂ y)
    (hv₁ : ∀ x, χ₁ x = 1 ∨ χ₁ x = -1) (hv₂ : ∀ x, χ₂ x = 1 ∨ χ₂ x = -1)
    (ho₁ : χ₁ 1 = 1) (ho₂ : χ₂ 1 = 1) {u v w : G} (hu : χ₁ u * χ₂ u = -1) (hv : χ₁ v = -1)
    (hw : χ₂ w = -1) {ε₁ ε₂ : ℤ} (he₁ : ε₁ = 1 ∨ ε₁ = -1) (he₂ : ε₂ = 1 ∨ ε₂ = -1) :
    ∃ t, χ₁ t = ε₁ ∧ χ₂ t = ε₂ := by
  have hA : ∃ A, χ₁ A = -1 ∧ χ₂ A = 1 := by
    rcases hv₁ u with h1 | h1 <;> rcases hv₂ u with h2 | h2 <;> rw [h1, h2] at hu <;>
      norm_num at hu
    · rcases hv₂ v with h3 | h3
      · exact ⟨v, hv, h3⟩
      · exact ⟨u * v, by rw [h₁, h1, hv]; norm_num, by rw [h₂, h2, h3]; norm_num⟩
    · exact ⟨u, h1, h2⟩
  have hB : ∃ B, χ₁ B = 1 ∧ χ₂ B = -1 := by
    rcases hv₁ u with h1 | h1 <;> rcases hv₂ u with h2 | h2 <;> rw [h1, h2] at hu <;>
      norm_num at hu
    · exact ⟨u, h1, h2⟩
    · rcases hv₁ w with h3 | h3
      · exact ⟨w, h3, hw⟩
      · exact ⟨u * w, by rw [h₁, h1, h3]; norm_num, by rw [h₂, h2, hw]; norm_num⟩
  obtain ⟨A, hA₁, hA₂⟩ := hA
  obtain ⟨B, hB₁, hB₂⟩ := hB
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · exact ⟨1, ho₁, ho₂⟩
  · exact ⟨B, hB₁, hB₂⟩
  · exact ⟨A, hA₁, hA₂⟩
  · exact ⟨A * B, by rw [h₁, hA₁, hB₁]; norm_num, by rw [h₂, hA₂, hB₂]; norm_num⟩

private theorem tern_exists_ne_one (hnd : TernNondeg F) {b : Fˣ} (hb : ¬IsSquare (b : F)) :
    ∃ a : Fˣ, hilbertSymbol F a b = -1 := by
  by_contra h
  push Not at h
  exact hb (hnd b fun a => (hilbertSymbol.eq_one_or_neg_one a b).resolve_right (h a))

private theorem tern_isSquare_mul_iff {c d : F} (hc : c ≠ 0) (hsq : IsSquare c) :
    IsSquare (c * d) ↔ IsSquare d := by
  obtain ⟨s, rfl⟩ := hsq
  have hs : s ≠ 0 := by rintro rfl; simp at hc
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r / s, by field_simp; linear_combination hr⟩
  · rintro ⟨r, rfl⟩
    exact ⟨s * r, by ring⟩

/-- The values of an anisotropic diagonal ternary form, over a field whose Hilbert symbol is
bilinear and nondegenerate. -/
private theorem tern_aniso (h2 : (2 : F) ≠ 0) (hmul : TernMul F) (hnd : TernNondeg F)
    (a₁ a₂ a₃ a : Fˣ)
    (hf : ¬∃ x₁ x₂ x₃ : F, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      (a₁ : F) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) :
    (∃ x₁ x₂ x₃ : F, (a₁ : F) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = a) ↔
      ¬IsSquare (-(a : F) * (a₁ * a₂ * a₃)) := by
  have ha₁ : (a₁ : F) ≠ 0 := a₁.ne_zero
  have ha₃ : (a₃ : F) ≠ 0 := a₃.ne_zero
  have ha : (a : F) ≠ 0 := a.ne_zero
  set c₁ : Fˣ := -(a₁ * a₂) with hc₁
  set c₂ : Fˣ := a₃ * a with hc₂
  have hd : -(a : F) * (a₁ * a₂ * a₃) = (c₁ : F) * c₂ := by
    rw [hc₁, hc₂]; push_cast; ring
  -- the binary form `⟨a₁, a₂⟩` has no nonzero zero
  have hbin : ∀ x₁ x₂ : F, (a₁ : F) * x₁ ^ 2 + a₂ * x₂ ^ 2 = 0 → x₁ = 0 ∧ x₂ = 0 := by
    intro x₁ x₂ h
    by_contra hne
    exact hf ⟨x₁, x₂, 0, fun h' => hne ⟨h'.1, h'.2.1⟩, by linear_combination h⟩
  have hc₁sq : ¬IsSquare (c₁ : F) := by
    rintro ⟨s, hs⟩
    have := hbin s a₁ (by
      have : (c₁ : F) = -(a₁ * a₂) := by rw [hc₁]; push_cast; ring
      linear_combination (a₁ : F) * (this.symm.trans hs).symm)
    exact ha₁ this.2
  rw [hd]
  by_cases hc₂sq : IsSquare (c₂ : F)
  · -- `a₃ a` is a square: `f` takes the value `a` and `-a d` is not a square
    obtain ⟨s, hs⟩ := hc₂sq
    have hs' : (a₃ : F) * a = s * s := by rw [← hs, hc₂]; push_cast; ring
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact mul_ne_zero ha₃ ha (by rw [hs']; ring)
    refine iff_of_true ⟨0, 0, s / a₃, ?_⟩ ?_
    · field_simp
      linear_combination -hs'
    · rw [mul_comm, tern_isSquare_mul_iff c₂.ne_zero ⟨s, hs⟩]
      exact hc₁sq
  · -- `f` takes `a` exactly when some `t ≠ 0` is a value of `⟨a₁, a₂⟩` and `-t` of `⟨a₃, -a⟩`
    have step : (∃ x₁ x₂ x₃ : F, (a₁ : F) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = a) ↔
        ∃ t : Fˣ, (∃ x y : F, (a₁ : F) * x ^ 2 + a₂ * y ^ 2 = t) ∧
          ∃ x y : F, (a₃ : F) * x ^ 2 + ((-a : Fˣ) : F) * y ^ 2 = ((-t : Fˣ) : F) := by
      constructor
      · rintro ⟨x₁, x₂, x₃, h⟩
        have ht : (a₁ : F) * x₁ ^ 2 + a₂ * x₂ ^ 2 ≠ 0 := by
          intro h0
          obtain ⟨rfl, rfl⟩ := hbin x₁ x₂ h0
          exact hc₂sq ⟨a₃ * x₃, by rw [hc₂]; push_cast; linear_combination -(a₃ : F) * h⟩
        refine ⟨Units.mk0 _ ht, ⟨x₁, x₂, rfl⟩, x₃, 1, ?_⟩
        simp only [Units.val_neg, Units.val_mk0]
        linear_combination h
      · rintro ⟨t, ⟨x₁, x₂, hx⟩, y, w, hy⟩
        simp only [Units.val_neg] at hy
        by_cases hw : w = 0
        · subst hw
          exfalso
          refine hf ⟨x₁, x₂, y, fun h' => t.ne_zero ?_, by linear_combination hx + hy⟩
          rw [← hx, h'.1, h'.2.1]; ring
        · exact ⟨x₁ / w, x₂ / w, y / w, by field_simp; linear_combination hx + hy⟩
    have hsym : ∀ t : Fˣ, ((∃ x y : F, (a₁ : F) * x ^ 2 + a₂ * y ^ 2 = t) ∧
          ∃ x y : F, (a₃ : F) * x ^ 2 + ((-a : Fˣ) : F) * y ^ 2 = ((-t : Fˣ) : F)) ↔
        hilbertSymbol F t c₁ = hilbertSymbol F a₁ a₂ ∧
          hilbertSymbol F t c₂ =
            hilbertSymbol F (-1) c₂ * hilbertSymbol F a₃ (-a) := by
      intro t
      rw [tern_binary h2 hmul, tern_binary h2 hmul]
      have e2 : -(a₃ * -a) = c₂ := by rw [hc₂, mul_neg, neg_neg]
      have e3 : -t = (-1) * t := by rw [neg_one_mul]
      rw [e2, e3, hmul]
      have hv := hilbertSymbol.eq_one_or_neg_one (F := F) (-1) c₂
      constructor
      · rintro ⟨h1, h2'⟩
        refine ⟨h1.symm, ?_⟩
        rw [h2', ← mul_assoc, tern_sq_eq_one hv, one_mul]
      · rintro ⟨h1, h2'⟩
        refine ⟨h1.symm, ?_⟩
        rw [h2', ← mul_assoc, tern_sq_eq_one hv, one_mul]
    rw [step]
    simp only [hsym]
    by_cases hcc : IsSquare ((c₁ : F) * c₂)
    · -- `-a d` is a square: the two characters agree, and anisotropy rules out every `t`
      simp only [hcc, not_true_eq_false, iff_false, not_exists, not_and]
      intro t h1 h2'
      have hmulc : hilbertSymbol F t c₁ * hilbertSymbol F t c₂ = 1 := by
        rw [← tern_mul_right hmul]
        exact hilbertSymbol.eq_one_of_isSquare_right (by push_cast; exact hcc)
      -- `c₂` and `c₁` have the same square class
      obtain ⟨s, hs⟩ := hcc
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact mul_ne_zero c₁.ne_zero c₂.ne_zero (by rw [hs]; ring)
      have hcls : ∀ x : Fˣ, hilbertSymbol F x c₂ = hilbertSymbol F x c₁ := by
        intro x
        have e : c₂ = c₁ * (Units.mk0 s hs0 * c₁⁻¹) ^ 2 := by
          ext
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
            Units.val_mk0]
          field_simp
          linear_combination hs
        rw [e, hilbertSymbol.mul_sq_right]
      have hε : hilbertSymbol F (-1) c₂ * hilbertSymbol F a₃ (-a) =
          hilbertSymbol F (-a₃) c₁ := by
        have e1 : hilbertSymbol F a₃ (-a) = hilbertSymbol F a₃ c₂ := by
          have e : -a = (-1) * a := by rw [neg_one_mul]
          rw [e, tern_mul_right hmul, hc₂, tern_mul_right hmul a₃ a₃, tern_self h2 hmul]
        rw [e1, hcls, hcls, ← hmul, neg_one_mul]
      have hanis : hilbertSymbol F a₁ a₂ ≠ hilbertSymbol F (-a₃) c₁ := by
        intro h
        exact hf ((tern_ternary h2 hmul a₁ a₂ a₃).2 h)
      apply hanis
      rw [← h1, ← hε, ← h2']
      have h1v := hilbertSymbol.eq_one_or_neg_one t c₁
      have h2v := hilbertSymbol.eq_one_or_neg_one t c₂
      exact (tern_mul_eq_one_iff h1v h2v).1 hmulc
    · -- `-a d` is not a square: the two characters differ, and a suitable `t` exists
      simp only [hcc, not_false_eq_true, iff_true]
      obtain ⟨u, hu⟩ := tern_exists_ne_one hnd (b := c₁ * c₂) (by push_cast; exact hcc)
      obtain ⟨v, hv⟩ := tern_exists_ne_one hnd hc₁sq
      obtain ⟨w, hw⟩ := tern_exists_ne_one hnd hc₂sq
      refine tern_exists_signs (fun t => hilbertSymbol F t c₁) (fun t => hilbertSymbol F t c₂)
        (fun x y => hmul x y c₁) (fun x y => hmul x y c₂)
        (fun x => hilbertSymbol.eq_one_or_neg_one x c₁)
        (fun x => hilbertSymbol.eq_one_or_neg_one x c₂) (tern_one_left c₁) (tern_one_left c₂)
        (u := u) (v := v) (w := w) ?_ hv hw (hilbertSymbol.eq_one_or_neg_one _ _) ?_
      · rw [← tern_mul_right hmul]; exact hu
      · rcases hilbertSymbol.eq_one_or_neg_one (F := F) (-1) c₂ with h | h <;>
          rcases hilbertSymbol.eq_one_or_neg_one a₃ (-a) with h' | h' <;> rw [h, h'] <;>
          norm_num

end Generic

section Instances

private theorem tern_padic_mul {p : ℕ} [Fact p.Prime] : TernMul ℚ_[p] :=
  fun a a' b => padicHilbertSymbol.mul_left a a' b

private theorem tern_padic_nondeg {p : ℕ} [Fact p.Prime] : TernNondeg ℚ_[p] := by
  intro b h
  obtain ⟨c, rfl⟩ := (padicHilbertSymbol.forall_eq_one_iff_isSquare b).1 h
  exact ⟨c, by push_cast; ring⟩

private theorem tern_real_eq_ite (a b : ℝˣ) :
    hilbertSymbol ℝ a b = if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then -1 else 1 := by
  split_ifs with h
  · exact realHilbertSymbol.eq_neg_one_iff_both_neg.2 h
  · exact (hilbertSymbol.eq_one_or_neg_one a b).resolve_right
      fun h' => h (realHilbertSymbol.eq_neg_one_iff_both_neg.1 h')

private theorem tern_real_mul : TernMul ℝ := by
  intro a a' b
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · simp only [tern_real_eq_ite, Units.val_mul, hb, and_true]
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha <;>
      rcases lt_or_gt_of_ne a'.ne_zero with ha' | ha'
    · simp [ha, ha', (mul_pos_of_neg_of_neg ha ha').not_gt]
    · simp [ha, ha'.not_gt, mul_neg_of_neg_of_pos ha ha']
    · simp [ha.not_gt, ha', mul_neg_of_pos_of_neg ha ha']
    · simp [ha.not_gt, ha'.not_gt, (mul_pos ha ha').not_gt]
  · simp [tern_real_eq_ite, hb.not_gt]

private theorem tern_real_nondeg : TernNondeg ℝ := by
  intro b h
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · have := h (-1)
    simp [tern_real_eq_ite, hb] at this
  · exact ⟨Real.sqrt b, (Real.mul_self_sqrt hb.le).symm⟩

end Instances

end HilbertSymbol

open HilbertSymbol

namespace padicHilbertSymbol

variable {p : ℕ} [Fact p.Prime]

/-- **When a diagonal binary form over $\mathbb{Q}_p$ takes a given value.** Let $p$ be a prime
($p = 2$ included) and let $a, b, t \in \mathbb{Q}_p$ be nonzero. Then $a x^2 + b y^2 = t$ for
some $x, y \in \mathbb{Q}_p$ if and only if the $p$-adic Hilbert symbols satisfy
$(a, b)_p = (t, -ab)_p$.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture
11, Lemma 11.3 and its proof, p. 1. -/
theorem exists_mul_sq_add_mul_sq_eq_iff (a b t : ℚ_[p]ˣ) :
    (∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 = t) ↔
      padicHilbertSymbol p a b = padicHilbertSymbol p t (-(a * b)) :=
  tern_binary two_ne_zero tern_padic_mul a b t

/-- **When a diagonal ternary form over $\mathbb{Q}_p$ has a nonzero zero.** Let $p$ be a prime
($p = 2$ included) and let $a, b, c \in \mathbb{Q}_p$ be nonzero. Then
$a x^2 + b y^2 + c z^2 = 0$ for some $(x, y, z) \in \mathbb{Q}_p^3$ other than $(0, 0, 0)$ if and
only if the $p$-adic Hilbert symbols satisfy $(a, b)_p = (-c, -ab)_p$.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture
11, Corollary 11.4, p. 1. The proof here goes through
`hilbertSymbol.exists_ternary_eq_zero_iff` and bilinearity instead of Sutherland's reduction to
Lemma 11.3. -/
theorem exists_ternary_eq_zero_iff (a b c : ℚ_[p]ˣ) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
      padicHilbertSymbol p a b = padicHilbertSymbol p (-c) (-(a * b)) :=
  tern_ternary two_ne_zero tern_padic_mul a b c

/-- **The values of an anisotropic diagonal ternary form over $\mathbb{Q}_p$.** Let $p$ be a prime
($p = 2$ included), let $a_1, a_2, a_3 \in \mathbb{Q}_p$ be nonzero, and suppose that
$f = a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2$ has no zero in $\mathbb{Q}_p^3$ other than $(0, 0, 0)$.
Then for nonzero $a \in \mathbb{Q}_p$, $f(x) = a$ for some $x \in \mathbb{Q}_p^3$ if and only if
$-a \, a_1 a_2 a_3$ is not a square in $\mathbb{Q}_p$.

The proof derives this from the binary and ternary criteria
(`padicHilbertSymbol.exists_mul_sq_add_mul_sq_eq_iff`,
`padicHilbertSymbol.exists_ternary_eq_zero_iff`; A. V. Sutherland, *18.782 Introduction to
Arithmetic Geometry*, MIT, Fall 2013, Lecture 11, Lemma 11.3 and Corollary 11.4, p. 1), the
bilinearity of the symbol and its nondegeneracy (`padicHilbertSymbol.forall_eq_one_iff_isSquare`),
by a character argument on the square classes. -/
theorem exists_ternary_eq_iff_not_isSquare (a₁ a₂ a₃ a : ℚ_[p]ˣ)
    (hf : ¬∃ x₁ x₂ x₃ : ℚ_[p], ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      (a₁ : ℚ_[p]) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) :
    (∃ x₁ x₂ x₃ : ℚ_[p], (a₁ : ℚ_[p]) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = a) ↔
      ¬IsSquare (-(a : ℚ_[p]) * (a₁ * a₂ * a₃)) :=
  tern_aniso two_ne_zero tern_padic_mul tern_padic_nondeg a₁ a₂ a₃ a hf

/-- **Representation by diagonal ternary forms over $\mathbb{Q}_p$.** Let $p$ be a prime
($p = 2$ included), let $a_1, a_2, a_3 \in \mathbb{Q}_p$ be nonzero, let
$f = a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2$ and let $d = a_1 a_2 a_3$. Then:

1. $f$ has a zero in $\mathbb{Q}_p^3$ other than $(0, 0, 0)$ if and only if the $p$-adic Hilbert
   symbol $(-a_1 a_2, -a_1 a_3)_p$ equals $1$;
2. for nonzero $a \in \mathbb{Q}_p$, $f(x) = a$ for some $x \in \mathbb{Q}_p^3$ if and only if $f$
   has such a zero or $-a d$ is not a square in $\mathbb{Q}_p$.

Part 1 is `hilbertSymbol.exists_ternary_eq_zero_iff`; part 2 combines the fact that a diagonal
ternary form with a nonzero zero takes every value with
`padicHilbertSymbol.exists_ternary_eq_iff_not_isSquare`. The proof derives both from
A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture 11,
Lemma 11.3 and Corollary 11.4, p. 1, and the nondegeneracy of the symbol. -/
theorem ternary_criteria (a₁ a₂ a₃ : ℚ_[p]ˣ) :
    ((∃ x₁ x₂ x₃ : ℚ_[p], ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
        (a₁ : ℚ_[p]) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) ↔
      padicHilbertSymbol p (-(a₁ * a₂)) (-(a₁ * a₃)) = 1) ∧
    ∀ a : ℚ_[p]ˣ, (∃ x₁ x₂ x₃ : ℚ_[p], (a₁ : ℚ_[p]) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = a) ↔
      (∃ x₁ x₂ x₃ : ℚ_[p], ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
        (a₁ : ℚ_[p]) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) ∨
      ¬IsSquare (-(a : ℚ_[p]) * (a₁ * a₂ * a₃)) := by
  refine ⟨hilbertSymbol.exists_ternary_eq_zero_iff two_ne_zero a₁ a₂ a₃, fun a => ?_⟩
  by_cases hf : ∃ x₁ x₂ x₃ : ℚ_[p], ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      (a₁ : ℚ_[p]) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0
  · exact iff_of_true (tern_represents two_ne_zero a₁ a₂ a₃ hf a) (Or.inl hf)
  · rw [exists_ternary_eq_iff_not_isSquare a₁ a₂ a₃ a hf]
    exact ⟨Or.inr, fun h => h.resolve_left hf⟩

end padicHilbertSymbol

namespace realHilbertSymbol

/-- **When a diagonal binary form over $\mathbb{R}$ takes a given value.** Let $a, b, t$ be
nonzero real numbers. Then $a x^2 + b y^2 = t$ for some $x, y \in \mathbb{R}$ if and only if the
real Hilbert symbols satisfy $(a, b)_\infty = (t, -ab)_\infty$.

The real case of A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013,
Lecture 11, Lemma 11.3, p. 1, stated for $\mathbb{Q}_p$ where, by the convention of Lecture 10,
p. 1, $p$ may be the archimedean prime $\infty$ with $\mathbb{Q}_\infty = \mathbb{R}$. The
bilinearity of the real symbol is read off the sign rule
`realHilbertSymbol.eq_neg_one_iff_both_neg`. -/
theorem exists_mul_sq_add_mul_sq_eq_iff (a b t : ℝˣ) :
    (∃ x y : ℝ, (a : ℝ) * x ^ 2 + b * y ^ 2 = t) ↔
      realHilbertSymbol a b = realHilbertSymbol t (-(a * b)) :=
  tern_binary two_ne_zero tern_real_mul a b t

/-- **When a diagonal ternary form over $\mathbb{R}$ has a nonzero zero.** Let $a, b, c$ be
nonzero real numbers. Then $a x^2 + b y^2 + c z^2 = 0$ for some $(x, y, z) \in \mathbb{R}^3$ other
than $(0, 0, 0)$ if and only if the real Hilbert symbols satisfy
$(a, b)_\infty = (-c, -ab)_\infty$.

The real case of A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013,
Lecture 11, Corollary 11.4, p. 1 ($p = \infty$ in the convention of Lecture 10, p. 1). -/
theorem exists_ternary_eq_zero_iff (a b c : ℝˣ) :
    (∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ (a : ℝ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
      realHilbertSymbol a b = realHilbertSymbol (-c) (-(a * b)) :=
  tern_ternary two_ne_zero tern_real_mul a b c

/-- **The values of an anisotropic diagonal ternary form over $\mathbb{R}$.** Let
$a_1, a_2, a_3$ be nonzero real numbers and suppose that $f = a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2$
has no zero in $\mathbb{R}^3$ other than $(0, 0, 0)$. Then for a nonzero real number $a$,
$f(x) = a$ for some $x \in \mathbb{R}^3$ if and only if $-a \, a_1 a_2 a_3$ is not a square in
$\mathbb{R}$.

The proof is the one of `padicHilbertSymbol.exists_ternary_eq_iff_not_isSquare`, with the
bilinearity and nondegeneracy of the real symbol read off the sign rule
`realHilbertSymbol.eq_neg_one_iff_both_neg`. -/
theorem exists_ternary_eq_iff_not_isSquare (a₁ a₂ a₃ a : ℝˣ)
    (hf : ¬∃ x₁ x₂ x₃ : ℝ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      (a₁ : ℝ) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) :
    (∃ x₁ x₂ x₃ : ℝ, (a₁ : ℝ) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = a) ↔
      ¬IsSquare (-(a : ℝ) * (a₁ * a₂ * a₃)) :=
  tern_aniso two_ne_zero tern_real_mul tern_real_nondeg a₁ a₂ a₃ a hf

/-- **Representation by diagonal ternary forms over $\mathbb{R}$.** Let $a_1, a_2, a_3$ be nonzero
real numbers, let $f = a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2$ and let $d = a_1 a_2 a_3$. Then:

1. $f$ has a zero in $\mathbb{R}^3$ other than $(0, 0, 0)$ if and only if the real Hilbert symbol
   $(-a_1 a_2, -a_1 a_3)_\infty$ equals $1$;
2. for a nonzero real number $a$, $f(x) = a$ for some $x \in \mathbb{R}^3$ if and only if $f$ has
   such a zero or $-a d$ is not a square in $\mathbb{R}$.

The real case of `padicHilbertSymbol.ternary_criteria`, with the same proof. -/
theorem ternary_criteria (a₁ a₂ a₃ : ℝˣ) :
    ((∃ x₁ x₂ x₃ : ℝ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
        (a₁ : ℝ) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) ↔
      realHilbertSymbol (-(a₁ * a₂)) (-(a₁ * a₃)) = 1) ∧
    ∀ a : ℝˣ, (∃ x₁ x₂ x₃ : ℝ, (a₁ : ℝ) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = a) ↔
      (∃ x₁ x₂ x₃ : ℝ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
        (a₁ : ℝ) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0) ∨
      ¬IsSquare (-(a : ℝ) * (a₁ * a₂ * a₃)) := by
  refine ⟨hilbertSymbol.exists_ternary_eq_zero_iff two_ne_zero a₁ a₂ a₃, fun a => ?_⟩
  by_cases hf : ∃ x₁ x₂ x₃ : ℝ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      (a₁ : ℝ) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 = 0
  · exact iff_of_true (tern_represents two_ne_zero a₁ a₂ a₃ hf a) (Or.inl hf)
  · rw [exists_ternary_eq_iff_not_isSquare a₁ a₂ a₃ a hf]
    exact ⟨Or.inr, fun h => h.resolve_left hf⟩

end realHilbertSymbol
