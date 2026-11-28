/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.Ternary
public import MathlibExt.NumberTheory.Rat.Place

/-!
# Ternary forms over `ℚ` with a nonzero zero at all places but one

A diagonal ternary form over `ℚ` with a nonzero zero over the completion `ℚ_v` at every place `v`
of `ℚ` except possibly one has a nonzero zero over every completion
(`Rat.Place.exists_ternary_eq_zero_of_forall_ne`). Over each completion the form has a nonzero
zero exactly when a Hilbert symbol is `1` (`hilbertSymbol.exists_ternary_eq_zero_iff`), and
Hilbert's product formula (`Rat.hilbertSymbol_product_formula`) then forces the remaining symbol.
-/

@[expose] public section

open HilbertSymbol

namespace Rat.Place

private theorem tap_two_ne_zero (v : Place) : (2 : CompletedField v) ≠ 0 := by
  cases v <;> exact two_ne_zero

/-- Over the completion at `v`, the form has a nonzero zero exactly when the Hilbert symbol of
`-a₁ a₂` and `-a₁ a₃` is `1`. -/
private theorem tap_iff (v : Place) (u₁ u₂ u₃ : ℚˣ) :
    (∃ x y z : CompletedField v, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        embedding v u₁ * x ^ 2 + embedding v u₂ * y ^ 2 + embedding v u₃ * z ^ 2 = 0) ↔
      hilbertSymbol (CompletedField v) (Units.map (embedding v).toMonoidHom (-(u₁ * u₂)))
        (Units.map (embedding v).toMonoidHom (-(u₁ * u₃))) = 1 := by
  have h := hilbertSymbol.exists_ternary_eq_zero_iff (tap_two_ne_zero v)
    (Units.map (embedding v).toMonoidHom u₁) (Units.map (embedding v).toMonoidHom u₂)
    (Units.map (embedding v).toMonoidHom u₃)
  have e : ∀ x y : ℚˣ, Units.map (embedding v).toMonoidHom (-(x * y)) =
      -(Units.map (embedding v).toMonoidHom x * Units.map (embedding v).toMonoidHom y) := by
    intro x y
    ext
    simp
  rw [e, e]
  simpa using h

/-- **Ternary forms with a nonzero zero at all places but one.** Let $a_1, a_2, a_3$ be nonzero
rational numbers and let $v_0$ be a place of $\mathbb{Q}$. If
$a_1 x^2 + a_2 y^2 + a_3 z^2 = 0$ has a solution $(x, y, z) \neq (0, 0, 0)$ in $\mathbb{Q}_v^3$
for every place $v \neq v_0$ of $\mathbb{Q}$, then it has such a solution in $\mathbb{Q}_v^3$ for
every place $v$ of $\mathbb{Q}$, $v_0$ included. Here $\mathbb{Q}_v$ is $\mathbb{R}$ at the
infinite place and $\mathbb{Q}_p$ at the place of a prime $p$.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture
11, Corollary 11.5 and its proof, p. 2, for the nondegenerate case; Sutherland's proof uses the
product formula for Hilbert symbols and Corollary 11.4. Here the criterion at each place is
`hilbertSymbol.exists_ternary_eq_zero_iff`, and the product formula is
`Rat.hilbertSymbol_product_formula`. -/
theorem exists_ternary_eq_zero_of_forall_ne {a₁ a₂ a₃ : ℚ} (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0)
    (h₃ : a₃ ≠ 0) (v₀ : Place)
    (h : ∀ v : Place, v ≠ v₀ → ∃ x y z : CompletedField v, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      embedding v a₁ * x ^ 2 + embedding v a₂ * y ^ 2 + embedding v a₃ * z ^ 2 = 0)
    (v : Place) :
    ∃ x y z : CompletedField v, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      embedding v a₁ * x ^ 2 + embedding v a₂ * y ^ 2 + embedding v a₃ * z ^ 2 = 0 := by
  set u₁ := Units.mk0 a₁ h₁
  set u₂ := Units.mk0 a₂ h₂
  set u₃ := Units.mk0 a₃ h₃
  have key : ∀ w : Place, (∃ x y z : CompletedField w, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      embedding w a₁ * x ^ 2 + embedding w a₂ * y ^ 2 + embedding w a₃ * z ^ 2 = 0) ↔
      hilbertSymbol (CompletedField w) (Units.map (embedding w).toMonoidHom (-(u₁ * u₂)))
        (Units.map (embedding w).toMonoidHom (-(u₁ * u₃))) = 1 :=
    fun w => tap_iff w u₁ u₂ u₃
  by_cases hv : v = v₀
  swap
  · exact h v hv
  subst hv
  rw [key]
  obtain ⟨-, hpf⟩ := Rat.hilbertSymbol_product_formula (-(u₁ * u₂)) (-(u₁ * u₃))
  cases v with
  | infinite =>
    have hp : ∀ p : Nat.Primes,
        (haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
        padicHilbertSymbol p (Units.map (Rat.castHom ℚ_[p]).toMonoidHom (-(u₁ * u₂)))
          (Units.map (Rat.castHom ℚ_[p]).toMonoidHom (-(u₁ * u₃)))) = 1 :=
      fun p => (key (.finite p)).1 (h _ (by simp))
    rw [finprod_eq_one_of_forall_eq_one hp, mul_one] at hpf
    exact hpf
  | finite q =>
    have hr : realHilbertSymbol (Units.map (Rat.castHom ℝ).toMonoidHom (-(u₁ * u₂)))
        (Units.map (Rat.castHom ℝ).toMonoidHom (-(u₁ * u₃))) = 1 :=
      (key .infinite).1 (h _ (by simp))
    have hp : ∀ p : Nat.Primes, p ≠ q →
        (haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
        padicHilbertSymbol p (Units.map (Rat.castHom ℚ_[p]).toMonoidHom (-(u₁ * u₂)))
          (Units.map (Rat.castHom ℚ_[p]).toMonoidHom (-(u₁ * u₃)))) = 1 :=
      fun p hpq => (key (.finite p)).1 (h _ (by simpa using hpq))
    rw [hr, one_mul, finprod_eq_single _ q hp] at hpf
    exact hpf

end Rat.Place
