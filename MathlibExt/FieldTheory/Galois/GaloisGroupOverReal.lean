/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Galois groups of finite Galois extensions of `ℝ` have order a power of `2`

For a finite Galois extension `E / ℝ`, the Galois group `Gal(E / ℝ)` has
order `1` or `2`, hence a power of `2`. This is the book's lemma in
Lecture 34 (Main Theorem of Algebra): "If `G = Gal(E / ℝ)` for a finite
Galois extension `E / ℝ`, then `|G|` is a power of `2`."

The proof combines the classification of algebraic extensions of `ℝ`
(Mathlib's `Real.nonempty_algEquiv_or`: such an extension is `ℝ`-algebra
isomorphic to `ℝ` or to `ℂ`) with the Galois degree formula
`IsGalois.card_aut_eq_finrank`. In particular, the companion theorem in
`targets.yaml` ("`ℂ` is the only finite extension of `ℝ`") is exactly
`Real.nonempty_algEquiv_or` and is not restated here.
-/

@[expose] public section

namespace RealGalois

/-- **Degree of a finite extension of the reals.** If $E$ is a field that is a finite-dimensional
algebra over $\mathbb{R}$, then the dimension of $E$ as a real vector space is $1$ or $2$.

This follows because such a field $E$ is isomorphic as an $\mathbb{R}$-algebra to $\mathbb{R}$ or
to $\mathbb{C}$. -/
theorem finrank_eq_one_or_two {E : Type*} [Field E] [Algebra ℝ E]
    [FiniteDimensional ℝ E] :
    Module.finrank ℝ E = 1 ∨ Module.finrank ℝ E = 2 := by
  rcases Real.nonempty_algEquiv_or E with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [e.toLinearEquiv.finrank_eq]
    exact Module.finrank_self ℝ
  · right
    rw [e.toLinearEquiv.finrank_eq]
    exact Complex.finrank_real_complex

/-- **Galois groups over the reals have order 1 or 2.** If $E$ is a finite Galois extension of
$\mathbb{R}$, then the Galois group $\mathrm{Gal}(E/\mathbb{R})$ has order $1$ or $2$. -/
theorem gal_card_eq_one_or_two {E : Type*} [Field E] [Algebra ℝ E]
    [FiniteDimensional ℝ E] [IsGalois ℝ E] :
    Nat.card Gal(E/ℝ) = 1 ∨ Nat.card Gal(E/ℝ) = 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_eq_one_or_two

/-- **Galois groups over the reals have order a power of 2.** If $E$ is a finite Galois extension
of $\mathbb{R}$, then the Galois group $\mathrm{Gal}(E/\mathbb{R})$ has order $2^n$ for some natural
number $n$.

In fact the order is $1$ or $2$.

Source: the book's lemma in Lecture 34 (Main Theorem of Algebra). -/
theorem gal_card_pow_two {E : Type*} [Field E] [Algebra ℝ E]
    [FiniteDimensional ℝ E] [IsGalois ℝ E] :
    ∃ n : ℕ, Nat.card Gal(E/ℝ) = 2 ^ n := by
  rcases gal_card_eq_one_or_two (E := E) with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

end RealGalois
