/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Logic.Diophantine
public import MathlibExt.ModelTheory.DefiningIntegersInRationals

/-!
# Defining the integers in the rationals

Published definitions of `ℤ` inside the field `ℚ` by formulas in the language of rings,
of decreasing logical complexity.

* Julia Robinson's explicit first-order formula (1949), with the quantifier prefix
  `∀ A B ((∃ X Y Z …) ∧ ∀ M ((∃ X Y Z …) → (∃ X Y Z …)) → (∃ X Y Z …))`. It is proved, as
  `mem_range_intCast_iff_robinson`, in `MathlibExt.ModelTheory.DefiningIntegersInRationals`, which
  this module re-exports.
* Poonen's universal-existential definition (2009): two universal quantifiers followed by seven
  existential quantifiers in front of one polynomial equation with integer coefficients.
* Koenigsmann's universal definition (2016), equivalently: `ℚ ∖ ℤ` is Diophantine over `ℚ`,
  stated both with one explicit polynomial and through `MetaMathlibExt.IsDiophantineSet`.

In the last two statements the formula's single polynomial equation is a polynomial with integer
coefficients (`MvPolynomial _ ℤ`, the terms of the language of rings), evaluated at rational
points through `Int.castRingHom ℚ`. Its variables are indexed by a sum type: `Fin 1` for the free
variable `t`, then the bound variables in the order of the quantifier prefix.

## References

* J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14
  (1949), 98-114, Theorem 3.1.
* B. Poonen, "Characterizing integers among rational numbers with a universal-existential
  formula", *Amer. J. Math.* 131 (2009), 675-682, Theorem 4.1; arXiv:math/0703907.
* J. Koenigsmann, "Defining ℤ in ℚ", *Ann. of Math.* 183 (2016), 73-93, Theorem 1 and
  Corollary 2; arXiv:1011.3424.
-/

@[expose] public section

namespace MathlibExt.ModelTheory.DefiningIntegersInRationalsWanted

open MvPolynomial

/-- **Poonen's `∀²∃⁷` definition of `ℤ` in `ℚ`.** There is a polynomial `P` with integer
coefficients in the variables `t, a₁, a₂, x₁, …, x₇` such that a rational number `t` is an
integer if and only if for all rationals `a₁, a₂` there are rationals `x₁, …, x₇` with
`P(t, a₁, a₂, x₁, …, x₇) = 0`.

This is B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), Theorem 4.1: "It is possible to define ℤ in ℚ with a
Π₂⁺-formula with 2 universal quantifiers followed by 7 existential quantifiers." A Π₂⁺-formula
is a block of universal quantifiers, then a block of existential quantifiers, in front of an
atomic formula, which in the language of rings is one polynomial equation; an equation between
two terms is the vanishing of their difference, a polynomial with integer coefficients. -/
theorem_wanted exists_forall_two_exists_seven_poonen :
    ∃ P : MvPolynomial (Fin 1 ⊕ Fin 2 ⊕ Fin 7) ℤ, ∀ t : ℚ,
      t ∈ Set.range ((↑) : ℤ → ℚ) ↔
        ∀ a : Fin 2 → ℚ, ∃ x : Fin 7 → ℚ,
          eval₂ (Int.castRingHom ℚ) (Sum.elim (fun _ => t) (Sum.elim a x)) P = 0

/-- **Koenigsmann: `ℚ ∖ ℤ` is Diophantine over `ℚ`.** There are a positive integer `n` and a
polynomial `f` with integer coefficients in the variables `t, x₁, …, xₙ` such that a rational
number `t` is not an integer if and only if `f(t, x₁, …, xₙ) = 0` for some rationals
`x₁, …, xₙ`.

J. Koenigsmann, "Defining ℤ in ℚ", Ann. of Math. 183 (2016), Theorem 1, states: there is a
positive integer `n` and a polynomial `g ∈ ℤ[t; x₁, …, xₙ]` such that for any `t ∈ ℚ`,
`t ∈ ℤ` if and only if `g(t; x₁, …, xₙ) ≠ 0` for all `x₁, …, xₙ ∈ ℚ`: a universal definition
of `ℤ` in `ℚ`. Negating both sides gives this statement with `f = g`, which is the paper's
Corollary 2: `ℚ ∖ ℤ` is diophantine in `ℚ`. -/
theorem_wanted not_mem_range_intCast_iff_exists_eval_eq_zero_koenigsmann :
    ∃ n : ℕ, 0 < n ∧ ∃ f : MvPolynomial (Fin 1 ⊕ Fin n) ℤ, ∀ t : ℚ,
      t ∉ Set.range ((↑) : ℤ → ℚ) ↔
        ∃ x : Fin n → ℚ, eval₂ (Int.castRingHom ℚ) (Sum.elim (fun _ => t) x) f = 0

/-- **Koenigsmann: `ℚ ∖ ℤ` is a Diophantine subset of `ℚ`.** The set of rational numbers that are
not integers is Diophantine over `ℚ` with integer coefficients
(`MetaMathlibExt.IsDiophantineSet (Int.castRingHom ℚ)`): there are `n ∈ ℕ` and finitely many
polynomials with integer coefficients in the variables `t, y₁, …, yₙ` such that a rational `t` is
not an integer if and only if they have a common zero `(t, y₁, …, yₙ)` with `y ∈ ℚⁿ`.

This is J. Koenigsmann, "Defining ℤ in ℚ", Ann. of Math. 183 (2016), Corollary 2: "ℚ ∖ ℤ is
diophantine in ℚ". It follows from
`not_mem_range_intCast_iff_exists_eval_eq_zero_koenigsmann` by taking the one polynomial `f`. -/
theorem_wanted isDiophantineSet_compl_range_intCast_koenigsmann :
    MetaMathlibExt.IsDiophantineSet (Int.castRingHom ℚ) {t : ℚ | t ∉ Set.range ((↑) : ℤ → ℚ)}

end MathlibExt.ModelTheory.DefiningIntegersInRationalsWanted
