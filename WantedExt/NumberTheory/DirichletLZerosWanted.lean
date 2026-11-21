/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

@[expose] public section

namespace MathlibExt.NumberTheory.DirichletLZerosWanted

open DirichletCharacter

/-!
# Zeros of Dirichlet L-functions near `s = 1`

The classical zero-free region for the Dirichlet L-functions of a fixed modulus, with at most one
exceptional zero (Landau–Page), and Siegel's lower bound for `L(1, χ)`.
-/

/-- **Classical zero-free region for Dirichlet L-functions of a fixed modulus.** There is a
constant `c > 0` with the following property. Fix a modulus `q ≥ 1` and call a complex number
`ρ ≠ 1` *exceptional for `q`* when `Re ρ > 1 - c / log (q (2 + |Im ρ|))`. If `L(ρ, χ) = 0` for a
Dirichlet character `χ` modulo `q` and an exceptional `ρ`, then `χ` is real (`χ² = 1`) and
non-principal, `ρ` is real and a simple zero of `L(·, χ)`, and the pair `(χ, ρ)` is the only one
for the modulus `q`: if `L(ρ', χ') = 0` for a character `χ'` modulo `q` and an exceptional `ρ'`,
then `χ' = χ` and `ρ' = ρ`. Here `L(·, χ)` is the meromorphic continuation of the Dirichlet
series, entire for non-principal `χ`.

Source: T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014),
<https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>:
Proposition 51 gives the zero-free region `σ > 1 - c / log (q (2 + |t|))` for each character
`χ` modulo `q` apart from at most one real zero, counted with multiplicity, which can occur only
for a non-principal real `χ`; Theorem 53 (Landau) and Exercise 52 (distinct characters modulo `q`
are induced by distinct primitive characters of conductor at most `q`, with the same zeros in
`Re s > 0`) show that at most one character modulo `q` has such a zero. The fixed-modulus form is
Proposition 6 of T. Tao, *254A, Notes 7: Linnik's theorem on primes in arithmetic progressions*
(2015). -/
theorem_wanted dirichletLFunction_zero_free_region_fixed_modulus :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      ρ ≠ 1 → 1 - c / Real.log ((q : ℝ) * (2 + |ρ.im|)) < ρ.re → LFunction χ ρ = 0 →
        χ ^ 2 = 1 ∧ χ ≠ 1 ∧ ρ.im = 0 ∧ analyticOrderAt (LFunction χ) ρ = 1 ∧
          ∀ (χ' : DirichletCharacter ℂ q) (ρ' : ℂ), ρ' ≠ 1 →
            1 - c / Real.log ((q : ℝ) * (2 + |ρ'.im|)) < ρ'.re → LFunction χ' ρ' = 0 →
              χ' = χ ∧ ρ' = ρ

/-- **Siegel's theorem.** For every `ε > 0` there is a constant `c > 0` such that
`|L(1, χ)| ≥ c q^(-ε)` for every real (`χ² = 1`) primitive non-principal Dirichlet character `χ`
of conductor `q`. The constant `c` is ineffective: the proof does not compute it.

Source: T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014),
<https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>,
Theorem 62(i), in the form stated in the paragraph after it: "all but at most one" real primitive
character may be replaced by "all" at the cost of an ineffective constant. For such `χ` the value
`L(1, χ)` is a positive real number. -/
theorem_wanted siegel_norm_LFunction_one_ge (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → c * (q : ℝ) ^ (-ε) ≤ ‖LFunction χ 1‖

end MathlibExt.NumberTheory.DirichletLZerosWanted
