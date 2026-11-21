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
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

@[expose] public section

namespace MathlibExt.NumberTheory.DirichletExplicitFormulaWanted

open DirichletCharacter ArithmeticFunction

/-!
# A truncated explicit formula for Dirichlet characters

The sum `Σ_{n ≤ x} Λ(n) χ(n)` expressed through the zeros of `L(·, χ)` with real part at least `ε`
and height at most `T`, up to an error `O_ε(x^ε log²(q T) + (x / T) log²(x q T))`.
-/

open Classical in
/-- **Truncated explicit formula for `ψ(x, χ)`.** For every `0 < ε < 1` there is a constant `C`
such that for every modulus `q ≥ 1`, every Dirichlet character `χ` modulo `q` and all real
`x, T ≥ 2`,
`|Σ_{n ≤ x} Λ(n) χ(n) - δ_χ x + Σ_ρ m_ρ x^ρ / ρ| ≤ C (x^ε log²(q T) + (x / T) log²(x q T))`,
where `δ_χ` is `1` for the principal character and `0` otherwise, `ρ` runs over the zeros
`ρ ≠ 1` of `L(·, χ)` with `Re ρ ≥ ε` and `|Im ρ| ≤ T` (finitely many), and `m_ρ` is the order of
the zero `ρ`. Here `Λ` is the von Mangoldt function and `L(·, χ)` the meromorphic continuation of
the Dirichlet series.

Source: T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014),
<https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>:
Exercise 45(iv) for non-principal `χ` (zeros counted with multiplicity, Remark 17), whose proof
repeats that of Theorem 21 with Exercise 45(i)–(iii) and the truncated Perron formula
(Proposition 12); and Theorem 21 for `ζ`, which gives the principal characters, since for `χ`
principal modulo `q` the zeros of `L(·, χ)` with `Re ρ > 0` are those of `ζ`, with the same
orders, and `Σ_{n ≤ x} Λ(n) (1 - χ(n))` is at most `log q · log x / log 2`. -/
theorem_wanted truncated_explicit_formula (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x T : ℝ), 2 ≤ x → 2 ≤ T →
      ‖(∑ n ∈ Finset.Iic ⌊x⌋₊, (Λ n : ℂ) * χ n) - (if χ = 1 then (x : ℂ) else 0) +
          ∑ᶠ ρ ∈ {ρ : ℂ | ρ ≠ 1 ∧ LFunction χ ρ = 0 ∧ ε ≤ ρ.re ∧ |ρ.im| ≤ T},
            (analyticOrderNatAt (LFunction χ) ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        C * (x ^ ε * Real.log ((q : ℝ) * T) ^ 2 + x / T * Real.log (x * q * T) ^ 2)

end MathlibExt.NumberTheory.DirichletExplicitFormulaWanted
