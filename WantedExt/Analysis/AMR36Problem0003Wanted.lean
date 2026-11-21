/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 036-0003: remaining Briot-Bouquet case implies exponential polynomial
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Analysis.AMR36Problem0003Wanted

/-!

Clause list for [AMR-036-0003] (Eremenko, Meromorphic solutions of
Briot–Bouquet type equations, remaining 2024 case):
1. `k : ℕ` is the differential order, higher-order means `2 ≤ k`.
2. `d : ℕ` is the total degree of `F`, with `1 ≤ d`.
3. `F : MvPolynomial (Fin 2) ℂ` is the governing two-variable polynomial,
   with `MvPolynomial.totalDegree F = d`.
4. `F` is irreducible (`Irreducible F`); the reducible instance
   `d = 2`, `Q = 0`, `F = (X₀ - a * X₁) ^ 2` is thereby excluded.
5. The highest-degree homogeneous part of `F` has a single distinct linear
   factor, in the source's equivalent remaining normal form
   `F = (X₀ - a * X₁) ^ d + Q` for some `a : ℂ`.
6. `Q : MvPolynomial (Fin 2) ℂ` satisfies `Q.totalDegree ≤ d - 1`.
7. `f : ℂ → ℂ` is entire, i.e. `Differentiable ℂ f`.
8. `f` satisfies the source equation `F(y^{(k)}, y) = 0`, i.e.
   `MvPolynomial.eval (X₀ ↦ iteratedDeriv k f z, X₁ ↦ f z) F = 0` for all `z`.
9. In normal-form coordinates this is
   `(f^{(k)}(z) - a * f(z)) ^ d + Q(f^{(k)}(z), f(z)) = 0` for all `z`,
   with `X₀ ↦ y^{(k)}` and `X₁ ↦ y`.
10. Question: every `f` satisfying (1)-(9) is an exponential polynomial.
-/

open scoped BigOperators

/-- Exponential polynomial on `ℂ`: a finite sum of polynomial times exponential
functions. Cites [AMR-036-0003] (Eremenko, remaining 2024 Briot–Bouquet case):
the conclusion predicate for the entire-solution question. -/
def IsExponentialPolynomial (f : ℂ → ℂ) : Prop :=
  ∃ (n : ℕ) (P : Fin n → Polynomial ℂ) (lam : Fin n → ℂ),
    f = fun z => ∑ j, Polynomial.eval z (P j) * Complex.exp (lam j * z)

/-- Remaining Briot–Bouquet data from [AMR-036-0003] (Eremenko, remaining 2024
case): order `k` with `2 ≤ k`, degree `d` with `1 ≤ d`, governing polynomial
`F : MvPolynomial (Fin 2) ℂ` with `totalDegree F = d`, `Irreducible F`,
remaining normal form `F = (X₀ - a * X₁) ^ d + Q`, lower part
`Q : MvPolynomial (Fin 2) ℂ` with `Q.totalDegree ≤ d - 1`, entire `f`
(`Differentiable ℂ f`) satisfying both `eval F = 0` and the normal-form
equation `((iteratedDeriv k f z - a * f z) ^ d + eval Q = 0)` for all `z`,
with `X₀ ↦ iteratedDeriv k f z` and `X₁ ↦ f z`. -/
def SatisfiesRemainingBriotBouquet (k d : ℕ) (F : MvPolynomial (Fin 2) ℂ)
    (a : ℂ) (Q : MvPolynomial (Fin 2) ℂ) (f : ℂ → ℂ) : Prop :=
  2 ≤ k ∧ 1 ≤ d ∧ MvPolynomial.totalDegree F = d ∧ Irreducible F ∧
    F = (MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1) ^ d + Q ∧
    MvPolynomial.totalDegree Q ≤ d - 1 ∧ Differentiable ℂ f ∧
    (∀ z : ℂ, MvPolynomial.eval
      (fun i => if i = 0 then iteratedDeriv k f z else f z) F = 0) ∧
    ∀ z : ℂ, ((iteratedDeriv k f z - a * f z) ^ d +
      MvPolynomial.eval (fun i => if i = 0 then iteratedDeriv k f z else f z) Q = 0)

/-- Question of [AMR-036-0003], posed as open and since resolved affirmatively (see
`BriotBouquetRemainingImpliesExpPoly_holds` below) (Eremenko, Meromorphic solutions of
Briot–Bouquet type equations, remaining 2024 case): every entire solution of
`F(y^{(k)}, y) = 0` with `F` irreducible of total degree `d` in the remaining
normal form `(y^{(k)} - a * y) ^ d + Q_{d-1}(y^{(k)}, y) = 0`,
`deg Q_{d-1} ≤ d - 1`, is an exponential polynomial. -/
def BriotBouquetRemainingImpliesExpPoly : Prop :=
  ∀ (k d : ℕ) (F : MvPolynomial (Fin 2) ℂ) (a : ℂ)
    (Q : MvPolynomial (Fin 2) ℂ) (f : ℂ → ℂ),
    SatisfiesRemainingBriotBouquet k d F a Q f → IsExponentialPolynomial f
/--
Resolved true: Resolved affirmatively: Eremenko, Ng and Zhang (Entire solutions of higher order
Briot-Bouquet equations, arXiv:2610.20438, October 2026, Theorem 1.1) prove that every
transcendental entire solution of an irreducible equation F(y^{(k)}, y) = 0 is R(e^{cz}) with R
rational, unless the equation is linear; entire such R(e^{cz}) are Laurent polynomials in
e^{cz}, and solutions of the linear case are exponential polynomials. Marques (arXiv:2610.19243)
gives an independent proof, and Eremenko's unsolved-problems page marks the problem solved
completely. Both papers are recent preprints. Source: A. Eremenko, T. W. Ng, T. Zhang, Entire
solutions of higher order Briot-Bouquet equations, arXiv:2610.20438 (2026),
https://arxiv.org/abs/2610.20438. Moved from `OpenConjectures/Analysis/AMR36Problem0003`.
-/
public theorem_wanted BriotBouquetRemainingImpliesExpPoly_holds : BriotBouquetRemainingImpliesExpPoly

end MathlibExt.Analysis.AMR36Problem0003Wanted
