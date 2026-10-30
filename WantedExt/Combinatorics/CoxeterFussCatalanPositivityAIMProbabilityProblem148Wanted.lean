/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Positivity of q-Fuss-Catalan numbers of Coxeter groups (AIM braid groups outline, Problem 2.1)

AIM workshop Braid groups, clusters and free probability, outline, Problem 2.1 (C. Athanasiadis):
for a finite Coxeter group `W` of rank `n` with Coxeter number `h`, exponents `e₁, …, eₙ` and `k ≥
1`, show that `∏ᵢ [kh + eᵢ + 1]_q / [eᵢ + 1]_q`, `[n]_q = q + q² + ⋯ + qⁿ`, is a polynomial in `q`
with nonnegative integer coefficients (then known in types `A`, `B`, `D`).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.CoxeterFussCatalanPositivityAIMProbabilityProblem148Wanted

/-!
Source: AIM workshop Braid groups, clusters and free probability (January 2005), outline by D.
Armstrong, Problem 2.1 (C. Athanasiadis), https://aimath.org/WWN/braidgroups/braidgroups.pdf.
UnsolvedMath record UM-20002706 (`AIM-PROBABILITY-0148`), dataset ulamai/UnsolvedMath v1.8.0.

A finite Coxeter group is a product of irreducible ones, and `h` is the Coxeter number of an
irreducible group, so the statement is made for the irreducible types `A_n` (`n ≥ 1`), `B_n` (`n ≥
2`), `D_n` (`n ≥ 4`), `E₆`, `E₇`, `E₈`, `F₄`, `H₃`, `H₄`, `I₂(m)` (`m ≥ 3`), through their degrees
`dᵢ = eᵢ + 1` (Mathlib has no invariant degrees; standard table, e.g. Humphreys, Reflection groups
and Coxeter groups, §3.7) and `h = max dᵢ`. The table was checked against the group orders `∏ dᵢ`,
the reflection counts `∑ (dᵢ - 1)` and the Catalan numbers `∏ (h + dᵢ)/dᵢ`. With `[a]_q = 1 + ⋯ +
q^{a-1}` the quotient is the list's (its `q + ⋯ + q^a` differ by `q`, which cancels). Nonnegative
integer coefficients: the product is `P` mapped from `ℕ[q]`.
-/

open Polynomial

/-- The `q`-integer `[a]_q = 1 + q + ⋯ + q^{a-1}`. -/
noncomputable def qInt (a : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range a, X ^ i

/-- Types of the irreducible finite Coxeter groups: `A_n`, `B_n`, `D_n`, `E₆`, `E₇`, `E₈`, `F₄`,
`H₃`, `H₄` and the dihedral types `I₂(m)`. -/
inductive CoxeterType
  | A (n : ℕ)
  | B (n : ℕ)
  | D (n : ℕ)
  | E6
  | E7
  | E8
  | F4
  | H3
  | H4
  | I2 (m : ℕ)

namespace CoxeterType

/-- The parameter range of the classification: `A_n` (`n ≥ 1`), `B_n` (`n ≥ 2`), `D_n` (`n ≥ 4`),
`I₂(m)` (`m ≥ 3`). -/
def IsValid : CoxeterType → Prop
  | A n => 1 ≤ n
  | B n => 2 ≤ n
  | D n => 4 ≤ n
  | I2 m => 3 ≤ m
  | _ => True

/-- The degrees `d₁, …, dₙ` of the basic invariants, `dᵢ = eᵢ + 1` for the exponents `eᵢ`:
`A_n`: `2, …, n + 1`; `B_n`: `2, 4, …, 2n`; `D_n`: `2, 4, …, 2n - 2, n`; `E₆`: `2, 5, 6, 8, 9, 12`;
`E₇`: `2, 6, 8, 10, 12, 14, 18`; `E₈`: `2, 8, 12, 14, 18, 20, 24, 30`; `F₄`: `2, 6, 8, 12`;
`H₃`: `2, 6, 10`; `H₄`: `2, 12, 20, 30`; `I₂(m)`: `2, m`. -/
def degrees : CoxeterType → List ℕ
  | A n => (List.range n).map (· + 2)
  | B n => (List.range n).map fun i => 2 * (i + 1)
  | D n => n :: (List.range (n - 1)).map fun i => 2 * (i + 1)
  | E6 => [2, 5, 6, 8, 9, 12]
  | E7 => [2, 6, 8, 10, 12, 14, 18]
  | E8 => [2, 8, 12, 14, 18, 20, 24, 30]
  | F4 => [2, 6, 8, 12]
  | H3 => [2, 6, 10]
  | H4 => [2, 12, 20, 30]
  | I2 m => [2, m]

/-- The Coxeter number `h`, the largest degree. -/
def coxeterNumber (T : CoxeterType) : ℕ :=
  T.degrees.foldr max 0

end CoxeterType

/-- AIM Braid groups, clusters and free probability, Problem 2.1, as a claim: for every
irreducible finite Coxeter group `W` with degrees `d₁, …, dₙ` (`dᵢ = eᵢ + 1`) and Coxeter number
`h`, and every integer `k ≥ 1`, `∏ᵢ [k h + dᵢ]_q / [dᵢ]_q` is a polynomial in `q` with nonnegative
integer coefficients. -/
def coxeterFussCatalanPositive : Prop :=
  ∀ T : CoxeterType, T.IsValid → ∀ k : ℕ, 1 ≤ k →
    ∃ P : ℕ[X], P.map (Nat.castRingHom ℤ) * (T.degrees.map qInt).prod =
      (T.degrees.map fun d => qInt (k * T.coxeterNumber + d)).prod

/--
Resolved true: Gordon and Griffeth proved that the `q`-Fuss-Catalan number `∏ᵢ [mh + dᵢ]_q / [dᵢ]_q`
of every irreducible finite Coxeter group (a well-generated real reflection group, for which their
Hecke algebra hypothesis holds) is a polynomial in `q` with nonnegative integer coefficients.
Source: AIM workshop Braid groups, clusters and free probability (January 2005), outline by D.
Armstrong, Problem 2.1 (C. Athanasiadis), https://aimath.org/WWN/braidgroups/braidgroups.pdf;
resolution: I. Gordon and S. Griffeth, Catalan numbers for complex reflection groups, Amer. J. Math.
134 (2012), no. 6, 1491-1502, arXiv:0912.1578, Theorem in §1.6: the q-Fuss-Catalan number
C_W^{(m)}(q) lies in ℕ[q] for every irreducible complex reflection group W under Hypothesis 2.4
(freeness of the Hecke algebra, which the paper notes is known for all real W); §1.9: for
well-generated W, in particular every irreducible finite Coxeter group, C_W^{(m)}(q) = ∏ [mh +
d_i]_q / [d_i]_q, https://doi.org/10.1353/ajm.2012.0047.
-/
public theorem_wanted coxeterFussCatalanPositive_holds : coxeterFussCatalanPositive

end MathlibExt.Combinatorics.CoxeterFussCatalanPositivityAIMProbabilityProblem148Wanted
