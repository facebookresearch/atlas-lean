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

/-- **q-integers.** For a natural number $a$, the $q$-integer is the integer polynomial
$[a]_q = 1 + q + \dots + q^{a-1} = \sum_{i=0}^{a-1} q^i$; in particular $[0]_q = 0$. -/
noncomputable def qInt (a : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range a, X ^ i

/-- **Types of irreducible finite Coxeter groups.** The labels $A_n$, $B_n$, $D_n$ and $I_2(m)$
for natural numbers $n$ and $m$, together with $E_6$, $E_7$, $E_8$, $F_4$, $H_3$ and $H_4$. Every
natural number parameter is allowed here; the classification of irreducible finite Coxeter groups
uses $A_n$ ($n \ge 1$), $B_n$ ($n \ge 2$), $D_n$ ($n \ge 4$), the six exceptional labels and the
dihedral types $I_2(m)$ ($m \ge 3$). -/
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

/-- **Valid Coxeter types.** A Coxeter type is valid when it lies in the parameter range of the
classification of irreducible finite Coxeter groups: $A_n$ is valid when $n \ge 1$, $B_n$ when
$n \ge 2$, $D_n$ when $n \ge 4$ and $I_2(m)$ when $m \ge 3$, while $E_6$, $E_7$, $E_8$, $F_4$,
$H_3$ and $H_4$ are always valid. -/
def IsValid : CoxeterType → Prop
  | A n => 1 ≤ n
  | B n => 2 ≤ n
  | D n => 4 ≤ n
  | I2 m => 3 ≤ m
  | _ => True

/-- **Degrees of the irreducible finite Coxeter groups.** The list of degrees $d_1, \dots, d_r$ of
the basic invariants of a Coxeter type (so $d_i = e_i + 1$ for the exponents $e_i$) is:
$2, 3, \dots, n + 1$ for $A_n$; $2, 4, \dots, 2n$ for $B_n$; $n, 2, 4, \dots, 2n - 2$ for $D_n$;
$2, 5, 6, 8, 9, 12$ for $E_6$; $2, 6, 8, 10, 12, 14, 18$ for $E_7$;
$2, 8, 12, 14, 18, 20, 24, 30$ for $E_8$; $2, 6, 8, 12$ for $F_4$; $2, 6, 10$ for $H_3$;
$2, 12, 20, 30$ for $H_4$; and $2, m$ for $I_2(m)$. -/
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

/-- **Coxeter number.** The Coxeter number $h$ of a Coxeter type is the largest of its degrees,
and $0$ if its list of degrees is empty. -/
def coxeterNumber (T : CoxeterType) : ℕ :=
  T.degrees.foldr max 0

end CoxeterType

/-- **AIM Problem 2.1: positivity of q-Fuss-Catalan numbers.** The claim that for every type $T$
among $A_n$ ($n \ge 1$), $B_n$ ($n \ge 2$), $D_n$ ($n \ge 4$), $E_6$, $E_7$, $E_8$, $F_4$, $H_3$,
$H_4$ and $I_2(m)$ ($m \ge 3$) of irreducible finite Coxeter groups, with degrees
$d_1, \dots, d_r$ and Coxeter number $h$ (the largest degree), and every integer $k \ge 1$, there
is a polynomial $P(q)$ with nonnegative integer coefficients such that
$P(q) \prod_i [d_i]_q = \prod_i [kh + d_i]_q$, where $[a]_q = 1 + q + \dots + q^{a-1}$ is the
$q$-integer. Equivalently, $\prod_i [kh + d_i]_q / [d_i]_q$ is a polynomial in $q$ with
nonnegative integer coefficients. -/
def coxeterFussCatalanPositive : Prop :=
  ∀ T : CoxeterType, T.IsValid → ∀ k : ℕ, 1 ≤ k →
    ∃ P : ℕ[X], P.map (Nat.castRingHom ℤ) * (T.degrees.map qInt).prod =
      (T.degrees.map fun d => qInt (k * T.coxeterNumber + d)).prod

/--
**Positivity of q-Fuss-Catalan numbers of Coxeter groups.** Let $T$ be one of the types $A_n$
($n \ge 1$), $B_n$ ($n \ge 2$), $D_n$ ($n \ge 4$), $E_6$, $E_7$, $E_8$, $F_4$, $H_3$, $H_4$ or
$I_2(m)$ ($m \ge 3$) of irreducible finite Coxeter groups, with degrees $d_1, \dots, d_r$ and
Coxeter number $h$ (the largest degree), and let $k \ge 1$ be an integer. With the $q$-integers
$[a]_q = 1 + q + \dots + q^{a-1}$, there is a polynomial $P(q)$ with nonnegative integer
coefficients such that $P(q) \prod_i [d_i]_q = \prod_i [kh + d_i]_q$; that is, the quotient
$\prod_i [kh + d_i]_q / [d_i]_q$ is a polynomial in $q$ with nonnegative integer coefficients.

Gordon and Griffeth proved this for every irreducible finite Coxeter group (a well-generated real
reflection group, for which their Hecke algebra hypothesis holds).

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
