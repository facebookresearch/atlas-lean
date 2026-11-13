/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The set-theoretic salmon problem (Sturmfels, Open Problems in Algebraic Statistics)

B. Sturmfels, Open problems in algebraic statistics, Specific Problem (the salmon problem;
Pachter-Sturmfels, Conjecture 3.24): consider the variety of `4 × 4 × 4`-tables of tensor rank at
most `4`. There are certain known polynomials of degree at most nine which vanish on this variety.
Do they suffice to cut out the variety?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SalmonSetTheoreticAMR146Problem0001Wanted

/-!
Source: B. Sturmfels, Open problems in algebraic statistics, in Emerging Applications of Algebraic
Geometry, IMA Vol. Math. Appl. 149 (2009), arXiv:0707.4558, Section 2, Specific Problem.
UnsolvedMath record UM-00800862 (`AMR-146-0001`), dataset ulamai/UnsolvedMath v1.8.0.

Tables are points of `ℂ^{64}` indexed by `Fin 4 × Fin 4 × Fin 4`. The variety of tables of tensor
rank at most `4` is the Zariski closure of the sums of four rank-one tables (the tables of border
rank at most `4`, the affine cone over the fourth secant variety of `ℙ³ × ℙ³ × ℙ³`), written as the
zero locus of the vanishing ideal. The source's known polynomials (its quintics, the
Landsberg-Manivel sextics and the generators of degree nine) are not named; the statement says that
the polynomials of total degree at most `9` vanishing on the variety cut it out, which is implied by
a positive answer to the source's question. The source's conclusion asks the question
'Set-theoretically? Ideal-theoretically?'; this module states the set-theoretic version, the one
Friedland and Gross proved.
-/

/-- `4 × 4 × 4` complex tables `(p_{ijk})`, as points of `ℂ^{64}`. -/
abbrev Table : Type := Fin 4 × Fin 4 × Fin 4 → ℂ

/-- The tables of tensor rank at most `4`: sums of four tables of the form `a ⊗ b ⊗ c`. -/
def rankAtMostFour : Set Table :=
  {T | ∃ a b c : Fin 4 → Fin 4 → ℂ, ∀ i j k, T (i, j, k) = ∑ r, a r i * b r j * c r k}

/-- The variety of `4 × 4 × 4` tables of tensor rank at most `4`: the common zero set of all
polynomials vanishing on `rankAtMostFour` (its Zariski closure, the affine cone over the fourth
secant variety of the Segre variety `ℙ³ × ℙ³ × ℙ³`). -/
def salmonVariety : Set Table :=
  MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ rankAtMostFour)

/-- Sturmfels's Specific Problem (the salmon problem, set-theoretic form): polynomials of degree at
most `9` vanishing on the variety cut it out, that is, a table at which every polynomial of total
degree at most `9` vanishing on `rankAtMostFour` vanishes lies in the variety. -/
def degreeNineCutsOutSalmonVariety : Prop :=
  {T : Table | ∀ f ∈ MvPolynomial.vanishingIdeal ℂ rankAtMostFour, f.totalDegree ≤ 9 →
      MvPolynomial.eval T f = 0} = salmonVariety

/--
Resolved true (set-theoretic version): Friedland and Gross proved that the variety of `4 × 4 × 4`
tensors of border rank at most `4` is the zero set of polynomial equations of degrees `5`, `6` and
`9` vanishing on it (Strassen's commutation conditions, the Landsberg-Manivel polynomials and the
symmetrization conditions). Source: B. Sturmfels, Open problems in algebraic statistics, in Emerging
Applications of Algebraic Geometry, IMA Vol. Math. Appl. 149 (2009), arXiv:0707.4558, Section 2,
Specific Problem; resolution: S. Friedland and E. Gross, A proof of the set-theoretic version of the
salmon conjecture, J. Algebra 356 (2012), 374-379, arXiv:1104.1776, Abstract: the irreducible
variety of 4 × 4 × 4 complex tensors of border rank at most 4 is the zero set of polynomial
equations of degree 5 (the Strassen commutation conditions), of degree 6 (the Landsberg-Manivel
polynomials) and of degree 9 (the symmetrization conditions), https://arxiv.org/abs/1104.1776.
-/
public theorem_wanted degreeNineCutsOutSalmonVariety_holds : degreeNineCutsOutSalmonVariety

end MathlibExt.AlgebraicGeometry.SalmonSetTheoreticAMR146Problem0001Wanted
