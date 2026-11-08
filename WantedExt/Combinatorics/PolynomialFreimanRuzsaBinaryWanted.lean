/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial Freiman–Ruzsa conjecture over binary vector spaces

`OWR-12177-008`: a doubling set in `𝔽₂ⁿ` contains a large subset with
polynomially bounded span.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.CovBySMul

@[expose] public section

namespace MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted

open scoped Pointwise

/-! Source: UnsolvedMath record `OWR-12177-008`, numeric id 30002239.
Complexity Theory (2013), Oberwolfach Reports,
DOI 10.4171/owr/2012/54, pp. 3267--3304. -/

/-- Polynomial Freiman–Ruzsa conjecture over binary vector spaces
([OWR-12177-008]): for doubling parameter `K ≥ 1`, polynomials `P Q`
independent of `n`, `A`, `K` witness that every nonempty `A : Finset 𝔽₂ⁿ`
with `|A + A| ≤ K * |A|` has a subset `A'` with `|A| / P(K) ≤ |A'|` and
`|span(A')| ≤ Q(K) * |A'|`. Resolved (true): proved by Gowers, Green,
Manners, and Tao (arXiv:2311.05762); stated as a proposition here. -/
def conjecture : Prop :=
  ∃ P Q : Polynomial ℝ,
    (∀ K : ℝ, 1 ≤ K → 0 < P.eval K ∧ 0 < Q.eval K) ∧
    ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (K : ℝ),
      1 ≤ K →
      A.Nonempty →
      ((((A.product A).image (fun p => p.1 + p.2)).card : ℝ)) ≤ K * (A.card : ℝ) →
      ∃ A' : Finset (Fin n → ZMod 2), A' ⊆ A ∧
        (A.card : ℝ) / P.eval K ≤ (A'.card : ℝ) ∧
        (Nat.card ↥(Submodule.span (ZMod 2) (↑A' : Set (Fin n → ZMod 2))) : ℝ) ≤
          Q.eval K * (A'.card : ℝ)

/--
Resolved true: Proved by Gowers, Green, Manners, and Tao (arXiv:2311.05762, November 2023): the
polynomial Freiman-Ruzsa conjecture in characteristic 2 (Marton's conjecture over F_2^n). Their
polynomial coset-cover result implies this large-subset polynomial-span formulation via the
densest-coset argument. Source: W. T. Gowers, B. Green, F. Manners, T. Tao, On a conjecture of
Marton, arXiv:2311.05762 (November 2023), https://arxiv.org/abs/2311.05762. Moved from
`OpenConjectures/Combinatorics/PolynomialFreimanRuzsaBinary`.
-/
public theorem_wanted conjecture_holds : conjecture

/-! ## Optimization Problems constant 18a -/

/-- The ambient binary vector space `𝔽₂ⁿ`.
Source: Optimization Problems constant 18a. -/
abbrev BinaryAmbientSpace (n : ℕ) := Fin n → ZMod 2

/--
`C` is an admissible asymptotic coset-cover exponent.  The
`∀ ε > 0, ∃ K₀, ∀ K ≥ K₀` prefix is the source's uniform
`K^(C + o(1))` convention: after `K` is sufficiently large, the same
bound works in every dimension and for every nonempty doubling set.

`CovByVAdd` is Mathlib's concrete finite-coset-cover predicate.  Thus the
conclusion supplies an actual linear subspace and an actual finite set of
translates, rather than a caller-provided cover oracle.

Source: Optimization Problems constant 18a, with the uniform asymptotic
quantifiers made explicit. -/
def IsAsymptoticCosetCoverExponent (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧
      ∀ K : ℝ, K₀ ≤ K →
        ∀ (n : ℕ) (A : Finset (BinaryAmbientSpace n)), A.Nonempty →
          ((A + A).card : ℝ) ≤ K * (A.card : ℝ) →
            ∃ H : Submodule (ZMod 2) (BinaryAmbientSpace n),
              Nat.card H ≤ A.card ∧
                CovByVAdd (BinaryAmbientSpace n) (Real.rpow K (C + ε))
                  (A : Set (BinaryAmbientSpace n)) (H : Set (BinaryAmbientSpace n))

/-- The set of admissible asymptotic coset-cover exponents.
Source: Optimization Problems constant 18a. -/
def asymptoticCosetCoverExponents : Set ℝ :=
  {C | IsAsymptoticCosetCoverExponent C}

/-- Optimization Problems constant 18a, the infimum of admissible exponents.
Source: Optimization Problems constant 18a. -/
noncomputable def martonPFRCoverExponent : ℝ :=
  sInf asymptoticCosetCoverExponents

/-- The source's literal least-exponent clause, separated from totalized `sInf`.
Source: Optimization Problems constant 18a. -/
def leastCoverExponentClaim : Prop :=
  IsLeast asymptoticCosetCoverExponents martonPFRCoverExponent

/-- Marton's historical finiteness claim, now resolved by the quantitative bounds.
Source: Optimization Problems constant 18a and GGMT, arXiv:2311.05762. -/
def martonPFRFinitenessTheorem : Prop :=
  asymptoticCosetCoverExponents.Nonempty

/-- Gowers--Green--Manners--Tao's refined exponent `7 + √17`.
Source: GGMT, arXiv:2311.05762, and Optimization Problems constant 18a. -/
def ggmt2025UpperBound7Sqrt17 : Prop :=
  IsAsymptoticCosetCoverExponent (7 + Real.sqrt 17)

/-- Liao's exponent-nine improvement.
Source: J.-J. Liao, arXiv:2404.09639, Theorem 1.1. -/
def liao2024UpperBound9 : Prop :=
  IsAsymptoticCosetCoverExponent 9

/-- The simplified exponent-eleven consequence recorded by Liao.
Source: J.-J. Liao, arXiv:2404.09639, Theorem 1.2 and the implication `C ≤ C' + 1`. -/
def liao2024SimplifiedUpperBound11 : Prop :=
  IsAsymptoticCosetCoverExponent 11

/-- The basis-vector obstruction: every admissible exponent is at least one.
Source: Optimization Problems constant 18a. -/
def basisVectorsLowerBound1 : Prop :=
  ∀ C : ℝ, IsAsymptoticCosetCoverExponent C → 1 ≤ C

/-- The asymptotic exponent has the source's asserted least-element property.
Source: Optimization Problems constant 18a. -/
public theorem_wanted leastCoverExponentClaim_holds : leastCoverExponentClaim

/-- GGMT's quantitative coset-cover theorem gives exponent `7 + √17`.
Source: GGMT, arXiv:2311.05762, and Optimization Problems constant 18a. -/
public theorem_wanted ggmt2025UpperBound7Sqrt17_holds : ggmt2025UpperBound7Sqrt17

/-- Liao's quantitative coset-cover theorem gives exponent `9`.
Source: J.-J. Liao, arXiv:2404.09639, Theorem 1.1. -/
public theorem_wanted liao2024UpperBound9_holds : liao2024UpperBound9

/-- Liao's simplified argument gives exponent `11`.
Source: J.-J. Liao, arXiv:2404.09639, Theorem 1.2 and the implication `C ≤ C' + 1`. -/
public theorem_wanted liao2024SimplifiedUpperBound11_holds :
  liao2024SimplifiedUpperBound11

/-- Basis vectors force the asymptotic exponent to be at least one.
Source: Optimization Problems constant 18a. -/
public theorem_wanted basisVectorsLowerBound1_holds : basisVectorsLowerBound1

end MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted
