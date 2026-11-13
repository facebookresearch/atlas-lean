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

/-- **Polynomial Freiman–Ruzsa conjecture over $\mathbb{F}_2$.** There are real polynomials $P$
and $Q$, with $P(K) > 0$ and $Q(K) > 0$ for every real $K \ge 1$, such that for every
$n \in \mathbb{N}$, every nonempty finite set $A \subseteq \mathbb{F}_2^n$ and every real $K \ge 1$
with $|A + A| \le K|A|$, there is a subset $A' \subseteq A$ with $|A| / P(K) \le |A'|$ and
$|\operatorname{span}(A')| \le Q(K)\,|A'|$, where $\operatorname{span}(A')$ is the
$\mathbb{F}_2$-linear span of $A'$.

The problem is recorded as OWR-12177-008. It was proved by Gowers, Green, Manners and Tao
(arXiv:2311.05762). -/
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
**Gowers–Green–Manners–Tao theorem (polynomial Freiman–Ruzsa over $\mathbb{F}_2$).** The
polynomial Freiman–Ruzsa conjecture over $\mathbb{F}_2$ holds: there are real polynomials $P$ and
$Q$, with $P(K) > 0$ and $Q(K) > 0$ for every real $K \ge 1$, such that for every
$n \in \mathbb{N}$, every nonempty finite set $A \subseteq \mathbb{F}_2^n$ and every real $K \ge 1$
with $|A + A| \le K|A|$, there is a subset $A' \subseteq A$ with $|A| / P(K) \le |A'|$ and
$|\operatorname{span}(A')| \le Q(K)\,|A'|$, where $\operatorname{span}(A')$ is the
$\mathbb{F}_2$-linear span of $A'$.

Gowers, Green, Manners and Tao prove that such a set $A$ is covered by polynomially many (in $K$)
cosets of a subspace of size at most $|A|$; the densest of these cosets gives the subset $A'$.

Source: W. T. Gowers, B. Green, F. Manners, T. Tao, On a conjecture of
Marton, arXiv:2311.05762 (November 2023), https://arxiv.org/abs/2311.05762. Moved from
`OpenConjectures/Combinatorics/PolynomialFreimanRuzsaBinary`.
-/
public theorem_wanted conjecture_holds : conjecture

/-! ## Optimization Problems constant 18a -/

/-- **The binary vector space $\mathbb{F}_2^n$.** For a natural number $n$, the ambient space
$\mathbb{F}_2^n$ of all functions from $\{0, 1, \dots, n - 1\}$ to the two-element field
$\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$.

Source: Optimization Problems constant 18a. -/
abbrev BinaryAmbientSpace (n : ℕ) := Fin n → ZMod 2

/--
**Admissible asymptotic coset-cover exponents.** A real number $C$ is an admissible asymptotic
coset-cover exponent if for every real $\varepsilon > 0$ there is a real $K_0 \ge 1$ such that
for every real $K \ge K_0$, every $n \in \mathbb{N}$ and every nonempty finite set
$A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$, there is an $\mathbb{F}_2$-linear subspace
$H$ of $\mathbb{F}_2^n$ with $|H| \le |A|$ such that $A$ is covered by at most $K^{C + \varepsilon}$
translates of $H$: there is a finite set $F \subseteq \mathbb{F}_2^n$ with
$|F| \le K^{C + \varepsilon}$ and $A \subseteq F + H$.

This makes the source's bound of $K^{C + o(1)}$ translates uniform: once $K$ is large enough,
the same bound works in every dimension and for every nonempty set of doubling at most $K$.

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

/-- **The set of admissible coset-cover exponents.** This is the set of all real numbers $C$
that are admissible asymptotic coset-cover exponents: for every real $\varepsilon > 0$ there is a
real $K_0 \ge 1$ such that for every real $K \ge K_0$, every $n \in \mathbb{N}$ and every
nonempty finite set $A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$, there are an
$\mathbb{F}_2$-linear subspace $H$ of $\mathbb{F}_2^n$ with $|H| \le |A|$ and a finite set
$F \subseteq \mathbb{F}_2^n$ with $|F| \le K^{C + \varepsilon}$ and $A \subseteq F + H$.

Source: Optimization Problems constant 18a. -/
def asymptoticCosetCoverExponents : Set ℝ :=
  {C | IsAsymptoticCosetCoverExponent C}

/-- **The Marton coset-cover exponent.** Call a real number $C$ an admissible asymptotic
coset-cover exponent if for every $\varepsilon > 0$ there is $K_0 \ge 1$ such that for every real
$K \ge K_0$, every $n \in \mathbb{N}$ and every nonempty finite set $A \subseteq \mathbb{F}_2^n$
with $|A + A| \le K|A|$, there is a subspace $H$ of $\mathbb{F}_2^n$ with $|H| \le |A|$ such that
$A$ is covered by at most $K^{C + \varepsilon}$ translates of $H$. The Marton coset-cover exponent
is the infimum in $\mathbb{R}$ of the set of admissible exponents, with the convention that this
infimum is $0$ when the set is empty or unbounded below.

Source: Optimization Problems constant 18a. -/
noncomputable def martonPFRCoverExponent : ℝ :=
  sInf asymptoticCosetCoverExponents

/-- **Statement that the Marton coset-cover exponent is attained.** The proposition that the
Marton coset-cover exponent $C^*$, the infimum of the admissible asymptotic coset-cover exponents,
is the least admissible exponent: $C^*$ is itself an admissible asymptotic coset-cover exponent,
and $C^* \le C$ for every admissible asymptotic coset-cover exponent $C$.

Source: Optimization Problems constant 18a. -/
def leastCoverExponentClaim : Prop :=
  IsLeast asymptoticCosetCoverExponents martonPFRCoverExponent

/-- **Statement that an admissible coset-cover exponent exists.** The proposition that some
real number $C$ is an admissible asymptotic coset-cover exponent: for every $\varepsilon > 0$
there is $K_0 \ge 1$ such that for every real $K \ge K_0$, every $n \in \mathbb{N}$ and every
nonempty finite set $A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$, there is a subspace $H$
of $\mathbb{F}_2^n$ with $|H| \le |A|$ such that $A$ is covered by at most $K^{C + \varepsilon}$
translates of $H$.

This is an asymptotic form of Marton's conjecture over $\mathbb{F}_2^n$, which was proved by
Gowers, Green, Manners and Tao.

Source: Optimization Problems constant 18a and GGMT, arXiv:2311.05762. -/
def martonPFRFinitenessTheorem : Prop :=
  asymptoticCosetCoverExponents.Nonempty

/-- **Statement of the Gowers–Green–Manners–Tao exponent $7 + \sqrt{17}$.** The proposition that
$7 + \sqrt{17}$ is an admissible asymptotic coset-cover exponent.

Source: GGMT, arXiv:2311.05762, and Optimization Problems constant 18a. -/
def ggmt2025UpperBound7Sqrt17 : Prop :=
  IsAsymptoticCosetCoverExponent (7 + Real.sqrt 17)

/-- **Statement of Liao's exponent-9 coset-cover bound.** The proposition that $9$ is an admissible
asymptotic coset-cover exponent: for every $\varepsilon > 0$ there is $K_0 \ge 1$ such that for
every real $K \ge K_0$, every $n \in \mathbb{N}$ and every nonempty finite set
$A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$, there is a subspace $H$ of $\mathbb{F}_2^n$
with $|H| \le |A|$ such that $A$ is covered by at most $K^{9 + \varepsilon}$ translates
of $H$.

Source: J.-J. Liao, arXiv:2404.09639, Theorem 1.1. -/
def liao2024UpperBound9 : Prop :=
  IsAsymptoticCosetCoverExponent 9

/-- **Statement of Liao's simplified exponent-11 coset-cover bound.** The proposition that $11$
is an admissible asymptotic coset-cover exponent: for every $\varepsilon > 0$ there is $K_0 \ge 1$
such that for every real $K \ge K_0$, every $n \in \mathbb{N}$ and every nonempty finite set
$A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$, there is a subspace $H$ of $\mathbb{F}_2^n$
with $|H| \le |A|$ such that $A$ is covered by at most $K^{11 + \varepsilon}$ translates of $H$.

Source: J.-J. Liao, arXiv:2404.09639, Theorem 1.2 and the implication `C ≤ C' + 1`. -/
def liao2024SimplifiedUpperBound11 : Prop :=
  IsAsymptoticCosetCoverExponent 11

/-- **Statement of the basis-vector lower bound.** The proposition that every admissible
asymptotic coset-cover exponent $C$ satisfies $C \ge 1$.

The obstruction comes from sets of basis vectors.

Source: Optimization Problems constant 18a. -/
def basisVectorsLowerBound1 : Prop :=
  ∀ C : ℝ, IsAsymptoticCosetCoverExponent C → 1 ≤ C

/-- **The least coset-cover exponent is attained.** The set of admissible asymptotic coset-cover
exponents has a least element, namely its infimum $C^*$ (the Marton cover exponent): $C^*$ is
itself admissible, and $C^* \le C$ for every admissible asymptotic coset-cover exponent $C$.

Source: Optimization Problems constant 18a. -/
public theorem_wanted leastCoverExponentClaim_holds : leastCoverExponentClaim

/-- **Gowers–Green–Manners–Tao exponent $7 + \sqrt{17}$.** The number $7 + \sqrt{17}$ is an
admissible asymptotic coset-cover exponent.

Source: GGMT, arXiv:2311.05762, and Optimization Problems constant 18a. -/
public theorem_wanted ggmt2025UpperBound7Sqrt17_holds : ggmt2025UpperBound7Sqrt17

/-- **Liao's coset-cover bound with exponent 9.** The number $9$ is an admissible
asymptotic coset-cover exponent: for every $\varepsilon > 0$ there is $K_0 \ge 1$ such that for
every real $K \ge K_0$, every $n \in \mathbb{N}$ and every nonempty finite set
$A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$, there is a subspace $H$ of $\mathbb{F}_2^n$
with $|H| \le |A|$ such that $A$ is covered by at most $K^{9 + \varepsilon}$ translates
of $H$.

Source: J.-J. Liao, arXiv:2404.09639, Theorem 1.1. -/
public theorem_wanted liao2024UpperBound9_holds : liao2024UpperBound9

/-- **Liao's simplified coset-cover bound with exponent 11.** The number $11$ is an admissible
asymptotic coset-cover exponent: for every $\varepsilon > 0$ there is $K_0 \ge 1$ such that for
every real $K \ge K_0$, every $n \in \mathbb{N}$ and every nonempty finite set
$A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$, there is a subspace $H$ of $\mathbb{F}_2^n$
with $|H| \le |A|$ such that $A$ is covered by at most $K^{11 + \varepsilon}$ translates
of $H$.

Source: J.-J. Liao, arXiv:2404.09639, Theorem 1.2 and the implication `C ≤ C' + 1`. -/
public theorem_wanted liao2024SimplifiedUpperBound11_holds :
  liao2024SimplifiedUpperBound11

/-- **Basis-vector lower bound for coset-cover exponents.** Every admissible asymptotic
coset-cover exponent $C$ satisfies $C \ge 1$.

The obstruction comes from sets of basis vectors.

Source: Optimization Problems constant 18a. -/
public theorem_wanted basisVectorsLowerBound1_holds : basisVectorsLowerBound1

end MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted
