/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Stanley-Stembridge conjecture (Stanley, Positivity Problems, Problem 21)

R. P. Stanley, Positivity problems and conjectures in algebraic combinatorics, Problem 21
(Stanley-Stembridge): let `P` be a finite `(3+1)`-free poset and `G = inc(P)` its incomparability
graph. Is the chromatic symmetric function `X_G` `e`-positive?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.StanleyStembridgeEPositivityAMR156Problem0022Wanted

/-!
Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 21 (Stanley-Stembridge conjecture; Stanley and Stembridge, J. Combin. Theory Ser. A 62
(1993), Conjecture 5.5). UnsolvedMath record UM-00801196 (`AMR-156-0022`), dataset
ulamai/UnsolvedMath v1.8.0.

`X_G` is written in `n = |V|` variables: the sum of `∏_v x_{κ v}` over proper colourings `κ : V →
Fin n`. Restricting a symmetric function of degree `n` to `n` variables is injective, the products
`e_λ`, `λ ⊢ n`, stay linearly independent there, and colourings using a colour `≥ n` only contribute
monomials in the omitted variables; so `X_G` is `e`-positive exactly when this polynomial is a
nonnegative integer combination of the `e_λ(x₀, …, x_{n-1})`. A `(3+1)`-free poset has no `a < b <
c` with an element `d` incomparable to all three; posets are finite types in `Type`. The same
conjecture is Conjecture 1 of P. Brosnan's report in Oberwolfach Report 5/2016, pp. 222-223
(UnsolvedMath record `OWR-14213-006`), stated there for the graphs `G(m)` of Hessenberg functions,
to which Guay-Paquet reduced the general case (the report's Remark 2); the classical `(3+1)`-free
form is stated here. MathlibExt's `SimpleGraph.chromaticProfileCount` counts the colourings behind
each coefficient of `X_G`; the `e`-expansion needs the polynomial itself, defined below.
-/

/-- `P` is `(3+1)`-free: no induced subposet is a `3`-element chain together with an element
incomparable to each of its elements. -/
def IsThreePlusOneFree (P : Type*) [PartialOrder P] : Prop :=
  ¬ ∃ a b c d : P, a < b ∧ b < c ∧ (¬ a ≤ d ∧ ¬ d ≤ a) ∧ (¬ b ≤ d ∧ ¬ d ≤ b) ∧
    (¬ c ≤ d ∧ ¬ d ≤ c)

/-- The incomparability graph `inc(P)`: distinct elements are adjacent when they are
incomparable. -/
def incomparabilityGraph (P : Type*) [PartialOrder P] : SimpleGraph P :=
  SimpleGraph.fromRel fun x y => ¬ x ≤ y ∧ ¬ y ≤ x

open Classical in
/-- The chromatic symmetric function `X_G` of a graph on `n = |V|` vertices, in the variables
`x₀, …, x_{n-1}`: the sum of `∏_v x_{κ v}` over all proper colourings `κ : V → Fin n`. -/
noncomputable def chromaticSymmetricPoly {V : Type*} [Fintype V] (G : SimpleGraph V) :
    MvPolynomial (Fin (Fintype.card V)) ℤ :=
  ∑ κ ∈ Finset.univ.filter (fun κ : V → Fin (Fintype.card V) => ∀ u v, G.Adj u v → κ u ≠ κ v),
    ∏ v, MvPolynomial.X (κ v)

/-- A polynomial in `n` variables is `e`-positive: a combination with nonnegative integer
coefficients of the products `e_λ = ∏ᵢ e_{λᵢ}` of elementary symmetric polynomials over the
partitions `λ` of `n`. -/
def IsEPositive {n : ℕ} (f : MvPolynomial (Fin n) ℤ) : Prop :=
  ∃ c : Nat.Partition n → ℕ, f = ∑ p : Nat.Partition n,
    (c p : MvPolynomial (Fin n) ℤ) * (p.parts.map fun i => MvPolynomial.esymm (Fin n) ℤ i).prod

/-- The Stanley–Stembridge conjecture (Stanley, Positivity Problems, Problem 21): the chromatic
symmetric function of the incomparability graph of every finite `(3+1)`-free poset is
`e`-positive. -/
def stanleyStembridge : Prop :=
  ∀ (P : Type) [Fintype P] [PartialOrder P], IsThreePlusOneFree P →
    IsEPositive (chromaticSymmetricPoly (incomparabilityGraph P))

/--
Resolved true: Hikita proved that the coefficients of the `e`-expansion of the chromatic
quasisymmetric function of every unit interval graph are nonnegative and, as a corollary, the
Stanley-Stembridge conjecture (J. Amer. Math. Soc., Early View 2026). Source: R. P. Stanley,
Positivity Problems and Conjectures in Algebraic Combinatorics (1999), Problem 21
(Stanley-Stembridge conjecture; Stanley and Stembridge, J. Combin. Theory Ser. A 62 (1993),
Conjecture 5.5); resolution: T. Hikita, A proof of the Stanley-Stembridge conjecture, J. Amer. Math.
Soc., published online (Early View) 2026-08-28, doi:10.1090/jams/1090,
https://www.ams.org/jams/earlyview/#jams1090; arXiv:2410.12758, Abstract: a probabilistic
interpretation of the coefficients of the elementary symmetric function expansion of the chromatic
quasisymmetric function of every unit interval graph, 'As a corollary, we prove the
Stanley-Stembridge conjecture'; Section 1.1: the positivity of these coefficients 'is sufficient to
conclude that the original Stanley-Stembridge conjecture is true',
https://doi.org/10.1090/jams/1090.
-/
public theorem_wanted stanleyStembridge_holds : stanleyStembridge

end MathlibExt.Combinatorics.StanleyStembridgeEPositivityAMR156Problem0022Wanted
