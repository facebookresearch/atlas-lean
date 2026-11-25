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

/-- **$(3+1)$-free posets.** A partially ordered set $P$ is $(3+1)$-free when there are no
elements $a, b, c, d \in P$ with $a < b < c$ such that $d$ is incomparable to each of $a$, $b$
and $c$ (neither $d \le x$ nor $x \le d$ for $x = a, b, c$). -/
def IsThreePlusOneFree (P : Type*) [PartialOrder P] : Prop :=
  ¬ ∃ a b c d : P, a < b ∧ b < c ∧ (¬ a ≤ d ∧ ¬ d ≤ a) ∧ (¬ b ≤ d ∧ ¬ d ≤ b) ∧
    (¬ c ≤ d ∧ ¬ d ≤ c)

/-- **Incomparability graph of a poset.** The incomparability graph $\operatorname{inc}(P)$ of a
partially ordered set $P$ is the simple graph on $P$ in which two distinct elements $x$ and $y$ are
adjacent when they are incomparable, that is, neither $x \le y$ nor $y \le x$. -/
def incomparabilityGraph (P : Type*) [PartialOrder P] : SimpleGraph P :=
  SimpleGraph.fromRel fun x y => ¬ x ≤ y ∧ ¬ y ≤ x

open Classical in
/-- **Chromatic symmetric function in as many variables as vertices.** For a simple graph $G$ on
a finite vertex set $V$ with $n = |V|$ elements, $X_G$ is the polynomial with integer coefficients
in the variables $x_0, \dots, x_{n-1}$ given by $X_G = \sum_{\kappa} \prod_{v \in V} x_{\kappa(v)}$,
where $\kappa$ ranges over the proper colourings $\kappa : V \to \{0, \dots, n - 1\}$ of $G$, that
is, the maps with $\kappa(u) \ne \kappa(v)$ whenever $u$ and $v$ are adjacent. -/
noncomputable def chromaticSymmetricPoly {V : Type*} [Fintype V] (G : SimpleGraph V) :
    MvPolynomial (Fin (Fintype.card V)) ℤ :=
  ∑ κ ∈ Finset.univ.filter (fun κ : V → Fin (Fintype.card V) => ∀ u v, G.Adj u v → κ u ≠ κ v),
    ∏ v, MvPolynomial.X (κ v)

/-- **$e$-positive polynomials.** A polynomial $f$ with integer coefficients in the $n$ variables
$x_0, \dots, x_{n-1}$ is $e$-positive when $f = \sum_{\lambda} c_\lambda e_\lambda$ for some
natural numbers $c_\lambda$, where $\lambda = (\lambda_1, \dots, \lambda_k)$ ranges over the
partitions of $n$ and $e_\lambda = e_{\lambda_1} \cdots e_{\lambda_k}$ is the product of the
elementary symmetric polynomials $e_{\lambda_i}$ in $x_0, \dots, x_{n-1}$. -/
def IsEPositive {n : ℕ} (f : MvPolynomial (Fin n) ℤ) : Prop :=
  ∃ c : Nat.Partition n → ℕ, f = ∑ p : Nat.Partition n,
    (c p : MvPolynomial (Fin n) ℤ) * (p.parts.map fun i => MvPolynomial.esymm (Fin n) ℤ i).prod

/-- **Statement of the Stanley–Stembridge conjecture.** The proposition that for every finite
$(3+1)$-free partially ordered set $P$, the chromatic symmetric function in $|P|$ variables of the
incomparability graph of $P$ is $e$-positive. -/
def stanleyStembridge : Prop :=
  ∀ (P : Type) [Fintype P] [PartialOrder P], IsThreePlusOneFree P →
    IsEPositive (chromaticSymmetricPoly (incomparabilityGraph P))

/--
**Hikita's theorem: the Stanley–Stembridge conjecture holds.** For every finite $(3+1)$-free
partially ordered set $P$, the chromatic symmetric function in $|P|$ variables of the
incomparability graph of $P$ is $e$-positive.

Source: R. P. Stanley,
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
