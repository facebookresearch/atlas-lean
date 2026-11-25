/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Factorization of Eulerian polynomials and solvability (Kourovka Notebook Problem 11.104)

Kourovka Notebook, Archive of Solved Problems, Problem 11.104 (G. E. Wall): for a finite group `G`
define `f(H) = x_p^α x_q^β ⋯` when `|H| = p^α q^β ⋯`, and `φ` by `∑_{K ≤ H} φ(K) = f(H)`; `f(G)` and
`φ(G)` are the order and Eulerian polynomials of `G`. If `G` is `p`-solvable, `φ(G)` is a product of
a polynomial in `x_p` and a polynomial in the remaining variables; if `G` is solvable, `φ(G)` is a
product of polynomials in single variables. Are the converses true (a) for solvable groups? (b) for
`p`-solvable groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.EulerianPolynomialFactorizationKourovka11Problem104Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.104 (G. E.
Wall). UnsolvedMath record UM-00700796 (`KOU-11.104`), dataset ulamai/UnsolvedMath v1.8.0.

The variable `x_p` is the `MvPolynomial` variable indexed by the prime `p`, with integer
coefficients. The relation `∑_{K ≤ H} φ(K) = f(H)` determines `φ` uniquely (induction on `H`), so
the targets quantify over every `φ` satisfying it. In (a) the factors are polynomials in single
prime-indexed variables, over a finite set of primes. `p`-solvable means a subnormal series whose
factors are `p`-groups or have order prime to `p`.
-/

/-- **Order polynomial of a subgroup.** For a subgroup $H$ of a group, the order polynomial of $H$
is $f(H) = \prod_p x_p^{v_p(|H|)}$ in the integer polynomial ring $\mathbb{Z}[x_0, x_1, \dots]$,
where $p$ runs over the primes, $x_p$ is the variable indexed by $p$, and $v_p(|H|)$ is the
exponent of $p$ in the order $|H|$ of $H$. If $H$ is infinite, $f(H) = 1$. -/
noncomputable def orderPolynomial {G : Type*} [Group G] (H : Subgroup G) : MvPolynomial ℕ ℤ :=
  (Nat.card H).factorization.prod fun p a => MvPolynomial.X p ^ a

/-- **Eulerian function of a group (G. E. Wall).** Let $G$ be a group and let $f$ be the order
polynomial. A function $\varphi$ from the subgroups of $G$ to the integer polynomial ring
$\mathbb{Z}[x_0, x_1, \dots]$ is an Eulerian function of $G$ if $\sum_{K \le H} \varphi(K) = f(H)$
for every subgroup $H$ of $G$, the sum running over the subgroups $K$ of $H$. The value
$\varphi(G)$ is the Eulerian polynomial of $G$.

For finite $G$ this relation determines $\varphi$ uniquely, by induction on $H$. If infinitely many
subgroups $K \le H$ have $\varphi(K) \ne 0$, the sum is read as $0$. -/
def IsEulerianFunction {G : Type*} [Group G] (φ : Subgroup G → MvPolynomial ℕ ℤ) : Prop :=
  ∀ H : Subgroup G, ∑ᶠ (K : Subgroup G) (_ : K ≤ H), φ K = orderPolynomial H

/-- **$p$-solvable group.** For a natural number $p$, a group $G$ is $p$-solvable if it has a chain
of subgroups $1 = N_0 \le N_1 \le \dots \le N_n = G$ in which each $N_i$ is normal in $N_{i+1}$ and
each index $[N_{i+1} : N_i]$, taken to be $0$ when it is infinite, is a power $p^k$ with $k \ge 0$
or is coprime to $p$. For finite $G$ and prime $p$ this says that every factor $N_{i+1}/N_i$ is a
$p$-group or has order prime to $p$. -/
def IsPSolvable (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (N : ℕ → Subgroup G), N 0 = ⊥ ∧ N n = ⊤ ∧ ∀ i < n, N i ≤ N (i + 1) ∧
    ((N i).subgroupOf (N (i + 1))).Normal ∧
    ((∃ k : ℕ, (N i).relIndex (N (i + 1)) = p ^ k) ∨ Nat.Coprime ((N i).relIndex (N (i + 1))) p)

/-- **Kourovka Problem 11.104(a) (Eulerian polynomials and solvability, G. E. Wall).** This is the
statement that for every finite group $G$ and every Eulerian function $\varphi$ of $G$, with values
in the integer polynomial ring $\mathbb{Z}[x_0, x_1, \dots]$: if there are a finite set $S$ of
primes and, for each $q \in S$, an integer polynomial $P_q$ involving no variable other than $x_q$,
such that the Eulerian polynomial $\varphi(G)$ equals $\prod_{q \in S} P_q$, then $G$ is
solvable. -/
def eulerianPolynomialSplitsSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (φ : Subgroup G → MvPolynomial ℕ ℤ), IsEulerianFunction φ →
    (∃ (s : Finset ℕ) (P : ℕ → MvPolynomial ℕ ℤ), (∀ q ∈ s, q.Prime ∧ (P q).vars ⊆ {q}) ∧
      φ ⊤ = ∏ q ∈ s, P q) →
    Group.IsSolvable G

/-- **Kourovka Problem 11.104(b) (Eulerian polynomials and $p$-solvability).** This is the
statement that for every finite group $G$, every prime $p$ and every Eulerian function $\varphi$ of
$G$, with values in the integer polynomial ring $\mathbb{Z}[x_0, x_1, \dots]$: if the Eulerian
polynomial $\varphi(G)$ is a product $PQ$ of integer polynomials where $P$ involves no variable
other than $x_p$ and $x_p$ does not occur in $Q$, then $G$ is $p$-solvable. -/
def eulerianPolynomialSeparatesPSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ φ : Subgroup G → MvPolynomial ℕ ℤ,
    IsEulerianFunction φ →
    (∃ P Q : MvPolynomial ℕ ℤ, P.vars ⊆ {p} ∧ p ∉ Q.vars ∧ φ ⊤ = P * Q) → IsPSolvable p G

/--
**Solvability from one-variable factorizations of the Eulerian polynomial.** Let $G$ be a finite
group and let $\varphi$ be an Eulerian function of $G$, with values in the integer polynomial ring
$\mathbb{Z}[x_0, x_1, \dots]$. If there are a finite set $S$ of primes and, for each $q \in S$, an
integer polynomial $P_q$ involving no variable other than $x_q$, such that the Eulerian polynomial
$\varphi(G)$ equals $\prod_{q \in S} P_q$, then $G$ is solvable.

Resolved true: the Kourovka Archive answers 11.104(a) Yes, citing Detomi and Lucchini (2004).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.104
(G. E. Wall); resolution: E. Detomi and A. Lucchini, J. London Math. Soc. (2) 70 (2004), 165-181
(a); E. Damian and A. Lucchini, Commun. Algebra 35 (2007), 3451-3472 (b), Kourovka Archive, Problem
11.104 ("Yes, the converses are true").
-/
public theorem_wanted eulerianPolynomialSplitsSolvable_holds : eulerianPolynomialSplitsSolvable

/--
**Eulerian polynomial factorization implies $p$-solvability.** Let $G$ be a finite group, let $p$
be a prime, and let $\varphi$ be an Eulerian function of $G$, with values in the integer polynomial
ring $\mathbb{Z}[x_0, x_1, \dots]$. If the Eulerian polynomial $\varphi(G)$ is a product $PQ$ of
integer polynomials where $P$ involves no variable other than $x_p$ and $x_p$ does not occur in
$Q$, then $G$ is $p$-solvable.

Resolved true: the Kourovka Archive answers 11.104(b) Yes, citing Damian and Lucchini (2007).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.104
(G. E. Wall); resolution: E. Detomi and A. Lucchini, J. London Math. Soc. (2) 70 (2004), 165-181
(a); E. Damian and A. Lucchini, Commun. Algebra 35 (2007), 3451-3472 (b), Kourovka Archive, Problem
11.104 ("Yes, the converses are true").
-/
public theorem_wanted eulerianPolynomialSeparatesPSolvable_holds :
    eulerianPolynomialSeparatesPSolvable

end MathlibExt.GroupTheory.EulerianPolynomialFactorizationKourovka11Problem104Wanted
