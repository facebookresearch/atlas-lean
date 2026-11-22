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

/-- The order polynomial `f(H) = ∏_p x_p ^ {v_p(|H|)}` of a subgroup `H`, in `ℤ[x₀, x₁, …]`
(the variable `x_p` is the one indexed by the prime `p`). -/
noncomputable def orderPolynomial {G : Type*} [Group G] (H : Subgroup G) : MvPolynomial ℕ ℤ :=
  (Nat.card H).factorization.prod fun p a => MvPolynomial.X p ^ a

/-- `φ` is the Eulerian function of the finite group `G` (G. E. Wall): `∑_{K ≤ H} φ(K) = f(H)` for
every subgroup `H`. This determines `φ` uniquely, by induction on `H`; `φ ⊤` is the Eulerian
polynomial `φ(G)`. -/
def IsEulerianFunction {G : Type*} [Group G] (φ : Subgroup G → MvPolynomial ℕ ℤ) : Prop :=
  ∀ H : Subgroup G, ∑ᶠ (K : Subgroup G) (_ : K ≤ H), φ K = orderPolynomial H

/-- `G` is `p`-solvable: it has a subnormal series `1 = N₀ ≤ N₁ ≤ ⋯ ≤ Nₙ = G` each of whose factors
`Nᵢ₊₁ / Nᵢ` is a `p`-group or has order prime to `p`. -/
def IsPSolvable (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (N : ℕ → Subgroup G), N 0 = ⊥ ∧ N n = ⊤ ∧ ∀ i < n, N i ≤ N (i + 1) ∧
    ((N i).subgroupOf (N (i + 1))).Normal ∧
    ((∃ k : ℕ, (N i).relIndex (N (i + 1)) = p ^ k) ∨ Nat.Coprime ((N i).relIndex (N (i + 1))) p)

/-- Kourovka 11.104(a) (G. E. Wall): a finite group whose Eulerian polynomial is a product of
polynomials each in a single variable `x_p` (one for each prime in a finite set) is solvable. -/
def eulerianPolynomialSplitsSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (φ : Subgroup G → MvPolynomial ℕ ℤ), IsEulerianFunction φ →
    (∃ (s : Finset ℕ) (P : ℕ → MvPolynomial ℕ ℤ), (∀ q ∈ s, q.Prime ∧ (P q).vars ⊆ {q}) ∧
      φ ⊤ = ∏ q ∈ s, P q) →
    Group.IsSolvable G

/-- Kourovka 11.104(b): if the Eulerian polynomial of a finite group `G` is the product of a
polynomial in `x_p` and a polynomial in the remaining variables, then `G` is `p`-solvable. -/
def eulerianPolynomialSeparatesPSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ φ : Subgroup G → MvPolynomial ℕ ℤ,
    IsEulerianFunction φ →
    (∃ P Q : MvPolynomial ℕ ℤ, P.vars ⊆ {p} ∧ p ∉ Q.vars ∧ φ ⊤ = P * Q) → IsPSolvable p G

/--
Resolved true: the Kourovka Archive answers 11.104(a) Yes, citing Detomi and Lucchini (2004): a
finite group whose Eulerian polynomial is a product of polynomials each in a single variable is
solvable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.104
(G. E. Wall); resolution: E. Detomi and A. Lucchini, J. London Math. Soc. (2) 70 (2004), 165-181
(a); E. Damian and A. Lucchini, Commun. Algebra 35 (2007), 3451-3472 (b), Kourovka Archive, Problem
11.104 ("Yes, the converses are true").
-/
public theorem_wanted eulerianPolynomialSplitsSolvable_holds : eulerianPolynomialSplitsSolvable

/--
Resolved true: the Kourovka Archive answers 11.104(b) Yes, citing Damian and Lucchini (2007): if
`φ(G)` is the product of a polynomial in `x_p` and a polynomial in the other variables, then `G` is
`p`-solvable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.104
(G. E. Wall); resolution: E. Detomi and A. Lucchini, J. London Math. Soc. (2) 70 (2004), 165-181
(a); E. Damian and A. Lucchini, Commun. Algebra 35 (2007), 3451-3472 (b), Kourovka Archive, Problem
11.104 ("Yes, the converses are true").
-/
public theorem_wanted eulerianPolynomialSeparatesPSolvable_holds :
    eulerianPolynomialSeparatesPSolvable

end MathlibExt.GroupTheory.EulerianPolynomialFactorizationKourovka11Problem104Wanted
