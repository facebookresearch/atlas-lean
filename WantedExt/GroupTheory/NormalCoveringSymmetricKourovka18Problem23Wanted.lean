/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The normal covering number of the symmetric groups (Kourovka Notebook Problem 18.23)

Kourovka Notebook, Archive of Solved Problems, Problem 18.23 (D. Bubboloni, C. E. Praeger, P.
Spiga): the normal covering number `γ(Sₙ)` is the least number of proper subgroups of `Sₙ` such that
every element of `Sₙ` is conjugate to an element of one of them. For `n = p₁^α₁ ⋯ p_r^α_r` with
primes `p₁ < ⋯ < p_r` the conjecture gives `γ(Sₙ)` in four cases; the proposers also ask whether it
holds for `n` sufficiently large.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.GroupTheory.NormalCoveringSymmetricKourovka18Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.23 (D.
Bubboloni, C. E. Praeger, P. Spiga). UnsolvedMath record UM-00701452 (`KOU-18.23`), dataset
ulamai/UnsolvedMath v1.8.0.

The conjectured value is `(n/2)(1 - 1/p₁)` (`r = 1`, `α₁ = 1`), `(n/2)(1 - 1/p₁) + 1` (`r = 1`, `α₁
≥ 2`), `(n/2)(1 - 1/p₁)(1 - 1/p₂) + 1` (`r = 2`, `α₁ + α₂ = 2`) and `(n/2)(1 - 1/p₁)(1 - 1/p₂) + 2`
(`r ≥ 2`, `α₁ + ⋯ + α_r ≥ 3`), computed in `ℚ`. The target is the "for `n` sufficiently large" form;
its refutation also refutes the conjecture for all `n` and avoids small degrees where the formula is
not meant (for `n = 3` it gives `1`, while no finite group is covered by the conjugates of one
proper subgroup).
-/

/-- **Normal covering number of the symmetric group.** For a natural number $n$, the normal
covering number $\gamma(S_n)$ is the least $k$ for which there are proper subgroups
$H_1, \dots, H_k$ of the symmetric group $S_n$ such that every element of $S_n$ is conjugate to an
element of some $H_i$. When no such subgroups exist, as for $n \le 2$, it is $0$. -/
noncomputable def normalCoveringNumber (n : ℕ) : ℕ :=
  sInf {k | ∃ H : Fin k → Subgroup (Equiv.Perm (Fin n)), (∀ i, H i ≠ ⊤) ∧
    ∀ σ : Equiv.Perm (Fin n), ∃ i, ∃ τ ∈ H i, IsConj σ τ}

/-- **Bubboloni–Praeger–Spiga conjectured value.** For a natural number $n \ge 2$, write
$n = p_1^{\alpha_1} \cdots p_r^{\alpha_r}$ with primes $p_1 < \cdots < p_r$ and exponents
$\alpha_i \ge 1$, and let $p_2$ be the least prime factor of $n / p_1^{\alpha_1}$. The conjectured
value of $n$ is the rational number $\frac{n}{2}(1 - \frac{1}{p_1})$ if $r = 1$ and $\alpha_1 = 1$;
$\frac{n}{2}(1 - \frac{1}{p_1}) + 1$ if $r = 1$ and $\alpha_1 \ge 2$;
$\frac{n}{2}(1 - \frac{1}{p_1})(1 - \frac{1}{p_2}) + 1$ if $r = 2$ and $\alpha_1 = \alpha_2 = 1$;
and $\frac{n}{2}(1 - \frac{1}{p_1})(1 - \frac{1}{p_2}) + 2$ if $r \ge 2$ and
$\alpha_1 + \cdots + \alpha_r \ge 3$. For $n = 0$ and $n = 1$ the value is $2$. -/
def conjecturedValue (n : ℕ) : ℚ :=
  let p₁ := n.minFac
  let p₂ := (n / p₁ ^ n.factorization p₁).minFac
  let a : ℚ := n / 2 * (1 - 1 / (p₁ : ℚ))
  let b : ℚ := a * (1 - 1 / (p₂ : ℚ))
  if n.primeFactors.card = 1 then
    (if n.primeFactorsList.length = 1 then a else a + 1)
  else if n.primeFactorsList.length = 2 then b + 1 else b + 2

/-- **Bubboloni–Praeger–Spiga normal covering conjecture (eventual form).** There is a natural
number $N$ such that, for every $n \ge N$, the normal covering number $\gamma(S_n)$ of the
symmetric group $S_n$ equals the Bubboloni–Praeger–Spiga conjectured value of $n$.

This is Kourovka Problem 18.23 (D. Bubboloni, C. E. Praeger, P. Spiga) in the form "for all
sufficiently large $n$" that the proposers single out. -/
def normalCoveringNumberEventuallyConjectured : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (normalCoveringNumber n : ℚ) = conjecturedValue n

/--
**Refutation of the Bubboloni–Praeger–Spiga normal covering conjecture.** It is not the case
that there is a natural number $N$ such that, for every $n \ge N$, the normal covering number
$\gamma(S_n)$ of the symmetric group $S_n$ equals the Bubboloni–Praeger–Spiga conjectured value
of $n$. In other words, the conjecture fails for arbitrarily large $n$.

The Kourovka Archive records that A. Maróti showed the conjecture incorrect for odd $n$. His
covering, given in Section 2 of Bubboloni–Praeger–Spiga (2020), yields
$\gamma(S_n) \le n/3 + \varphi(n)/2 + \omega(n)$, where $\varphi$ is Euler's function and
$\omega(n)$ the number of distinct prime factors of $n$. This is below the conjectured value when
$n$ is the product of $r$ consecutive primes starting at a prime $p \ge 43$ and $r$ is large.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 18.23 (D. Bubboloni, C. E. Praeger, P. Spiga); resolution: D. Bubboloni, C.
E. Praeger and P. Spiga, Linear bounds for the normal covering number of the symmetric and
alternating groups, Monatsh. Math. 191 (2020), 229-247, Section 2, A. Maróti's construction: for n =
N(r, p), the product of r consecutive primes starting at p ≥ 43, and r ≥ r*, γ(Sym(n)) < (n/2)(1 -
1/p₁)(1 - 1/p₂) + 2, contradicting the conjecture for infinitely many p and r; Kourovka Archive,
Problem 18.23,
https://api.research-repository.uwa.edu.au/ws/files/49055019/Bubboloni_et_al_2019_Linear_bounds_for_the_normal_covering.pdf.
-/
public theorem_wanted normalCoveringNumberEventuallyConjectured_refuted :
    ¬ normalCoveringNumberEventuallyConjectured

end MathlibExt.GroupTheory.NormalCoveringSymmetricKourovka18Problem23Wanted
