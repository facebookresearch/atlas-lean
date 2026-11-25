/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `p`-parts of character degrees of Sylow subgroups (Kourovka Notebook Problem 15.62)

Kourovka Notebook, Archive of Solved Problems, Problem 15.62 (A. Moretó): for an irreducible
character `χ` of a finite group `G` let `p^(e_p(χ))` be the `p`-part of `χ(1)`, and let `e_p(G) =
max e_p(χ)`. If `P` is a Sylow `p`-subgroup of `G`, is `e_p(P)` bounded above by a function of
`e_p(G)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

namespace MathlibExt.GroupTheory.SylowCharacterDegreePPartKourovka15Problem62Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.62 (A.
Moretó). UnsolvedMath record UM-00701150 (`KOU-15.62`), dataset ulamai/UnsolvedMath v1.8.0.

Irreducible character degrees are the dimensions of the irreducible finite-dimensional complex
representations (`Representation ℂ G V` with Mathlib's `ρ.IsIrreducible`: `V ≠ 0` and no invariant
subspaces other than `0` and `V`), and
`e_p(G)` is the supremum, a maximum since the set is finite, of the `p`-adic valuations of these
degrees. The function is one function of `e_p(G)` for all primes, as the problem asks (it does not
allow a dependence on `p`, unlike 15.32). Yang and Qian's bound has an absolute constant `k`, and
`e_p(P) ≤ e_p(G) + log_p |P : O_p(G)|` (Clifford theory over the normal `p`-subgroup `O_p(G) ≤ P`,
with `|P : O_p(G)| = |G : F(G)|_p`), so `f(e) = (k + 1) e` works.
-/

/-- **Irreducible complex representation degrees.** For a group $G$, the set of natural numbers $d$
such that $G$ has an irreducible complex representation of finite dimension $d$; for a finite
group these are the degrees $\chi(1)$ of its irreducible characters. -/
def irreducibleDegrees (G : Type*) [Group G] : Set ℕ :=
  {d | ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ Module.finrank ℂ V = d}

/-- **Largest $p$-adic exponent of the irreducible degrees.** For a natural number $p$ and a group
$G$, $e_p(G)$ is the supremum in $\mathbb{N}$ of the exponents of $p$ in the prime factorizations
of the dimensions of the finite-dimensional irreducible complex representations of $G$, where the
supremum of an empty or unbounded set is $0$. For a prime $p$ and a finite group $G$, it is the
largest $e$ such that $p^e$ divides the degree $\chi(1)$ of some irreducible character $\chi$ of
$G$. -/
noncomputable def maxPPartExponent (p : ℕ) (G : Type*) [Group G] : ℕ :=
  sSup ((fun d => d.factorization p) '' irreducibleDegrees G)

/-- **Kourovka Problem 15.62 ($p$-parts of character degrees of Sylow subgroups).** The statement,
asked by A. Moretó, that there is a function $f \colon \mathbb{N} \to \mathbb{N}$ such that
$e_p(P) \le f(e_p(G))$ for every prime $p$, every finite group $G$ and every Sylow $p$-subgroup $P$
of $G$, where $e_p(H)$ is the largest exponent of $p$ dividing an irreducible character degree of
$H$. -/
def sylowCharacterDegreeExponentBounded : Prop :=
  ∃ f : ℕ → ℕ, ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G] (P : Sylow p G),
    maxPPartExponent p (P : Subgroup G) ≤ f (maxPPartExponent p G)

/--
**Character degrees of Sylow subgroups are bounded in terms of those of the group.** There is a
function $f \colon \mathbb{N} \to \mathbb{N}$ such that for every prime $p$, every finite group
$G$ and every Sylow $p$-subgroup $P$ of $G$, $e_p(P) \le f(e_p(G))$, where $e_p(H)$ is the
largest exponent of $p$ dividing an irreducible character degree of $H$.

One function works for all primes, since Yang and Qian's bound $|G : F(G)|_p \le p^{k e_p(G)}$,
with $F(G)$ the Fitting subgroup of $G$, has an absolute constant $k$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.62 (A.
Moretó); resolution: Yong Yang and Guohua Qian, Adv. Math. 328 (2018), 356-366, abstract (|G :
F(G)|_p ≤ p^(k e_p(G)) for a constant k, F(G) the Fitting subgroup, which settles Moretó's
conjecture that e_p(P) = log_p b(P), b(P) the largest character degree of P, is bounded by a
function of e_p(G)); Kourovka Archive, Problem 15.62 (answer: Yes, it is true); the solvable case is
due to A. Moretó and T. R. Wolf, Adv. Math. 184 (2004), 18-36.
-/
public theorem_wanted sylowCharacterDegreeExponentBounded_holds :
    sylowCharacterDegreeExponentBounded

end MathlibExt.GroupTheory.SylowCharacterDegreePPartKourovka15Problem62Wanted
