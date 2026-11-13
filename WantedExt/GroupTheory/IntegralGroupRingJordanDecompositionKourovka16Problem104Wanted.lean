/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Jordan decompositions in integral group rings of `2`-groups (Kourovka Notebook Problem 16.104)

Kourovka Notebook, Archive of Solved Problems, Problem 16.104 (A. W. Hales, I. B. S. Passi): for a
finite group `G`, every `a ∈ ℚ[G]` has a unique Jordan decomposition `a = a_s + a_n` with `a_n`
nilpotent, `a_s` semisimple over `ℚ` and `a_s a_n = a_n a_s`, and every invertible `a` has a unique
decomposition `a = a_s a_u` with `a_u` unipotent. `ℤ[G]` has AJD if `a_s, a_n ∈ ℤ[G]` for every `a ∈
ℤ[G]`, and MJD if `a_s, a_u ∈ ℤ[G]` for every invertible `a ∈ ℤ[G]`. Are there only finitely many
isomorphism classes of finite `2`-groups `G` such that `ℤ[G]` has MJD but not AJD?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.IntegralGroupRingJordanDecompositionKourovka16Problem104Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.104 (A. W.
Hales, I. B. S. Passi). UnsolvedMath record UM-00701295 (`KOU-16.104`), dataset ulamai/UnsolvedMath
v1.8.0.

`ℤ[G]` is the set of elements of `ℚ[G]` with integer coefficients. Semisimple over `ℚ` means a
squarefree minimal polynomial over `ℚ` (equivalently separable, `ℚ` being perfect), and unipotent
means `u - 1` nilpotent. The decompositions exist and are unique, so AJD and MJD are stated for
every such decomposition. An invertible element of `ℤ[G]` has its inverse in `ℤ[G]`. Finitely many
isomorphism classes is stated as a bound on the orders, which is equivalent.
-/

/-- **Elements with integer coefficients.** An element $x$ of the monoid algebra $\mathbb{Q}[G]$
lies in $\mathbb{Z}[G]$ when all its coefficients are integers: for every $g \in G$, the
coefficient of $x$ at $g$ is an integer. -/
def HasIntegralCoeffs {G : Type*} (x : MonoidAlgebra ℚ G) : Prop :=
  ∀ g : G, ∃ z : ℤ, x.coeff g = z

/-- **Additive Jordan decomposition property.** For a group $G$, let $\mathbb{Z}[G]$ be the set
of elements of the rational group algebra $\mathbb{Q}[G]$ all of whose coefficients are integers.
Then $\mathbb{Z}[G]$ has the additive Jordan decomposition property (AJD) when, for all
$a, s, n \in \mathbb{Q}[G]$ such that $a \in \mathbb{Z}[G]$, $a = s + n$, $sn = ns$, $n$ is
nilpotent and the minimal polynomial of $s$ over $\mathbb{Q}$ is squarefree, both $s$ and $n$ lie
in $\mathbb{Z}[G]$.

For finite $G$ every $a \in \mathbb{Q}[G]$ has exactly one such decomposition $a = s + n$, its
Jordan decomposition, so AJD says that the semisimple and nilpotent parts of every
$a \in \mathbb{Z}[G]$ lie in $\mathbb{Z}[G]$. -/
def HasAJD (G : Type*) [Group G] : Prop :=
  ∀ a s n : MonoidAlgebra ℚ G, HasIntegralCoeffs a → a = s + n → Commute s n → IsNilpotent n →
    Squarefree (minpoly ℚ s) → HasIntegralCoeffs s ∧ HasIntegralCoeffs n

/-- **Multiplicative Jordan decomposition property.** For a group $G$, let $\mathbb{Z}[G]$ be
the set of elements of the rational group algebra $\mathbb{Q}[G]$ all of whose coefficients are
integers. Then $\mathbb{Z}[G]$ has the multiplicative Jordan decomposition property (MJD) when,
for all $a, b, s, u \in \mathbb{Q}[G]$ such that $a, b \in \mathbb{Z}[G]$, $ab = ba = 1$,
$a = su$, $su = us$, $u - 1$ is nilpotent and the minimal polynomial of $s$ over $\mathbb{Q}$ is
squarefree, both $s$ and $u$ lie in $\mathbb{Z}[G]$.

Equivalently, for every unit $a$ of $\mathbb{Z}[G]$ and every factorization $a = su$ in
$\mathbb{Q}[G]$ into commuting factors with $s$ semisimple over $\mathbb{Q}$ and $u$ unipotent,
both factors lie in $\mathbb{Z}[G]$; for finite $G$ such a factorization exists and is unique. -/
def HasMJD (G : Type*) [Group G] : Prop :=
  ∀ a b s u : MonoidAlgebra ℚ G, HasIntegralCoeffs a → HasIntegralCoeffs b → a * b = 1 →
    b * a = 1 → a = s * u → Commute s u → IsNilpotent (u - 1) → Squarefree (minpoly ℚ s) →
      HasIntegralCoeffs s ∧ HasIntegralCoeffs u

/-- **Kourovka Problem 16.104.** The proposition that there is a natural number $B$ such that
every finite $2$-group $G$ whose integral group ring $\mathbb{Z}[G]$ has the multiplicative Jordan
decomposition property (MJD) but not the additive Jordan decomposition property (AJD) has order
at most $B$.

A. W. Hales and I. B. S. Passi asked whether only finitely many isomorphism classes of finite
$2$-groups $G$ have MJD but not AJD for $\mathbb{Z}[G]$; a bound on the orders is equivalent. -/
def finitelyManyTwoGroupsMJDNotAJD : Prop :=
  ∃ B : ℕ, ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G → HasMJD G → ¬ HasAJD G →
    Nat.card G ≤ B

/--
**Finitely many $2$-groups have MJD but not AJD.** There is a natural number $B$ such that every
finite $2$-group $G$ whose integral group ring $\mathbb{Z}[G]$ has the multiplicative Jordan
decomposition property (MJD) but not the additive Jordan decomposition property (AJD) has order
at most $B$. In particular, only finitely many isomorphism classes of finite $2$-groups have MJD
but not AJD, which answers Kourovka Problem 16.104 in the affirmative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.104 (A. W.
Hales, I. B. S. Passi); resolution: A. W. Hales, I. B. S. Passi and L. E. Wilson, The
multiplicative Jordan decomposition in group rings, II, J. Algebra 316 (2007), no. 1, 109-132;
corrigendum, J. Algebra 371 (2012), 665-666, Kourovka Archive, Problem 16.104 (answer: Yes, it is
true).
-/
public theorem_wanted finitelyManyTwoGroupsMJDNotAJD_holds : finitelyManyTwoGroupsMJDNotAJD

end MathlibExt.GroupTheory.IntegralGroupRingJordanDecompositionKourovka16Problem104Wanted
