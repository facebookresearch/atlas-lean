/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomially short conjugators in braid groups (Kourovka Notebook Problem 19.81)

Kourovka Notebook, Archive of Solved Problems, Problem 19.81 (V. Shpilrain): is the conjugacy
problem in the braid group `Bₙ` in the class NP? A stronger question: given two conjugate elements
of `Bₙ` represented by braid words of lengths `≤ m`, is there a conjugator whose length is bounded
by a polynomial function of `m`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import MathlibExt.GroupTheory.ArtinGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BraidConjugatorLengthKourovka19Problem81Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.81 (V.
Shpilrain). UnsolvedMath record UM-00701629 (`KOU-19.81`), dataset ulamai/UnsolvedMath v1.8.0.

Only the stronger question is formalized; the NP question is not. `B_{n+1}` is MathlibExt's Artin
group of the Coxeter matrix of type `Aₙ`, braid words are elements of the free group on its standard
generators, and length is the length of the reduced word (`FreeGroup.norm`), which is at most the
length of any word representing the same free group element. A polynomial bound in `m` is written `C
(m + 1)^d` with `C, d` depending on `n`.
-/

/-- **The braid represented by a braid word.** For $n \in \mathbb{N}$, let $B_{n+1}$ be the braid
group on $n + 1$ strands, realized as the Artin group of the Coxeter matrix of type $A_n$, with
standard generators $\sigma_1, \dots, \sigma_n$. A braid word is an element of the free group on
$\sigma_1, \dots, \sigma_n$; the braid it represents is its image under the group homomorphism from
this free group to $B_{n+1}$ that sends each $\sigma_i$ to the generator $\sigma_i$ of $B_{n+1}$. -/
def braidOf (n : ℕ) : FreeGroup (Fin n) →* (CoxeterMatrix.A n).ArtinGroup :=
  FreeGroup.lift (CoxeterMatrix.ArtinGroup.of (CoxeterMatrix.A n))

/-- **Polynomially short conjugators in braid groups.** The proposition (the stronger question of
Kourovka Problem 19.81, V. Shpilrain) that for every $n \in \mathbb{N}$ there are natural numbers
$C$ and $d$ with the following property. Let $B_{n+1}$ be the braid group on $n + 1$ strands,
realized as the Artin group of the Coxeter matrix of type $A_n$, with standard generators
$\sigma_1, \dots, \sigma_n$; a braid word is an element of the free group on
$\sigma_1, \dots, \sigma_n$, and its length $|u|$ is the length of its freely reduced form. For all
braid words $u$ and $v$ whose braids are conjugate in $B_{n+1}$ there is a braid word $w$ with
$|w| \le C (\max(|u|, |v|) + 1)^d$ such that $w u w^{-1}$ and $v$ represent the same braid. -/
def braidPolynomialConjugatorLength : Prop :=
  ∀ n : ℕ, ∃ C d : ℕ, ∀ u v : FreeGroup (Fin n), IsConj (braidOf n u) (braidOf n v) →
    ∃ w : FreeGroup (Fin n), w.norm ≤ C * (max u.norm v.norm + 1) ^ d ∧
      braidOf n (w * u * w⁻¹) = braidOf n v

/--
**Braid groups have polynomially short conjugators.** For $n \in \mathbb{N}$, let $B_{n+1}$ be
the braid group on $n + 1$ strands, realized as the Artin group of the Coxeter matrix of type
$A_n$, with standard generators $\sigma_1, \dots, \sigma_n$. A braid word is an element of the
free group on $\sigma_1, \dots, \sigma_n$, and its length $|u|$ is the length of its freely reduced
form. For every $n$ there are natural numbers $C$ and $d$ such that for all braid words $u$ and $v$
whose braids are conjugate in $B_{n+1}$ there is a braid word $w$ with
$|w| \le C (\max(|u|, |v|) + 1)^d$ such that $w u w^{-1}$ and $v$ represent the same braid.

This answers the stronger question of Kourovka Problem 19.81 positively: the Kourovka Archive
answers "Yes, there is such a conjugator, even for any mapping class groups", citing Tao's
linearly bounded conjugator property for mapping class groups (Theorem B: a conjugator of length
at most $K(|f| + |g|)$).

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.81 (V. Shpilrain);
resolution: J. Tao, Linearly bounded conjugator property for mapping class groups, Geom. Funct.
Anal. 23 (2013), no. 1, 415-466 (arXiv:1106.2341), Theorem B: for a finite generating set of the
mapping class group of a surface of finite type there is K such that conjugate f, g have a
conjugator ω with |ω| ≤ K(|f| + |g|); Kourovka Archive, Problem 19.81: Yes, there is such a
conjugator, even for any mapping class groups, https://arxiv.org/abs/1106.2341.
-/
public theorem_wanted braidPolynomialConjugatorLength_holds : braidPolynomialConjugatorLength

end MathlibExt.GroupTheory.BraidConjugatorLengthKourovka19Problem81Wanted
