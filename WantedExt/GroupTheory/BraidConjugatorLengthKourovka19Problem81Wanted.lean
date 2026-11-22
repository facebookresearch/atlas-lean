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

/-- The braid in `B_{n+1}` represented by a braid word, an element of the free group on the
standard generators `σ₁, …, σₙ`; `B_{n+1}` is the Artin group of the Coxeter matrix of type `Aₙ`
(MathlibExt). -/
def braidOf (n : ℕ) : FreeGroup (Fin n) →* (CoxeterMatrix.A n).ArtinGroup :=
  FreeGroup.lift (CoxeterMatrix.ArtinGroup.of (CoxeterMatrix.A n))

/-- Kourovka 19.81 (V. Shpilrain), the stronger question: in each braid group `B_{n+1}`, two
conjugate braids represented by braid words of length at most `m` have a conjugating braid word of
length bounded by a polynomial in `m` (here `C (m + 1)^d`, with `C` and `d` depending on `n`); word
length is the length of the freely reduced word. -/
def braidPolynomialConjugatorLength : Prop :=
  ∀ n : ℕ, ∃ C d : ℕ, ∀ u v : FreeGroup (Fin n), IsConj (braidOf n u) (braidOf n v) →
    ∃ w : FreeGroup (Fin n), w.norm ≤ C * (max u.norm v.norm + 1) ^ d ∧
      braidOf n (w * u * w⁻¹) = braidOf n v

/--
Resolved true: the Kourovka Archive answers the stronger question of 19.81 "Yes, there is such a
conjugator, even for any mapping class groups", citing Tao's linearly bounded conjugator property
for mapping class groups (Theorem B: a conjugator of length at most `K(|f| + |g|)`). Source: E. I.
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
