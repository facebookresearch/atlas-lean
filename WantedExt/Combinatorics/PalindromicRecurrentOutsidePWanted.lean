/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-4425-004: Palindromic recurrent words outside class P.
RESOLVED TRUE: Labbé (EJC 21 (2014) #P3.11, arXiv:1307.1589, Theorem 1)
exhibited a palindromic, uniformly recurrent fixed point of a primitive
ternary morphism that is fixed by no non-identity morphism with a
conjugate in class P. The binary case holds (Bo Tan, Mirror substitutions
and palindromic sequences, Theoret. Comput. Sci. 389 (2007)).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted

/-! Source record `OWR-4425-004`. Resolution: Labbé 2014, EJC 21 #P3.11. -/

/-- Ternary alphabet (Labbé's counterexample is ternary). -/
abbrev Sigma := Fin 3

/-- Morphisms as letter maps. -/
abbrev Morphism := Sigma → List Sigma

/-- Extension of a letter map to words. -/
def extend (φ : Morphism) (w : List Sigma) : List Sigma :=
  List.flatten (w.map φ)

/-- Iterate the word extension. -/
def extendIter (φ : Morphism) : Nat → List Sigma → List Sigma
  | 0 => id
  | n + 1 => (extend φ) ∘ (extendIter φ n)

/-- Primitivity: some power hits every letter from every letter. -/
def IsPrimitive (φ : Morphism) : Prop :=
  ∃ n : Nat, ∀ a b : Sigma, b ∈ extendIter φ n [a]

/-- Palindromes read the same backwards. -/
def IsPalindrome (w : List Sigma) : Prop := w = w.reverse

/-- Class P (Hof–Knill–Simon): `φ a = p ++ q` for a fixed palindrome `p`
and letter palindromes `q` (Labbé 2014, Section 2). -/
def InClassP (φ : Morphism) : Prop :=
  ∃ p : List Sigma, IsPalindrome p ∧
    ∀ a : Sigma, ∃ q : List Sigma, IsPalindrome q ∧ φ a = p ++ q

/-- Infinite words. -/
abbrev InfWord := Nat → Sigma

/-- A finite word occurs in an infinite word at position `k`. -/
def OccursAt (w : List Sigma) (u : InfWord) (k : Nat) : Prop :=
  ∀ i : Fin w.length, w[i] = u (k + i.val)

/-- A finite word occurs in an infinite word at some position. -/
def IsFactor (w : List Sigma) (u : InfWord) : Prop :=
  ∃ k : Nat, OccursAt w u k

/-- Fixed points: limits of iterated images of a prolongable letter. -/
def IsFixedPoint (φ : Morphism) (u : InfWord) : Prop :=
  ∃ a : Sigma, (φ a).head? = some a ∧
    (∀ L : Nat, ∃ m : Nat,
      L ≤ (extendIter φ m [a]).length) ∧
    ∀ m : Nat, ∀ i : Fin (extendIter φ m [a]).length,
      (extendIter φ m [a])[i] = u i.val

/-- Palindromic infinite words (Labbé 2014): arbitrarily long palindromic
factors, equivalently infinitely many palindromic factors over the finite
ternary alphabet. -/
def IsPalindromic (u : InfWord) : Prop :=
  ∀ N : Nat, ∃ w : List Sigma, N ≤ w.length ∧ IsPalindrome w ∧ IsFactor w u

/-- Uniform recurrence: every factor reoccurs within a bounded gap. -/
def IsUniformlyRecurrent (u : InfWord) : Prop :=
  ∀ w : List Sigma, IsFactor w u →
    ∃ B : Nat, ∀ k : Nat, ∃ j : Nat, j ≤ B ∧ OccursAt w u (k + j)

/-- Conjugate morphisms (Labbé 2014, Section 2; Lothaire): `ψ` and `θ` are
conjugate when `ψ a ++ w = w ++ θ a` for every letter `a` (or the
symmetric condition) for some word `w`. -/
def MorphConjugate (ψ θ : Morphism) : Prop :=
  (∃ w : List Sigma, ∀ a : Sigma, ψ a ++ w = w ++ θ a) ∨
    (∃ w : List Sigma, ∀ a : Sigma, θ a ++ w = w ++ ψ a)

/-- Identity morphism. -/
def IsIdentityMorphism (ψ : Morphism) : Prop :=
  ∀ a : Sigma, ψ a = [a]

/-- [OWR-4425-004] Labbé's counterexample (EJC 2014, Theorem 1): a primitive
ternary morphism has a palindromic, uniformly recurrent fixed point `u`
such that no morphism fixing `u`, other than the identity, has a
conjugate in class P. Fixing is the entry's fixed-point notion
(`IsFixedPoint ψ u`: `u` is the prolongable-letter limit, hence fixed
by `ψ`). -/
def conjecture : Prop :=
  ∃ φ : Morphism, IsPrimitive φ ∧
    ∃ u : InfWord, IsFixedPoint φ u ∧ IsPalindromic u ∧
      IsUniformlyRecurrent u ∧
      ¬ ∃ ψ : Morphism, IsFixedPoint ψ u ∧ ¬ IsIdentityMorphism ψ ∧
        ∃ θ : Morphism, MorphConjugate ψ θ ∧ InClassP θ

/--
Resolved true: Labbé (EJC 21 (2014) #P3.11, arXiv:1307.1589) exhibited a palindromic fixed point
of a primitive ternary morphism fixed by no morphism with a conjugate in class P; the binary
case holds (Tan 2007). Source: Sébastien Labbé, A counterexample to a question of Hof, Knill and
Simon, Electron. J. Combin. 21 (2014) #P3.11, https://doi.org/10.37236/3758. Moved from
`OpenConjectures/Combinatorics/PalindromicRecurrentOutsideP`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted
