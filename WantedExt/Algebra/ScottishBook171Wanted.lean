/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace MathlibExt.Algebra.ScottishBook171Wanted

/-- **Associative operations on self-maps.** Let $A$ be a set and let $U$ be an operation that
assigns to any two maps $f, g \colon A \to A$ a map $U(f, g) \colon A \to A$. We say $U$ is
associative (condition (1) of Problem 171) if $U(f, U(g, h)) = U(U(f, g), h)$ for all maps
$f, g, h \colon A \to A$. -/
def IsAssociative (A : Type*) (U : (A → A) → (A → A) → (A → A)) : Prop :=
  ∀ f g h : A → A, U f (U g h) = U (U f g) h

/-- **Permutation-invariant operations on self-maps.** Let $A$ be a set and let $U$ be an
operation that assigns to any two maps $f, g \colon A \to A$ a map $U(f, g) \colon A \to A$. We
say $U$ is invariant under permutations of $A$ (condition (2) of Problem 171) if conjugating the
arguments by a permutation conjugates the result: for every permutation $p$ of $A$ and all maps
$f, g \colon A \to A$, $U(p^{-1} \circ f \circ p, p^{-1} \circ g \circ p) = p^{-1} \circ U(f, g)
\circ p$. -/
def IsPermutationInvariant (A : Type*)
    (U : (A → A) → (A → A) → (A → A)) : Prop :=
  ∀ (p : Equiv.Perm A) (f g : A → A),
    U (p.symm ∘ f ∘ p) (p.symm ∘ g ∘ p) = p.symm ∘ U f g ∘ p

/--
**Scottish Book Problem 171 is false.** Not every associative, permutation-invariant operation
on self-maps is composition: there are a set $A$, an operation $U$ that assigns to any two maps
$f, g \colon A \to A$ a map $U(f, g) \colon A \to A$ and is both associative (condition (1) of
Problem 171) and invariant under permutations of $A$ (condition (2)), and maps
$f, g \colon A \to A$ with $U(f, g) \ne f \circ g$, where $(f \circ g)(x) = f(g(x))$.

Reverse composition $U(f, g) = g \circ f$ and the two projections $U(f, g) = f$ and
$U(f, g) = g$ satisfy (1) and (2) but are not composition in general. The typescript's
parenthetical $(U(f,g) \ne 1)$ is of unclear meaning and is not read as excluding these
counterexamples.

Source: J. Schreier – S. Ulam, Problem 171 of the
Scottish Book, typescript p. 76.
-/
theorem_wanted scottishBook171_refuted :
    ¬ ∀ (A : Type*) (U : (A → A) → (A → A) → (A → A)),
      IsAssociative A U → IsPermutationInvariant A U →
      ∀ f g : A → A, U f g = f ∘ g

end MathlibExt.Algebra.ScottishBook171Wanted
