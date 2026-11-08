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

/-- `U` is associative, condition (1) of Problem 171. -/
def IsAssociative (A : Type*) (U : (A → A) → (A → A) → (A → A)) : Prop :=
  ∀ f g h : A → A, U f (U g h) = U (U f g) h

/-- `U` is invariant under permutations of the underlying set, condition
(2) of Problem 171: conjugating the arguments by a permutation `p`
conjugates the result by `p`. -/
def IsPermutationInvariant (A : Type*)
    (U : (A → A) → (A → A) → (A → A)) : Prop :=
  ∀ (p : Equiv.Perm A) (f g : A → A),
    U (p.symm ∘ f ∘ p) (p.symm ∘ g ∘ p) = p.symm ∘ U f g ∘ p

/--
Scottish Book Problem 171, as printed, is false: there are associative,
permutation-invariant operations on self-maps other than composition —
reverse composition `U(f, g) = g ∘ f` and the two projections
`U(f, g) = f`, `U(f, g) = g` satisfy (1) and (2) but are not composition
in general. The typescript's parenthetical `(U(f,g) ≠ 1)` is of unclear
meaning and is not read as excluding these counterexamples. Status:
solved-negative. Source: J. Schreier – S. Ulam, Problem 171 of the
Scottish Book, typescript p. 76.
-/
theorem_wanted scottishBook171_refuted :
    ¬ ∀ (A : Type*) (U : (A → A) → (A → A) → (A → A)),
      IsAssociative A U → IsPermutationInvariant A U →
      ∀ f g : A → A, U f g = f ∘ g

end MathlibExt.Algebra.ScottishBook171Wanted
