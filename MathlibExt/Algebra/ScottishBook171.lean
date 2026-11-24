/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Basic

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

/-- **Associativity and permutation invariance do not force composition.** There are a set $A$,
an associative operation $U$ on self-maps of $A$ that is invariant under conjugation by
permutations of $A$, and self-maps $f, g$ for which $U(f, g) \ne f \circ g$.

The left projection $U(f, g) = f$ is a counterexample to the implication from the two numbered
conditions of Scottish Book Problem 171 alone. This does not address any extra restriction
from the typescript's parenthetical $(U(f,g) \ne 1)$.

Source: J. Schreier – S. Ulam, Scottish Book, Problem 171, typescript p. 76. -/
theorem not_forall_eq_comp_of_associative_permutationInvariant :
    ¬ ∀ (A : Type*) (U : (A → A) → (A → A) → (A → A)),
      IsAssociative A U → IsPermutationInvariant A U →
      ∀ f g : A → A, U f g = f ∘ g := by
  intro h
  -- Lift the two-point set so the witness works in every universe.
  have hcomp := h (ULift Bool) (fun f _ => f)
    (by intro f g k; rfl) (by intro p f g; rfl) id (fun x => ⟨!x.down⟩)
  have hfalse : false = true := congrArg ULift.down (congrFun hcomp (ULift.up false))
  cases hfalse

/-- Deprecated name for `not_forall_eq_comp_of_associative_permutationInvariant`.
It concerns the two numbered conditions only, not the full question in the typescript. -/
@[deprecated (since := "2026-11-23")]
alias scottishBook171_refuted := not_forall_eq_comp_of_associative_permutationInvariant

end MathlibExt.Algebra.ScottishBook171Wanted
