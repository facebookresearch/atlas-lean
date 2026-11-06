/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Köthe's Nil Left Ideals Conjecture
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

namespace MathlibExt.Algebra.KoetheNilLeftIdealsWanted

universe u

/-- **Nil left ideal.** A left ideal $I$ of a ring $R$ is nil if each of its elements is
nilpotent: for every $x \in I$ there is a natural number $n$ with $x^n = 0$. -/
def IsNilLeftIdeal {R : Type*} [Ring R] (I : Ideal R) : Prop :=
  ∀ x : R, x ∈ I → IsNilpotent x

/-- **Köthe's conjecture.** The statement that for every ring $R$ (associative, with identity)
and all nil left ideals $I$ and $J$ of $R$, the sum $I + J$ is again a nil left ideal. -/
def conjecture : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R),
    IsNilLeftIdeal I → IsNilLeftIdeal J → IsNilLeftIdeal (I + J)

/--
**Köthe's conjecture is false.** There exist a ring $R$ (associative, with identity) and nil left
ideals $I$ and $J$ of $R$ (left ideals all of whose elements are nilpotent) such that the sum
$I + J$ is not nil.

Adamczewski, Böhmler and Marczinzik (arXiv:2609.07996, 2026; Lean 4 machine-checked by
Adamczewski) build, over any countable field $F$, a nil algebra $N$ such that $M_2(F1 + N)$ has
two nil left ideals with non-nil sum. Greenfeld, King and Vendramin (arXiv:2609.15080) give an
independent refutation.

Source: Tom Adamczewski, Bernhard Böhmler and René Marczinzik, A counterexample to Köthe's
conjecture and a question of Rowen, arXiv:2609.07996 (2026), https://arxiv.org/abs/2609.07996;
Be'eri Greenfeld, G. King and Leandro Vendramin, The Köthe conjecture via point modules,
arXiv:2609.15080 (2026), https://arxiv.org/abs/2609.15080. Moved from
`OpenConjectures/Algebra/KoetheNilLeftIdeals`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.KoetheNilLeftIdealsWanted
