/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Models whose automorphism groups have undecidable theory (Kourovka Notebook Problem 12.14)

Kourovka Notebook, Archive of Solved Problems, Problem 12.14 (M. Giraudet, A. M. W. Glass): if `T`
is a countable theory, does there exist a model `𝔄` of `T` such that the theory of `Aut(𝔄)` is
undecidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace MathlibExt.ModelTheory.AutomorphismGroupUndecidableTheoryKourovka12Problem14Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.14 (M.
Giraudet, A. M. W. Glass). UnsolvedMath record UM-00700834 (`KOU-12.14`), dataset
ulamai/UnsolvedMath v1.8.0.

The answer recorded in the Archive is stated: every theory with infinite models has a model whose
automorphism group has undecidable existential theory; undecidable existential theory implies
undecidable theory, and theories with only finite models are excluded (a finite automorphism group
has decidable theory). A countable theory is a theory in a language with countably many symbols.
Existential sentences of the group language are effectively equivalent to finite disjunctions of
systems `u₁ = 1, …, v₁ ≠ 1, …` of words, and a disjunction holds iff some disjunct is solvable, so
the existential theory is decidable iff solvability of such systems in `Aut(𝔄)` is a computable
predicate; words are coded as lists of (variable, sign) pairs and evaluated in `Equiv.Perm 𝔄`.
-/

open FirstOrder FirstOrder.Language

/-- A finite system of group equations `u = 1` and inequations `v ≠ 1` in the variables
`x₀, x₁, …`; each word is a list of (variable index, exponent sign) pairs. -/
abbrev WordSystem : Type := List (List (ℕ × Bool)) × List (List (ℕ × Bool))

/-- The system `s` is solvable in the automorphism group of the `L`-structure `A`: some assignment
of automorphisms to the variables satisfies all its equations and inequations (words are evaluated
in `Equiv.Perm A`, which contains the automorphism group as a subgroup). -/
def AutSolvable (L : FirstOrder.Language) (A : Type) [L.Structure A] (s : WordSystem) : Prop :=
  ∃ x : ℕ → L.Equiv A A,
    (∀ w ∈ s.1, FreeGroup.lift (fun n => ((x n).toEquiv : Equiv.Perm A)) (FreeGroup.mk w) = 1) ∧
    ∀ w ∈ s.2, FreeGroup.lift (fun n => ((x n).toEquiv : Equiv.Perm A)) (FreeGroup.mk w) ≠ 1

/-- Kourovka 12.14 (M. Giraudet, A. M. W. Glass), in the strong form of the answer: every theory `T`
in a countable language with an infinite model has a model `A` whose automorphism group has
undecidable existential theory. An existential sentence of the group language is equivalent,
effectively, to a finite disjunction of solvable systems of equations and inequations, so its
existential theory is decidable iff `AutSolvable L A` is a computable predicate. -/
def autGroupUndecidableExistentialTheory : Prop :=
  ∀ (L : FirstOrder.Language.{0, 0}) [Countable L.Symbols] (T : L.Theory),
    (∃ (M : Type) (_ : L.Structure M), T.Model M ∧ Infinite M) →
    ∃ (A : Type) (_ : L.Structure A), T.Model A ∧ ¬ ComputablePred (AutSolvable L A)

/--
Resolved true: Bludov, Giraudet, Glass and Sabbagh prove that every first-order theory with infinite
models has a model whose automorphism group has undecidable existential theory ("Yes, moreover,
..."); in particular the theory of that automorphism group is undecidable. Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.14 (M. Giraudet, A. M. W. Glass);
resolution: V. V. Bludov, M. Giraudet, A. M. W. Glass and G. Sabbagh, in: Models, Modules and
Abelian Groups, de Gruyter, Berlin, 2008, 325-328, Kourovka Archive, Problem 12.14: "Yes, moreover,
every first order theory having infinite models has a model whose automorphism group has undecidable
existential theory", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted autGroupUndecidableExistentialTheory_holds :
    autGroupUndecidableExistentialTheory

end MathlibExt.ModelTheory.AutomorphismGroupUndecidableTheoryKourovka12Problem14Wanted
