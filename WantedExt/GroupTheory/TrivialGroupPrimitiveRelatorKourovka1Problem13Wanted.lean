/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Replacing a relator of the trivial group by a primitive element (Kourovka Notebook Problem 1.13)

Kourovka Notebook, Archive of Solved Problems, Problem 1.13 (J. Stallings; M. D. Greendlinger): if a
finitely presented group is trivial, is it always possible to replace one of the defining words by a
primitive element without changing the group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.TrivialGroupPrimitiveRelatorKourovka1Problem13Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.13 (J.
Stallings; M. D. Greendlinger). UnsolvedMath record UM-00700011 (`KOU-1.13`), dataset
ulamai/UnsolvedMath v1.8.0.

A finite presentation is `⟨x₁, …, xₙ | r₁, …, rₘ⟩` with relators `r : Fin m → FreeGroup (Fin n)`. A
primitive element of `Fₙ` is a member of some free basis. At least one generator is required: with
`n = 0` the empty presentation of the trivial group has no relator to replace and `F₀` has no
primitive element, so the claim would fail for a trivial reason. For `n = 2` the answer is yes
(every element of `F₂` lies in the normal closure of a primitive element), so the refutation is
carried by a presentation with three generators.
-/

/-- An element of the free group `F_n` is primitive if it belongs to some free basis of `F_n`. -/
def IsPrimitive {n : ℕ} (w : FreeGroup (Fin n)) : Prop :=
  ∃ (b : FreeGroupBasis (Fin n) (FreeGroup (Fin n))) (i : Fin n), b i = w

/-- The presentation `⟨x₁, …, xₙ | r₁, …, rₘ⟩` defines the trivial group. -/
def PresentsTrivialGroup {n m : ℕ} (r : Fin m → FreeGroup (Fin n)) : Prop :=
  Subsingleton (PresentedGroup (Set.range r))

/-- Kourovka 1.13 (J. Stallings): if a finite presentation `⟨x₁, …, xₙ | r₁, …, rₘ⟩` with `n ≥ 1`
defines the trivial group, then some defining relator `rᵢ` can be replaced by a primitive element of
the free group `F_n` so that the new presentation still defines the trivial group. -/
def trivialPresentationPrimitiveReplacement : Prop :=
  ∀ (n m : ℕ) (r : Fin m → FreeGroup (Fin n)), 1 ≤ n → PresentsTrivialGroup r →
    ∃ (i : Fin m) (w : FreeGroup (Fin n)), IsPrimitive w ∧
      PresentsTrivialGroup (Function.update r i w)

/--
Resolved false: the Kourovka Archive answers 1.13 "No, not always", citing Ivanov, who constructs a
balanced presentation of the trivial group in which no defining relator can be replaced by a free
generator (a member of a free basis, that is, a primitive element) with the altered presentation
still defining the trivial group; his abstract states that this solves the problems of Magnus and
Stallings (https://doi.org/10.1007/s00222-005-0497-1). The Baumslag-Myasnikov-Shpilrain list
(problem FP4) records the answer as yes for two generators and no for three (Ivanov). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.13 (J. Stallings; M. D.
Greendlinger); resolution: S. V. Ivanov, On balanced presentations of the trivial group, Invent.
Math. 165 (2006), no. 3, 525-549, Kourovka Archive, Problem 1.13 (No, not always); counterexample on
three generators, as recorded in the Baumslag-Myasnikov-Shpilrain open problems list, problem FP4,
https://shpilrain.ccny.cuny.edu/gworld/problems/probFP.html.
-/
public theorem_wanted trivialPresentationPrimitiveReplacement_refuted :
    ¬ trivialPresentationPrimitiveReplacement

end MathlibExt.GroupTheory.TrivialGroupPrimitiveRelatorKourovka1Problem13Wanted
