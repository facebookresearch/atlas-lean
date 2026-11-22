/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# One-relator groups that are homomorphic images of each other (Kourovka Notebook Problem 3.33)

Kourovka Notebook, Archive of Solved Problems, Problem 3.33 (D. I. Moldavanskiĭ): are two groups
necessarily isomorphic if each of them can be defined by a single relation and is a homomorphic
image of the other one?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorMutualImagesKourovka3Problem33Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.33 (D. I.
Moldavanskiĭ). UnsolvedMath record UM-00700183 (`KOU-3.33`), dataset ulamai/UnsolvedMath v1.8.0.

Groups defined by a single relation are `PresentedGroup {r}` with `r ∈ FreeGroup (Fin n)`; the
statement is about isomorphism types, so quantifying over the presentations loses nothing.
-/

/-- Kourovka 3.33 (D. I. Moldavanskiĭ): two groups, each defined by a single relation (on finitely
many generators) and each a homomorphic image of the other, are isomorphic. -/
def oneRelatorMutualImagesIsomorphic : Prop :=
  ∀ (m n : ℕ) (r : FreeGroup (Fin m)) (s : FreeGroup (Fin n)),
    (∃ f : PresentedGroup {r} →* PresentedGroup {s}, Function.Surjective f) →
    (∃ g : PresentedGroup {s} →* PresentedGroup {r}, Function.Surjective g) →
    Nonempty (PresentedGroup {r} ≃* PresentedGroup {s})

/--
Resolved false: the Kourovka Archive answers 3.33 "No, not necessarily", citing Borshchev and
Moldavanskiĭ (Math. Notes 79 (2006)): there are non-isomorphic one-relator groups each of which is a
homomorphic image of the other. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 3.33 (D. I. Moldavanskiĭ); resolution: A. V. Borshchev and D. I. Moldavanskiĭ,
Math. Notes 79 (2006), no. 1, 31-40, Kourovka Archive, Problem 3.33: No, not necessarily,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted oneRelatorMutualImagesIsomorphic_refuted : ¬ oneRelatorMutualImagesIsomorphic

end MathlibExt.GroupTheory.OneRelatorMutualImagesKourovka3Problem33Wanted
