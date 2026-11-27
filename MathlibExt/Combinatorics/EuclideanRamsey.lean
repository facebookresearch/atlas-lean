/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`lean/ComparatorChallenges/EuclideanRamseySpherical.lean` (openai/math,
https://github.com/openai/math), revision `3344da59991ed94f9ba711217b29c1d760badfa6`.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source file and the applicable license files name no copyright holder or authors.
Authors: OpenAI (project attribution in lean/formalization.yaml).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- **Euclidean Ramsey configurations.** A fixed finite indexed family $a$ of points in Euclidean
space is Euclidean Ramsey if, for each finite palette with at least two colors, there is a positive
host dimension such that every coloring of that Euclidean space by that palette contains an
indexed monochromatic copy of $a$ with the same pairwise distances. The family $a$ may be empty
and may have repeated points. The distances are preserved, not merely proportional, and there is
no regularity restriction on colorings.

Sources: Erdős, Graham, Montgomery, Rothschild, Spencer and Straus,
[*Euclidean Ramsey theorems. I*](https://doi.org/10.1016/0097-3165(73)90011-3), §1, pp. 342–344;
[proof comparator, indexed formulation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseySpherical.lean#L10-L17). -/
@[expose] public def IsEuclideanRamsey {s d : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ color : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
      (∀ i j, dist (b i) (b j) = dist (a i) (a j)) ∧ ∃ k : Fin r, ∀ i, color (b i) = k
