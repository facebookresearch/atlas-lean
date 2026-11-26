/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- **Euclidean Ramsey configurations.** For each finite palette with at least two colors,
some positive dimension has the property that every coloring of its Euclidean space has
an indexed monochromatic copy with the same pairwise distances. The distances are
preserved, not merely proportional, and there is no regularity restriction on colorings.

Sources: Erdős, Graham, Montgomery, Rothschild, Spencer and Straus,
[*Euclidean Ramsey theorems. I*](https://doi.org/10.1016/0097-3165(73)90011-3);
[proof comparator, indexed formulation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseySpherical.lean#L10-L17). -/
@[expose] public def IsEuclideanRamsey {s d : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ color : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
      (∀ i j, dist (b i) (b j) = dist (a i) (a j)) ∧ ∃ k : Fin r, ∀ i, color (b i) = k
