/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Geometry.Euclidean.Sphere.Basic
import MathlibExt.Combinatorics.EuclideanRamsey

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- **Finite Euclidean Ramsey configurations are cospherical.** An injective indexed
configuration with the Euclidean Ramsey property lies on a sphere in its original
ambient space. There is no full-span requirement; empty configurations and singletons
are included. This is a necessary condition, not a converse.

Source: Erdős, Graham, Montgomery, Rothschild, Spencer and Straus,
[*Euclidean Ramsey theorems. I*](https://doi.org/10.1016/0097-3165(73)90011-3),
Theorem 13; [indexed statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseySpherical.lean#L19-L23). -/
public theorem_wanted euclideanRamsey_configurations_cospherical {s d : ℕ}
    (a : Fin s → EuclideanSpace ℝ (Fin d)) (ha : Function.Injective a)
    (hRamsey : IsEuclideanRamsey a) : EuclideanGeometry.Cospherical (Set.range a)
