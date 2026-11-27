/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:
`lean/ComparatorChallenges/HadamardCubeFiber.lean` in OpenAI's `openai/math` repository,
revision `3344da59991ed94f9ba711217b29c1d760badfa6`.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The pinned source file records no separate copyright notice or author list.
Authors: OpenAI (project attribution in `lean/formalization.yaml`).

The comparator's helper definitions are inlined, and its result is recorded as a wanted statement.
-/
module

import Batteries.Util.ProofWanted
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Matrix

open Classical in
/-- **Cube-fiber cancellation for order-six complex Hadamard matrices.** Suppose a complex
$6\times6$ matrix $H$ and its entrywise square both have unit-modulus entries and satisfy
$A^*A=6I$. Fix two distinct rows $i,j$ and set $r_k=H_{ik}\overline{H_{jk}}$.
If $a,b$ are distinct complex numbers and every $r_k^3$ equals either $a$ or $b$, then
$\sum_{k:r_k^3=a}r_k=0$. Neither fiber is required to be nonempty.

Source: OpenAI, [Hadamard cube-fiber comparator](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HadamardCubeFiber.lean#L9-L34).
-/
public theorem_wanted sum_rowRatio_eq_zero_of_two_cube_values
    {H : Matrix (Fin 6) (Fin 6) ℂ}
    (hH : (∀ i k, ‖H i k‖ = 1) ∧ H.conjTranspose * H = (6 : ℂ) • 1)
    (hSq : let S : Matrix (Fin 6) (Fin 6) ℂ := fun i k => H i k ^ 2
           (∀ i k, ‖S i k‖ = 1) ∧ S.conjTranspose * S = (6 : ℂ) • 1)
    {i j : Fin 6} (hij : i ≠ j) (a b : ℂ) (hab : a ≠ b) :
    let r := fun k : Fin 6 => H i k * star (H j k)
    (∀ k, r k ^ 3 = a ∨ r k ^ 3 = b) →
      ∑ k ∈ Finset.univ.filter (fun k => r k ^ 3 = a), r k = 0

end Matrix
