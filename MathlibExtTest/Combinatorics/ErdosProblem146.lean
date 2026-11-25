/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ErdosProblem146

open MathlibExt.Combinatorics.ErdosProblem146Wanted

universe u

example (bound : ∀ (V : Type u) [Fintype V] (H : SimpleGraph V) (r : ℕ),
    H.IsBipartite → H.IsDegenerate r → 1 ≤ r →
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)))) : False :=
  DegenerateExtremalClaim_refuted bound
