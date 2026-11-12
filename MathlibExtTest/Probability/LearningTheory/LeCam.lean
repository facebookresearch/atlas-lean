/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.LeCam

/-- Boundary check: for two point masses at distinct points and
the test that decides `q`'s point, both error probabilities are
`0`, so the bound says `1 - (1/2) * 2 ≤ 0`, an equality case; here
we only instantiate the statement on a two-point type. -/
example (p q : PMF (Fin 2)) (δ : Fin 2 → Bool) :
    1 - (1 / 2) * ∑ a, |(p a).toReal - (q a).toReal| ≤
      (∑ a ∈ Finset.univ.filter (fun a => δ a = true), (p a).toReal) +
        (∑ a ∈ Finset.univ.filter (fun a => δ a = false), (q a).toReal) :=
  lecam_two_point p q δ
