/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.Fano

/-- Boundary check: Fano's bound instantiates for two hypotheses
on a two-point observation space. -/
example (P : Fin 2 → PMF (Fin 2)) (est : Fin 2 → Fin 2)
    (hsupp : ∀ i j a, (P j a) = 0 → (P i a) = 0)
    (β : ℝ) (hkl : ∀ i j, klSum (P i) (P j) ≤ β) :
    1 - (β + Real.log 2) / Real.log (Fintype.card (Fin 2)) ≤
      (∑ i, (∑ a ∈ Finset.univ.filter (fun a => est a ≠ i), (P i a).toReal)) /
        Fintype.card (Fin 2) :=
  fano_finite P est (by norm_num) hsupp β hkl
