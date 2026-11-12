/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.LeCamKL

/-- Boundary check: the KL form of Le Cam's bound instantiates on
a two-point type. -/
example (p q : PMF (Fin 2)) (δ : Fin 2 → Bool)
    (hsupp : ∀ a, (q a) = 0 → (p a) = 0) :
    1 - Real.sqrt (klSum p q / 2) ≤
      (∑ a ∈ Finset.univ.filter (fun a => δ a = true), (p a).toReal) +
        (∑ a ∈ Finset.univ.filter (fun a => δ a = false), (q a).toReal) :=
  lecam_kl p q δ hsupp
