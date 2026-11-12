/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.Typical.AEP

/-- Boundary check: the uniform distribution on one point has
entropy `0`. -/
example : shannonEntropy (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
  simp [shannonEntropy]

/-- The AEP estimate instantiates for a two-point distribution. -/
example (p : Fin 2 → ℝ) (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (ε : ℝ) (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter
        (fun a => ε < |(if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p|),
        p a) ≤
      (∑ a, p a * ((if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p) ^ 2)
        / ε ^ 2 :=
  aep_chebyshev p hp_nonneg hp_sum ε hε
