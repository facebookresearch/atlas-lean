/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.SlepianWolf

/-- Boundary check: the chain rule instantiates on a two-by-two
joint law, and the binning average for `k = 2`, `M = 2` is
`C(2, 2) / 2 = 1 / 2`. -/
example (p : PMF (Fin 2 × Fin 2)) :
    entropyPMF p = entropyPMF (marginalSnd p) + condEntropy p ∧
    (∑ b : Fin 2 → Fin 2, binCollisions b) / (2 : ℝ) ^ 2 =
      ((Nat.choose 2 2 : ℝ)) / 2 :=
  ⟨entropy_chain_rule p, by
    have h := expected_bin_collisions (k := 2) (M := 2) (by norm_num)
    simpa using h⟩
