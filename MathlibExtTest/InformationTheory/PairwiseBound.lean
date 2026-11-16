/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.PairwiseBound

@[expose] public section

/-- Equal distributions: the whole mass is bounded by the
coefficient, which is 1 for a point mass. -/
example : ∑ i ∈ Finset.univ.filter (fun i : Fin 1 => (1 : ℝ) ≤ 1), (1 : ℝ)
    ≤ ∑ _i : Fin 1, Real.sqrt ((1 : ℝ) * 1) :=
  pairwise_error_le (fun _ => 1) (fun _ => 1) (fun _ => zero_le_one) (fun _ => zero_le_one)

end
