/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.NashZeroSum

@[expose] public section

/-- Against a fixed column, some row attains at least the payoff of
the uniform row mix. -/
example : ∃ i : Fin 2, expPayoff (m := 2) (n := 2) (fun a b => if a = b then (1 : ℝ) else 0)
    (fun _ => 1 / 2) (fun _ => 1) ≤ ∑ j, (1 : ℝ) * (fun a b => if a = b then (1 : ℝ) else 0) i j :=
  exists_pure_best_response (m := 2) (n := 2) (fun a b => if a = b then (1 : ℝ) else 0)
    (fun _ => 1) (fun _ => 1 / 2) (fun _ => by norm_num) (by norm_num)

end
