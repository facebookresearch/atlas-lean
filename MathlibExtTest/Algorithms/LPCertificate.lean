/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.LPCertificate

@[expose] public section

/-- The zero system: every feasible point has objective at most the
value at zero. -/
example : ∑ j : Fin 1, (0 : ℚ) * (fun _ => (5 : ℚ)) j
    ≤ ∑ j : Fin 1, (0 : ℚ) * (fun _ => (0 : ℚ)) j :=
  lp_optimal_of_certificate (m := 1) (fun _ _ => (0 : ℚ)) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => le_refl (0 : ℚ)) (fun _ => by simp)
    (fun _ => by simp) (fun _ => by simp) (fun _ => 5)
    (fun _ => by norm_num) (fun _ => by simp)

end
