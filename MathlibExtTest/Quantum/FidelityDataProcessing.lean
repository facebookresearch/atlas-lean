/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.FidelityDataProcessing

@[expose] public section

/-- The identity channel preserves the coefficient of a point mass
with itself. -/
example : bhattD (n := 1) (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 1)
    ≤ bhattD (n := 1) (pushf (fun _ _ => 1) (fun _ : Fin 1 => 1))
        (pushf (fun _ _ => 1) (fun _ : Fin 1 => (1 : ℝ))) :=
  bhatt_pushf_ge (m := 1) (n := 1) (fun _ _ => 1) (fun _ _ => zero_le_one)
    (fun _ => by norm_num) (fun _ => (1 : ℝ)) (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => zero_le_one)

end
