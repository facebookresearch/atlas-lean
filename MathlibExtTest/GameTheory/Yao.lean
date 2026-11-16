/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Yao

@[expose] public section

/-- With one algorithm, its cost is the mixed cost. -/
example : ∃ a : Fin 1, (∑ y : Fin 1, (1 : ℚ) * (fun _ _ => (3 : ℚ)) a y)
    ≤ ∑ a' : Fin 1, (1 : ℚ) * (∑ y : Fin 1, (1 : ℚ) * (fun _ _ => (3 : ℚ)) a' y) :=
  yao_exists_det (fun _ _ => (3 : ℚ)) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => zero_le_one) (by simp)

end
