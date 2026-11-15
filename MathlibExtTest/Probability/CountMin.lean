/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CountMin

@[expose] public section

/-- The estimate for a constant stream never undercounts. -/
example : (1 : ℕ) ≤ cmEst (fun _ : Fin 2 => 1) (fun _ _ => 0) 1 (by norm_num) 0 :=
  freq_le_cmEst _ _ _ _ _

/-- The estimate is at most the single counter when `d = 1`. -/
example : cmEst (fun _ : Fin 2 => 1) (fun _ _ => 0) 1 (by norm_num) 0
    ≤ cmCounter (fun _ : Fin 2 => 1) (fun _ => 0) 0 :=
  cmEst_le_counter _ _ _ _ _ 0 (by norm_num)

end
