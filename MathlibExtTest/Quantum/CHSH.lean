/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.CHSH

@[expose] public section

/-- Constant-zero strategies win exactly the three pairs with `x AND y = false`
except `(1, 1)`: they win 3 pairs, so the bound is tight for this family. -/
example : (Finset.univ.filter (fun p : Fin 2 × Fin 2 =>
    chshWin (fun _ => false) (fun _ => false) p.1 p.2)).card = 3 := by
  decide

end
