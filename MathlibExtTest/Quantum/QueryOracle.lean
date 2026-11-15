/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.QueryOracle

@[expose] public section

/-- Querying twice with the constant-true oracle restores the state. -/
example : queryOracle (fun _ : Fin 2 => true) (queryOracle (fun _ : Fin 2 => true) (1, false)) = (1, false) :=
  queryOracle_involutive _ _

/-- The oracle keeps the register value. -/
example : (queryOracle (fun _ : Fin 2 => true) (1, false)).1 = 1 :=
  queryOracle_fst _ _

end
