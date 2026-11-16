/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.PauliXZ

@[expose] public section

/-- The identity Pauli (a = b = 0) fixes the zero basis state. -/
example : pauliXZ (0 : Fin 1 → ZMod 2) 0 0 0 = 1 := by
  simp [pauliXZ]

end
