/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.LKSoundness

@[expose] public section

/-- A one-atom sequent derives itself. -/
example : Deriv [PForm.atom 0] [PForm.atom 0] :=
  Deriv.ax (List.mem_cons.mpr (Or.inl rfl)) (List.mem_cons.mpr (Or.inl rfl))

end
