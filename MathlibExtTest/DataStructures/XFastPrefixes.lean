/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.DataStructures.XFastPrefixes

@[expose] public section

/-- A stored full-length prefix recovers the key. -/
example : (fun _ : Fin 1 => true) ∈ ({(fun _ : Fin 1 => true)} : Finset (Fin 1 → Bool)) :=
  mem_of_storedPrefix_full {(fun _ : Fin 1 => true)} (fun _ : Fin 1 => true)
    ⟨_, Finset.mem_singleton_self _, fun _ => rfl⟩

end
