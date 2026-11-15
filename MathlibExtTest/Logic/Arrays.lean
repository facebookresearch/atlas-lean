/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Arrays

@[expose] public section

/-- Storing `7` at index `0` of the zero array reads back `7`. -/
example : aselect (astore (fun _ : Fin 2 => (0 : ℕ)) 0 7) 0 = 7 :=
  aselect_astore_same _ _ _

/-- Storing at index `0` leaves index `1` unchanged. -/
example : aselect (astore (fun _ : Fin 2 => (0 : ℕ)) 0 7) 1 = 0 :=
  aselect_astore_diff _ _ _ _ (by decide)

end
