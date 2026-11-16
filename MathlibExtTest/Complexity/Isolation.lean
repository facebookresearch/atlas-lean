/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.Isolation

@[expose] public section

/-- For the nonzero vector `1` in one coordinate, one of the two
functionals annihilates it. -/
example : 2 * (Finset.univ.filter
    (fun a : Fin 1 → ZMod 2 => dotF2 a (fun _ => 1) = 0)).card = 2 ^ 1 :=
  dotF2_card (fun _ => 1) (by decide)

end
