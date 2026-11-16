/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SwapIdentity

@[expose] public section

/-- Constant loss: both sides of the swap identity agree. -/
example : (∑ S : Fin 1 → Fin 1, ∑ z : Fin 1,
      (fun _ _ => (1 : ℚ)) ((fun S => S) (Function.update S 0 z)) (S 0))
    = ∑ S : Fin 1 → Fin 1, ∑ z : Fin 1, (fun _ _ => (1 : ℚ)) ((fun S => S) S) z :=
  swap_identity (fun S => S) (fun _ _ => 1) 0

end
