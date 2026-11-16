/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SwapIdentity

import Mathlib.Basic.Real.Basic

@[expose] public section

open MathlibExt.Probability.SwapIdentity

/-- Constant loss: both sides of the swap identity agree. -/
example : (∑ S : Fin 1 → Fin 1, ∑ z : Fin 1,
      (fun _ _ => (1 : ℕ)) ((fun S => S) (Function.update S 0 z)) (S 0))
    = ∑ S : Fin 1 → Fin 1, ∑ z : Fin 1, (fun _ _ => (1 : ℕ)) ((fun S => S) S) z :=
  swap_identity (fun S => S) (fun _ _ => 1) 0

/-- Real-valued losses on a sample type without decidable equality. -/
example {Z H : Type*} [Fintype Z] {n : ℕ} (A : (Fin n → Z) → H)
    (ℓ : H → Z → ℝ) (i : Fin n) :
    (∑ S : Fin n → Z, ∑ z : Z, ℓ (A (Function.update S i z)) (S i))
      = ∑ S : Fin n → Z, ∑ z : Z, ℓ (A S) z :=
  swap_identity A ℓ i

end
