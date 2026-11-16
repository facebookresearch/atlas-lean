/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.RankOneMatrix

@[expose] public section

/-- The zero matrix is in product form. -/
example : ∃ a : Fin 2 → ℂ, ∃ b : Fin 2 → ℂ,
    ∀ i j, (0 : Fin 2 → Fin 2 → ℂ) i j = a i * b j :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => by simp⟩

end
