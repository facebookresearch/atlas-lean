/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic

/-! Splitting a property of all 4096 spin labels into eight blocks of 512 labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The spin label with block `q` and offset `a`. -/
def generatedFeasibleAmbientTenthBlockLabel (q : Fin 8) (a : Fin 512) : Fin 4096 :=
  ⟨q.val * 512 + a.val, by have := q.isLt; have := a.isLt; omega⟩

/-- A property of every spin label from its eight blocks of 512 labels. -/
theorem generatedFeasibleAmbientTenth_fin4096_blocks {P : Fin 4096 → Prop}
    (h : ∀ q : Fin 8, ∀ a : Fin 512, P (generatedFeasibleAmbientTenthBlockLabel q a)) (a : Fin
        4096) : P a := by
  have h' := h ⟨a.val / 512, by have := a.isLt; omega⟩ ⟨a.val % 512, Nat.mod_lt _ (by decide)⟩
  have he : generatedFeasibleAmbientTenthBlockLabel ⟨a.val / 512, by have := a.isLt; omega⟩
      ⟨a.val % 512, Nat.mod_lt _ (by decide)⟩ = a := by
    apply Fin.ext
    change a.val / 512 * 512 + a.val % 512 = a.val
    omega
  rw [he] at h'
  exact h'

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
