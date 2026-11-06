/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthFastStep

/-! Transport bounded nibble checks to the genuine complete descending-edge obligation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Three finite nibbles enumerate precisely the full 4096-mask block. -/
def generatedAxisGlobalFifthBlockIndex (a b c : Fin 16) : Fin 4096 :=
  ⟨256 * a.val + 16 * b.val + c.val, by omega⟩

/-- A complete check on three finite nibbles proves every unchanged genuine forest edge. -/
theorem generatedAxisGlobalFifthFiniteBlock_sound (edge : Fin 4096 → ℕ) (start : ℕ)
    (hstart : start + 4096 ≤ 2 ^ 24)
    (hcheck : ∀ a b c : Fin 16, generatedAxisGlobalFifthFastStep
      (edge (generatedAxisGlobalFifthBlockIndex a b c))
      (start + 256 * a.val + 16 * b.val + c.val)) :
    ∀ i : Fin 4096, generatedAxisGlobalFifthForestStep (edge i) (start + i.val) := by
  intro i
  have hi : i.val / 256 < 16 := by omega
  have hx := hcheck ⟨i.val / 256, hi⟩
    ⟨(i.val / 16) % 16, Nat.mod_lt _ (by decide)⟩
    ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  have he : 256 * (i.val / 256) + 16 * ((i.val / 16) % 16) + i.val % 16 = i.val := by
    omega
  have hs : start + 256 * (i.val / 256) + 16 * ((i.val / 16) % 16) +
      i.val % 16 = start + i.val := by omega
  have hb : generatedAxisGlobalFifthBlockIndex ⟨i.val / 256, hi⟩
      ⟨(i.val / 16) % 16, Nat.mod_lt _ (by decide)⟩
      ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩ = i := by
    apply Fin.ext
    exact he
  rw [hb, hs] at hx
  exact generatedAxisGlobalFifthFastStep_sound _ _ (by omega) hx

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
