/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiSpinCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinBlockIndex

/-! Complete source spin certificates use finite support envelopes with proved vanishing at every omitted coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- A complete finite envelope is represented by exact bits at all original physical spin labels. -/
def generatedAxisGlobalOddSpinEnvelope (blocks : Fin 16 → ℕ) (k : Fin 4096) : Bool :=
  (blocks ⟨k.val / 256, by omega⟩).testBit (k.val % 256)

/-- Bounded checks cover every physical spin coordinate with its original label. -/
theorem generatedAxisGlobalOddSpinEnvelope_blocked_forall (p : Fin 4096 → Prop)
    (h : ∀ b : Fin 16, ∀ n : Fin 256, p (generatedAxisGlobalOddSpinOutputBlock b n)) :
    ∀ k, p k := by
  intro k
  have hr := generatedAxisGlobalOddSpinOutputBlock_roundtrip k
  simpa only [hr] using h ⟨k.val / 256, by omega⟩ ⟨k.val % 256, Nat.mod_lt _ (by decide)⟩

/-- The corresponding bounded decomposition covers every original low spin label. -/
theorem generatedAxisGlobalOddLowEnvelope_blocked_forall (p : Fin 2048 → Prop)
    (h : ∀ b : Fin 16, ∀ n : Fin 128,
      p ⟨128 * b.val + n.val, by omega⟩) : ∀ k, p k := by
  intro k
  let b : Fin 16 := ⟨k.val / 128, by omega⟩
  let n : Fin 128 := ⟨k.val % 128, Nat.mod_lt _ (by decide)⟩
  have hr : (⟨128 * b.val + n.val, by omega⟩ : Fin 2048) = k := by
    apply Fin.ext
    dsimp [b, n]
    omega
  simpa only [hr] using h b n

/-- Actual coefficient equalities on an envelope, and exact zeros outside it, determine the entire source vector. -/
theorem generatedAxisGlobalOddSpinEnvelope_certificate
    (E : Fin 4096 → Bool) (u v : Fin 4096 → ℤ) (a b : ℤ)
    (hi : ∀ k, E k = true → a * u k = b * v k)
    (hu : ∀ k, E k = false → u k = 0)
    (hv : ∀ k, E k = false → v k = 0) :
    ∀ k, a * u k = b * v k := by
  intro k
  cases hk : E k with
  | false => rw [hu k hk, hv k hk, mul_zero, mul_zero]
  | true => exact hi k hk

private theorem label_xor_cancel (n a : Fin 4096) :
    generatedSixthSpinLabelXor (generatedSixthSpinLabelXor n a) a = n := by
  apply Fin.ext
  change (n.val ^^^ a.val) ^^^ a.val = n.val
  exact Nat.xor_xor_cancel_right n.val a.val

/-- A genuine Gaussian output is zero outside the exact translated support envelope of its original input. -/
theorem generatedAxisGlobalOddXiSpin_zero_outside
    (u : Fin 4096 → ℤ) (E : Fin 4096 → Bool)
    (hc : ∀ m : Fin 4096, u m ≠ 0 → ∀ a : Fin 64,
      E (generatedSixthSpinLabelXor m (generatedSixthGrayCodeLabel a)) = true)
    (n : Fin 4096) (hn : E n = false) :
    generatedAxisGlobalOddXiSpinInteger u n = 0 := by
  rw [generatedAxisGlobalOddXiSpinInteger_eq_cached]
  unfold generatedSixthIntegerXiCached
  apply Finset.sum_eq_zero
  intro a _
  have hz : u (generatedSixthSpinLabelXor n (generatedSixthGrayCodeLabel a)) = 0 := by
    by_contra hh
    have he := hc _ hh a
    rw [label_xor_cancel, hn] at he
    contradiction
  simp only [hz, ite_true]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
