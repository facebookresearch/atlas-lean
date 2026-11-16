/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Feistel rounds

A Feistel round maps `(l, r)` to `(r, l xor f r)` for an
arbitrary round function `f`. Each round is a permutation
with the displayed inverse round, and three rounds are
bijective. Luby-Rackoff security is not included here.
-/

@[expose] public section

/-- Feistel rounds on bitstring halves (QCI-22 core).
A half-block is `Fin n → Bool`; xor is pointwise. A round
with round function `f` maps `(l, r)` to
`(r, l xor f r)`. -/
def feistelRound {n : ℕ} (f : (Fin n → Bool) → (Fin n → Bool)) :
    (Fin n → Bool) × (Fin n → Bool) → (Fin n → Bool) × (Fin n → Bool)
  | (l, r) => (r, fun i => Bool.xor (l i) (f r i))

/-- The inverse round: from `(r, l xor f r)` recover
`(l, r)`. -/
def feistelRoundInv {n : ℕ} (f : (Fin n → Bool) → (Fin n → Bool)) :
    (Fin n → Bool) × (Fin n → Bool) → (Fin n → Bool) × (Fin n → Bool)
  | (a, b) => (fun i => Bool.xor (b i) (f a i), a)

/-- The inverse round undoes the round. -/
theorem feistelRoundInv_round {n : ℕ}
    (f : (Fin n → Bool) → (Fin n → Bool))
    (p : (Fin n → Bool) × (Fin n → Bool)) :
    feistelRoundInv f (feistelRound f p) = p := by
  obtain ⟨l, r⟩ := p
  simp only [feistelRound, feistelRoundInv]
  congr 1
  funext i
  cases l i <;> cases f r i <;> rfl

/-- The round undoes the inverse round. -/
theorem feistelRound_invRound {n : ℕ}
    (f : (Fin n → Bool) → (Fin n → Bool))
    (p : (Fin n → Bool) × (Fin n → Bool)) :
    feistelRound f (feistelRoundInv f p) = p := by
  obtain ⟨a, b⟩ := p
  simp only [feistelRound, feistelRoundInv]
  congr 1
  funext i
  cases b i <;> cases f a i <;> rfl

/-- Three Feistel rounds are a permutation of the block
space, whatever the round functions are: the explicit
inverse is the inverse rounds in reverse order. -/
theorem feistel3_bijective {n : ℕ}
    (f₁ f₂ f₃ : (Fin n → Bool) → (Fin n → Bool)) :
    Function.Bijective (feistelRound f₃ ∘ feistelRound f₂ ∘ feistelRound f₁) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨feistelRoundInv f₁ ∘ feistelRoundInv f₂ ∘ feistelRoundInv f₃, ?_, ?_⟩
  · intro p
    simp only [Function.comp_apply, feistelRoundInv_round]
  · intro p
    simp only [Function.comp_apply, feistelRound_invRound]

end
