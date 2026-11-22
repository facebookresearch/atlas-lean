/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Feistel rounds

A Feistel round with round function `f` maps a block `(l, r)` of two half-blocks to
`(r, l xor f r)`. Half-blocks are bit strings `Fin n → Bool`, and xor is pointwise. For every
round function the round is a permutation of the block space, with inverse
`(a, b) ↦ (b xor f a, a)`, so rounds compose to permutations whatever the round functions are.

`feistelRound f` is an `Equiv.Perm`, the permutation type of the block-cipher API
`Cslib.Crypto.Modes.BlockCipher K X := K → Equiv.Perm X`. The pseudorandomness of Feistel
networks with pseudorandom round functions (Luby and Rackoff) is not proved here.

## Main declarations

* `Cslib.Crypto.Feistel.feistelRound`: one Feistel round, as a permutation of the block space.
* `Cslib.Crypto.Feistel.feistelRound_apply`, `Cslib.Crypto.Feistel.feistelRound_symm_apply`:
  the round and its inverse on a block.
* `Cslib.Crypto.Feistel.feistel3_bijective`: three rounds are a bijection.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Chapter 6.
* M. Luby and C. Rackoff, *How to construct pseudorandom permutations from pseudorandom
  functions*, SIAM J. Comput. 17(2), 1988.
-/

@[expose] public section

namespace Cslib.Crypto.Feistel

variable {n : ℕ}

/-- One Feistel round with round function `f`, as a permutation of the block space: it maps
`(l, r)` to `(r, l xor f r)`, and its inverse maps `(a, b)` to `(b xor f a, a)`. -/
def feistelRound (f : (Fin n → Bool) → (Fin n → Bool)) :
    Equiv.Perm ((Fin n → Bool) × (Fin n → Bool)) where
  toFun p := (p.2, fun i => Bool.xor (p.1 i) (f p.2 i))
  invFun p := (fun i => Bool.xor (p.2 i) (f p.1 i), p.1)
  left_inv := by
    rintro ⟨l, r⟩
    refine Prod.ext (funext fun i => ?_) rfl
    dsimp only
    cases l i <;> cases f r i <;> rfl
  right_inv := by
    rintro ⟨a, b⟩
    refine Prod.ext rfl (funext fun i => ?_)
    dsimp only
    cases b i <;> cases f a i <;> rfl

@[simp]
theorem feistelRound_apply (f : (Fin n → Bool) → (Fin n → Bool)) (l r : Fin n → Bool) :
    feistelRound f (l, r) = (r, fun i => Bool.xor (l i) (f r i)) :=
  rfl

@[simp]
theorem feistelRound_symm_apply (f : (Fin n → Bool) → (Fin n → Bool)) (a b : Fin n → Bool) :
    (feistelRound f).symm (a, b) = (fun i => Bool.xor (b i) (f a i), a) :=
  rfl

/-- Three Feistel rounds are a bijection of the block space, whatever the round functions are:
each round is a permutation (`feistelRound`), and so is their composite. -/
theorem feistel3_bijective (f₁ f₂ f₃ : (Fin n → Bool) → (Fin n → Bool)) :
    Function.Bijective (feistelRound f₃ ∘ feistelRound f₂ ∘ feistelRound f₁) :=
  (feistelRound f₃).bijective.comp ((feistelRound f₂).bijective.comp (feistelRound f₁).bijective)

end Cslib.Crypto.Feistel
