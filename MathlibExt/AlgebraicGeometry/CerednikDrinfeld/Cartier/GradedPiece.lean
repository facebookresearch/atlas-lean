/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_CartierGradedPiece.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.Homothety

/-!
# Graded pieces of the Cartier module of a formal `O_D`-module

For a formal `O_D`-module `X` over `B` and a ring homomorphism `j : Zp2 p →+* B`,
`FormalODModule.gradedPiece X j n` is the subgroup of the Cartier module of `X` on which each
Teichmüller representative `[c]` of `GaloisField p 2` acts as the homothety by
`j [c] ^ p ^ n`. Because `c ^ p ^ 2 = c`, the grading has period two
(`gradedPiece_add_two`, `gradedPiece_add_two_mul`).

## References

* J.-F. Boutot and H. Carayol, *Uniformisation p-adique des courbes de Shimura : les théorèmes
  de Čerednik et de Drinfeld*, in *Courbes modulaires et courbes de Shimura*, Astérisque
  196–197 (1991), 45–158, for special formal `O_D`-modules and their Cartier modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

/-- **Graded piece of the Cartier module.** For a formal `O_D`-module `X` over a commutative
ring `B`, a ring homomorphism `j : Zp2 p →+* B`, where `Zp2 p` is the ring of Witt vectors of
`GaloisField p 2`, and `n : ℕ`, the subgroup of the Cartier module of `X` on which, for every
`c : GaloisField p 2`, the action of the Teichmüller representative `[c]` agrees with the
homothety by `j [c] ^ p ^ n`. -/
def gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    AddSubgroup (CartierModule p X.F) where
  carrier := {f | ∀ c : GaloisField p 2,
    endAct (X.actEnd (WittVector.teichmuller p c)) f =
      homothety (j (WittVector.teichmuller p c) ^ p ^ n) f}
  zero_mem' := fun c => by simp only [map_zero]
  add_mem' := fun {f g} hf hg c => by simp only [map_add, hf c, hg c]
  neg_mem' := fun {f} hf c => by simp only [map_neg, hf c]

theorem mem_gradedPiece_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) :
    f ∈ X.gradedPiece j n ↔ ∀ c : GaloisField p 2,
      endAct (X.actEnd (WittVector.teichmuller p c)) f =
        homothety (j (WittVector.teichmuller p c) ^ p ^ n) f :=
  Iff.rfl

theorem pow_card_galoisField (c : GaloisField p 2) : c ^ p ^ 2 = c := by
  let : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]
  rw [← hcard]
  exact FiniteField.pow_card c

theorem apply_teichmuller_pow_pow_add_two (j : Zp2 p →+* B) (c : GaloisField p 2) (n : ℕ) :
    j (WittVector.teichmuller p c) ^ p ^ (n + 2) = j (WittVector.teichmuller p c) ^ p ^ n := by
  rw [pow_add, pow_mul, ← map_pow, ← map_pow, ← map_pow, ← map_pow, ← pow_mul, mul_comm, pow_mul,
    pow_card_galoisField]

theorem gradedPiece_add_two (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    X.gradedPiece j (n + 2) = X.gradedPiece j n := by
  ext f
  simp only [mem_gradedPiece_iff, apply_teichmuller_pow_pow_add_two]

theorem gradedPiece_add_two_mul (X : FormalODModule p B) (j : Zp2 p →+* B) (n k : ℕ) :
    X.gradedPiece j (n + 2 * k) = X.gradedPiece j n := by
  induction k with
  | zero => rw [mul_zero, add_zero]
  | succ k ih => rw [mul_add, mul_one, ← add_assoc, gradedPiece_add_two, ih]

end FormalODModule

end CerednikDrinfeld

end
