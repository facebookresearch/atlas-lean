/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.PairingAdjointKernel

@[expose] public section

/-- Consumer with the original binders of the source statement. -/
private theorem exactSource
    {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
    (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hleft : ∀ x, (∀ y, e x y = 1) → x = 0)
    (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
    (hsurj : ∀ χ : Multiplicative P →* Kˣ, ∃ y,
      ∀ x, e x y = χ (Multiplicative.ofAdd x))
    (T T' : P →+ P) (hadj : ∀ x y, e (T x) y = e x (T' y)) :
    Nat.card (T.ker) = Nat.card (T'.ker) :=
  AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint
    e hadd₁ hadd₂ hleft hright hsurj T T' hadj

/-- The identically zero and identity endomorphisms are adjoint for the
trivial pairing, but their kernels have different cardinalities. Hence
some nondegeneracy or character-surjectivity hypothesis is necessary. -/
example :
    Nat.card ((0 : ZMod 2 →+ ZMod 2).ker) ≠
      Nat.card ((AddMonoidHom.id (ZMod 2)).ker) := by
  have e1 : (0 : ZMod 2 →+ ZMod 2).ker ≃ ZMod 2 :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, by simp⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : (AddMonoidHom.id (ZMod 2)).ker ≃ (PUnit : Type) :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨0, by simp⟩
      left_inv := fun x => by
        have hx : (x : ZMod 2) = 0 := x.2
        exact Subtype.ext hx.symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2]
  simp
