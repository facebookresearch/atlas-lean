/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.FiniteAbelian.PiZModDualProduct

@[expose] public section

universe u

open scoped BigOperators

/-- Consumer with the original binders, generalised to an arbitrary
universe for `L`. -/
private theorem exactSource
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    (L : Type u) [AddCommGroup L] [Finite L]
    (e : L × (L →+ ZMod d) ≃+ (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) :
    Nonempty (L ≃+ ((i : Fin g) → ZMod (δ i))) :=
  AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod δ hδd L e

/-- Higher-universe consumer: `L` may live in `Type 1`. -/
example
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    (L : Type 1) [AddCommGroup L] [Finite L]
    (e : L × (L →+ ZMod d) ≃+ (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) :
    Nonempty (L ≃+ ((i : Fin g) → ZMod (δ i))) :=
  exactSource δ hδd L e

/-- Single-factor specialization (`g = 1`, `δ = fun _ => m`): the
hypothesis identifies `L × (L →+ ZMod m)` with the square of
`Fin 1 → ZMod m`, and the conclusion recovers `L` as that product. -/
example
    (m : ℕ) [NeZero m]
    (L : Type) [AddCommGroup L] [Finite L]
    (e : L × (L →+ ZMod m) ≃+ ((Fin 1 → ZMod m) × (Fin 1 → ZMod m))) :
    Nonempty (L ≃+ (Fin 1 → ZMod m)) :=
  exactSource (fun _ => m) (by simp) L e
