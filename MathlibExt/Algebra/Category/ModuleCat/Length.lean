/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Length

/-!
# Module length under surjective restriction of scalars

For a surjective ring homomorphism f:R→S and any S-module M, restriction of scalars gives the
same lattice of submodules. Its extended-natural composition length therefore satisfies
ℓ_R(U_fM)=ℓ_S(M), including the value ∞. The rings need not be commutative, and their universes
and the module universe are independent.

If e:R≅S is a ring isomorphism and an R-module M is linearly isomorphic to the restriction of an
S-module N, then ℓ_R(M)=ℓ_S(N). This comparison combines invariance under the module isomorphism
with surjective scalar restriction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace ModuleCat

universe u v w

/-- Let R,S be rings in independent universes u,v, f:R→S a surjective ring homomorphism and M an
S-module in universe w. Then ℓ_R(U_fM)=ℓ_S(M) as extended natural numbers. Surjectivity
identifies the R-submodule and S-submodule lattices of M, so the equality includes modules of
infinite length. -/
theorem restrictScalars_length_eq
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{w} S) :
    Module.length R ((restrictScalars f).obj M) = Module.length S M := by
  let : RingHomSurjective f := ⟨hf⟩
  let g : (restrictScalars f).obj M →ₛₗ[f] M :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective g
      ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩)

/-- Let R,S be rings in the same universe u, e:R≅S a ring isomorphism, M an R-module and N an
S-module in universe v. For a specified module isomorphism M≅U_eN, the extended-natural lengths
satisfy ℓ_R(M)=ℓ_S(N). The equality follows from linear-isomorphism invariance and surjectivity
of the ring equivalence. -/
theorem length_eq_of_restrictScalarsIso
    {R S : Type u} [Ring R] [Ring S]
    (eR : R ≃+* S) (M : ModuleCat.{v} R) (N : ModuleCat.{v} S)
    (e : M ≅ (ModuleCat.restrictScalars eR.toRingHom).obj N) :
    Module.length R M = Module.length S N :=
  e.toLinearEquiv.length_eq.trans
    (restrictScalars_length_eq eR.toRingHom eR.surjective N)

end ModuleCat
