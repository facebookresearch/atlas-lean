/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Restriction of `ZMod n` representations to integral representations

The functorial action maps of a `ZMod n` representation are additive, hence
canonically `ℤ`-linear.  This file packages the resulting `Rep ℤ` object.
The construction includes `n = 0`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

namespace Rep

variable {G : Type u} [Group G]

/-- Restrict a `ZMod n` representation along `Int.castRingHom (ZMod n)`.
The carrier and group action are unchanged. -/
noncomputable def zmodRestrictInt (n : ℕ) (A : Rep.{v} (ZMod n) G) :
    Rep ℤ G :=
  Rep.of
    { toFun := fun g => (A.ρ g).toAddMonoidHom.toIntLinearMap
      map_one' := by
        apply LinearMap.ext
        intro x
        change A.ρ 1 x = x
        exact DFunLike.congr_fun (map_one A.ρ) x
      map_mul' := fun g h => by
        apply LinearMap.ext
        intro x
        change A.ρ (g * h) x = A.ρ g (A.ρ h x)
        exact DFunLike.congr_fun (map_mul A.ρ g h) x }

/-- Restriction leaves the carrier unchanged. -/
theorem zmodRestrictInt_carrier (n : ℕ) (A : Rep.{v} (ZMod n) G) :
    (zmodRestrictInt n A).V = A.V :=
  rfl

/-- Restriction leaves the group action unchanged pointwise. -/
@[simp]
theorem zmodRestrictInt_action (n : ℕ) (A : Rep.{v} (ZMod n) G)
    (g : G) (x : zmodRestrictInt n A) :
    (zmodRestrictInt n A).ρ g x = A.ρ g x :=
  rfl

/-- The integral scalar action is the original `ZMod n` action through the
integer-cast homomorphism. -/
theorem zmodRestrictInt_smul (n : ℕ) (A : Rep.{v} (ZMod n) G)
    (z : ℤ) (x : zmodRestrictInt n A) :
    z • x = A.hV2.smul (z : ZMod n) x := by
  let _ : Module (ZMod n) (zmodRestrictInt n A : Type v) := A.hV2
  exact (Int.cast_smul_eq_zsmul (ZMod n) z x).symm

/-- Restriction of scalars on a morphism of `ZMod n` representations. -/
noncomputable def zmodRestrictIntMap {n : ℕ}
    {A B : Rep.{v} (ZMod n) G} (f : A ⟶ B) :
    zmodRestrictInt n A ⟶ zmodRestrictInt n B :=
  Rep.ofHom
    { toLinearMap := f.hom.toAddMonoidHom.toIntLinearMap
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        change f.hom (A.ρ g x) = B.ρ g (f.hom x)
        exact Rep.hom_comm_apply f g x }

@[simp]
theorem zmodRestrictIntMap_apply {n : ℕ}
    {A B : Rep.{v} (ZMod n) G} (f : A ⟶ B) (x : A) :
    zmodRestrictIntMap f x = f x :=
  rfl

/-- Restriction of scalars sends an isomorphism of `ZMod n`
representations to an isomorphism of integral representations. -/
noncomputable def zmodRestrictIntIso {n : ℕ}
    {A B : Rep.{v} (ZMod n) G} (e : A ≅ B) :
    zmodRestrictInt n A ≅ zmodRestrictInt n B where
  hom := zmodRestrictIntMap e.hom
  inv := zmodRestrictIntMap e.inv
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact Rep.inv_hom_apply A B e (show A from x)
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact Rep.hom_inv_apply A B e (show B from x)

@[simp]
theorem zmodRestrictIntIso_hom_apply {n : ℕ}
    {A B : Rep.{v} (ZMod n) G} (e : A ≅ B) (x : A) :
    (zmodRestrictIntIso e).hom x = e.hom x :=
  rfl

end Rep
