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
# Integral scalar restriction of residue-ring representations

Let n∈ℕ, G a group in universe u and A a ZMod n-representation
with coefficient carrier in universe v. The additive group of A
has its integer-module structure, and each G-action map is ℤ-linear.
This gives the integral representation Res(A) on the same carrier.

An integer z acts by its residue in ZMod n on A.
Coefficient morphisms and isomorphisms retain their underlying maps
under this restriction. All n, including n=0, are allowed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

namespace Rep

variable {G : Type u} [Group G]

/-- Let n∈ℕ, G a group in universe u and A a ZMod n-representation
with carrier universe v. The scalar restriction Res(A) to ℤ keeps
the carrier and G-action. The case n=0 is included.
Res(A) is the ℤ-linear representation on the additive group
of A, using the original G-action and integer scalar action. -/
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

/-- Let n∈ℕ, G a group in universe u and A a ZMod n-representation
with carrier universe v. The scalar restriction Res(A) to ℤ keeps
the carrier and G-action. The case n=0 is included.
The carrier of Res(A) is the same carrier A.V. -/
theorem zmodRestrictInt_carrier (n : ℕ) (A : Rep.{v} (ZMod n) G) :
    (zmodRestrictInt n A).V = A.V :=
  rfl

/-- Let n∈ℕ, G a group in universe u and A a ZMod n-representation
with carrier universe v. The scalar restriction Res(A) to ℤ keeps
the carrier and G-action. The case n=0 is included.
For g∈G and x in the coefficient carrier, the action satisfies
ρ_Res(A)(g)(x)=ρ_A(g)(x). -/
@[simp]
theorem zmodRestrictInt_action (n : ℕ) (A : Rep.{v} (ZMod n) G)
    (g : G) (x : zmodRestrictInt n A) :
    (zmodRestrictInt n A).ρ g x = A.ρ g x :=
  rfl

/-- Let n∈ℕ, G a group in universe u and A a ZMod n-representation
with carrier universe v. The scalar restriction Res(A) to ℤ keeps
the carrier and G-action. The case n=0 is included.
For z∈ℤ and x∈Res(A), its integer scalar has value
z•x=(z mod n)•_A x. -/
theorem zmodRestrictInt_smul (n : ℕ) (A : Rep.{v} (ZMod n) G)
    (z : ℤ) (x : zmodRestrictInt n A) :
    z • x = A.hV2.smul (z : ZMod n) x := by
  let _ : Module (ZMod n) (zmodRestrictInt n A : Type v) := A.hV2
  exact (Int.cast_smul_eq_zsmul (ZMod n) z x).symm

/-- Let n∈ℕ, G a group in universe u and A a ZMod n-representation
with carrier universe v. The scalar restriction Res(A) to ℤ keeps
the carrier and G-action. The case n=0 is included.
A morphism t:A→B of ZMod n-representations gives the integral
morphism Res(t):Res(A)→Res(B) with the same additive map. -/
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

/-- Let n∈ℕ, G a group in universe u and A a ZMod n-representation
with carrier universe v. The scalar restriction Res(A) to ℤ keeps
the carrier and G-action. The case n=0 is included.
An isomorphism e:A≅B of ZMod n-representations gives
Res(A)≅Res(B), with forward and inverse maps those of e. -/
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
