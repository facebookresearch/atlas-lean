/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Algebra_DescentCofaces.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent coface maps

For an `A`-algebra `B`, the two inclusions `B → B ⊗[A] B` and the three
coface maps `B ⊗[A] B → B ⊗[A] (B ⊗[A] B)` satisfy the cosimplicial
identities. They are the structure maps for descent data of `B`-modules
along `A → B`, with the cocycle condition stated via the transport `T`.
-/

@[expose] public section

universe u

open TensorProduct CategoryTheory

noncomputable section

namespace Algebra.DescentCofaces

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The second tensor power `B ⊗[A] B` as an object of `CommRingCat`. -/
abbrev R₂ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] B)

/-- The third tensor power `B ⊗[A] (B ⊗[A] B)` as an object of `CommRingCat`. -/
abbrev R₃ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] (B ⊗[A] B))

/-- The first inclusion `B → B ⊗[A] B`. -/
def i₁ : CommRingCat.of B ⟶ R₂ A B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- The second inclusion `B → B ⊗[A] B`. -/
def i₂ : CommRingCat.of B ⟶ R₂ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom

/-- The coface map placing the source factors in positions 1–2 (inserting the unit in
the third position). -/
def c₁₂ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := B))).toRingHom

/-- The coface map placing the source factors in positions 2–3 (inserting the unit in
the first position). -/
def c₂₃ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B ⊗[A] B)).toRingHom

/-- The coface map placing the source factors in positions 1 and 3 (inserting the unit
in the second position). -/
def c₁₃ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B))).toRingHom

@[simp] theorem i₁_apply (b : B) : (i₁ A B).hom b = b ⊗ₜ 1 := rfl
@[simp] theorem i₂_apply (b : B) : (i₂ A B).hom b = 1 ⊗ₜ b := rfl
@[simp] theorem c₁₂_tmul (b b' : B) : (c₁₂ A B).hom (b ⊗ₜ b') = b ⊗ₜ (b' ⊗ₜ 1) := rfl
@[simp] theorem c₂₃_tmul (b b' : B) : (c₂₃ A B).hom (b ⊗ₜ b') = 1 ⊗ₜ (b ⊗ₜ b') := rfl
@[simp] theorem c₁₃_tmul (b b' : B) : (c₁₃ A B).hom (b ⊗ₜ b') = b ⊗ₜ (1 ⊗ₜ b') := rfl

theorem i₁_c₁₂ : i₁ A B ≫ c₁₂ A B = i₁ A B ≫ c₁₃ A B := rfl
theorem i₂_c₁₂ : i₂ A B ≫ c₁₂ A B = i₁ A B ≫ c₂₃ A B := rfl
theorem i₂_c₁₃ : i₂ A B ≫ c₁₃ A B = i₂ A B ≫ c₂₃ A B := rfl

theorem algebraMap_i₁_eq_i₂ :
    CommRingCat.ofHom (algebraMap A B) ≫ i₁ A B = CommRingCat.ofHom (algebraMap A B) ≫ i₂ A B := by
  ext a
  change algebraMap A B a ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] algebraMap A B a
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem i₁_comp_algebraMap_eq :
    (i₁ A B).hom.comp (algebraMap A B) = (i₂ A B).hom.comp (algebraMap A B) :=
  congrArg CommRingCat.Hom.hom (algebraMap_i₁_eq_i₂ A B)

/-- The canonical comparison between the two pullbacks of an `A`-module along
the two inclusions. -/
def canonical (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (i₁ A B).hom).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) ⟶
      (ModuleCat.extendScalars (i₂ A B).hom).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  (ModuleCat.extendScalarsComp (algebraMap A B) (i₁ A B).hom).inv.app M ≫
    eqToHom (congrArg (fun f : A →+* B ⊗[A] B => (ModuleCat.extendScalars f).obj M)
      (i₁_comp_algebraMap_eq A B)) ≫
    (ModuleCat.extendScalarsComp (algebraMap A B) (i₂ A B).hom).hom.app M

variable {A B} in
/-- Transport of a descent isomorphism along a coface map. -/
def T (N : ModuleCat.{u} B) (c : R₂ A B ⟶ R₃ A B)
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶
      (ModuleCat.extendScalars (i₂ A B).hom).obj N) :
    (ModuleCat.extendScalars (i₁ A B ≫ c).hom).obj N ⟶
      (ModuleCat.extendScalars (i₂ A B ≫ c).hom).obj N :=
  (ModuleCat.extendScalarsComp (i₁ A B).hom c.hom).hom.app N ≫
    (ModuleCat.extendScalars c.hom).map φ' ≫
    (ModuleCat.extendScalarsComp (i₂ A B).hom c.hom).inv.app N

variable {A B} in
/-- Transport of the identity morphism is the identity. -/
theorem T_id (N : ModuleCat.{u} B) (c : R₂ A B ⟶ R₃ A B) :
    T N c (𝟙 _) = 𝟙 _ := by
  simp [T]

variable {A B} in
/-- The cocycle condition for a descent isomorphism. `φ'` is an isomorphism: the zero
morphism satisfies the displayed equation but is not descent data. -/
def Cocycle (N : ModuleCat.{u} B)
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj N ≅
      (ModuleCat.extendScalars (i₂ A B).hom).obj N) : Prop :=
  T N (c₁₂ A B) φ'.hom ≫ T N (c₂₃ A B) φ'.hom = T N (c₁₃ A B) φ'.hom

end Algebra.DescentCofaces

end
