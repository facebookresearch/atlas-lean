/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Encode

import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Combinatorial weak-diagonal K-zero equivalence

The multiplicative view of the K-zero encode is inverse to the based
weak-diagonal decode.  Decode after encode is proved on K-zero generators by
`K0.hom_ext`; encode after decode is proved on object-edge generators and
extended through the landed subgroup-generation theorem.  The resulting
decode-forward multiplicative equivalence has a canonical additive form via
the standard type-tag adapter.

This is a combinatorial equivalence only.  It installs no global algebraic
typeclass and makes no realization, topological `pi_0`, additivity-map,
spectrum, or Q/S claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- Multiplicative view of the additive K-zero encode. -/
noncomputable def stageWeakDiagonalK0EncodeMul :
    Multiplicative (WaldhausenKTheory.K0 C) →*
      stageWeakDiagonalFundamentalGroup C :=
  AddMonoidHom.toMultiplicativeLeft (stageWeakDiagonalK0Encode C)

@[simp]
theorem stageWeakDiagonalK0EncodeMul_ofAdd
    (x : WaldhausenKTheory.K0 C) :
    stageWeakDiagonalK0EncodeMul C (Multiplicative.ofAdd x) =
      Additive.toMul (stageWeakDiagonalK0Encode C x) :=
  rfl

theorem stageWeakDiagonalK0EncodeMul_mk (X : C) :
    stageWeakDiagonalK0EncodeMul C
        (Multiplicative.ofAdd (WaldhausenKTheory.K0.mk X)) =
      stageWeakDiagonalObjectGenerator C X := by
  change Additive.toMul
      (stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk X)) = _
  rw [stageWeakDiagonalK0Encode_mk]
  rfl

/-- Additive-hom form of the first inverse: decoding after encoding is the
identity on Waldhausen K-zero. -/
theorem stageWeakDiagonalK0DecodeAdd_comp_encode :
    (MonoidHom.toAdditiveLeft
        (stageWeakDiagonalFundamentalToK0 C)).comp
      (stageWeakDiagonalK0Encode C) =
    AddMonoidHom.id (WaldhausenKTheory.K0 C) := by
  apply WaldhausenKTheory.K0.hom_ext
  intro X
  change Multiplicative.toAdd
      (stageWeakDiagonalFundamentalToK0 C
        (Additive.toMul
          (stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk X)))) =
    WaldhausenKTheory.K0.mk X
  rw [stageWeakDiagonalK0Encode_mk]
  change Multiplicative.toAdd
      (stageWeakDiagonalFundamentalToK0 C
        (stageWeakDiagonalObjectGenerator C X)) = _
  rw [stageWeakDiagonalFundamentalToK0_objectGenerator]
  rfl

/-- Pointwise multiplicative first inverse. -/
@[simp]
theorem stageWeakDiagonalK0Decode_encodeMul
    (x : Multiplicative (WaldhausenKTheory.K0 C)) :
    stageWeakDiagonalFundamentalToK0 C
        (stageWeakDiagonalK0EncodeMul C x) = x := by
  induction x using Multiplicative.rec with
  | ofAdd x =>
      apply Multiplicative.toAdd.injective
      change ((MonoidHom.toAdditiveLeft
          (stageWeakDiagonalFundamentalToK0 C)).comp
        (stageWeakDiagonalK0Encode C)) x = x
      exact DFunLike.congr_fun
        (stageWeakDiagonalK0DecodeAdd_comp_encode C) x

/-- Pointwise second inverse, extended from object generators through the
landed subgroup-generation theorem. -/
@[simp]
theorem stageWeakDiagonalK0EncodeMul_decode
    (f : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalK0EncodeMul C
        (stageWeakDiagonalFundamentalToK0 C f) = f := by
  let F := (stageWeakDiagonalK0EncodeMul C).comp
    (stageWeakDiagonalFundamentalToK0 C)
  have hf := stageWeakDiagonalFundamentalGroup_mem_objectGenerators C f
  change f ∈ Subgroup.closure
    (Set.range (stageWeakDiagonalObjectGenerator C)) at hf
  change F f = f
  induction hf using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨A, rfl⟩ := hx
      dsimp only [F]
      change stageWeakDiagonalK0EncodeMul C
          (stageWeakDiagonalFundamentalToK0 C
            (stageWeakDiagonalObjectGenerator C A)) = _
      rw [stageWeakDiagonalFundamentalToK0_objectGenerator,
        stageWeakDiagonalK0EncodeMul_mk]
  | one => exact F.map_one
  | mul x y _ _ hx hy =>
      rw [F.map_mul, hx, hy]
  | inv x _ hx =>
      rw [map_inv, hx]

/-- Decode-forward multiplicative equivalence between the combinatorial
based fundamental group and multiplicative Waldhausen K-zero. -/
noncomputable def stageWeakDiagonalFundamentalK0MulEquiv :
    stageWeakDiagonalFundamentalGroup C ≃*
      Multiplicative (WaldhausenKTheory.K0 C) where
  toFun := stageWeakDiagonalFundamentalToK0 C
  invFun := stageWeakDiagonalK0EncodeMul C
  left_inv := stageWeakDiagonalK0EncodeMul_decode C
  right_inv := stageWeakDiagonalK0Decode_encodeMul C
  map_mul' := (stageWeakDiagonalFundamentalToK0 C).map_mul

@[simp]
theorem stageWeakDiagonalFundamentalK0MulEquiv_apply
    (f : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalFundamentalK0MulEquiv C f =
      stageWeakDiagonalFundamentalToK0 C f :=
  rfl

@[simp]
theorem stageWeakDiagonalFundamentalK0MulEquiv_symm_apply
    (x : Multiplicative (WaldhausenKTheory.K0 C)) :
    (stageWeakDiagonalFundamentalK0MulEquiv C).symm x =
      stageWeakDiagonalK0EncodeMul C x :=
  rfl

theorem stageWeakDiagonalFundamentalK0MulEquiv_objectGenerator (X : C) :
    stageWeakDiagonalFundamentalK0MulEquiv C
        (stageWeakDiagonalObjectGenerator C X) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk X) :=
  stageWeakDiagonalFundamentalToK0_objectGenerator C X

theorem stageWeakDiagonalFundamentalK0MulEquiv_symm_mk (X : C) :
    (stageWeakDiagonalFundamentalK0MulEquiv C).symm
        (Multiplicative.ofAdd (WaldhausenKTheory.K0.mk X)) =
      stageWeakDiagonalObjectGenerator C X :=
  stageWeakDiagonalK0EncodeMul_mk C X

/-- Canonical decode-forward additive equivalence. -/
noncomputable def stageWeakDiagonalFundamentalK0AddEquiv :
    Additive (stageWeakDiagonalFundamentalGroup C) ≃+
      WaldhausenKTheory.K0 C :=
  MulEquiv.toAdditiveLeft (stageWeakDiagonalFundamentalK0MulEquiv C)

@[simp]
theorem stageWeakDiagonalFundamentalK0AddEquiv_apply
    (f : Additive (stageWeakDiagonalFundamentalGroup C)) :
    stageWeakDiagonalFundamentalK0AddEquiv C f =
      Multiplicative.toAdd
        (stageWeakDiagonalFundamentalToK0 C (Additive.toMul f)) :=
  rfl

@[simp]
theorem stageWeakDiagonalFundamentalK0AddEquiv_symm_apply
    (x : WaldhausenKTheory.K0 C) :
    (stageWeakDiagonalFundamentalK0AddEquiv C).symm x =
      stageWeakDiagonalK0Encode C x := by
  change Additive.ofMul
      (stageWeakDiagonalK0EncodeMul C (Multiplicative.ofAdd x)) = _
  rw [stageWeakDiagonalK0EncodeMul_ofAdd]
  rfl

theorem stageWeakDiagonalFundamentalK0AddEquiv_objectGenerator (X : C) :
    stageWeakDiagonalFundamentalK0AddEquiv C
        (Additive.ofMul (stageWeakDiagonalObjectGenerator C X)) =
      WaldhausenKTheory.K0.mk X := by
  change Multiplicative.toAdd
      (stageWeakDiagonalFundamentalToK0 C
        (stageWeakDiagonalObjectGenerator C X)) = _
  rw [stageWeakDiagonalFundamentalToK0_objectGenerator]
  rfl

theorem stageWeakDiagonalFundamentalK0AddEquiv_symm_mk (X : C) :
    (stageWeakDiagonalFundamentalK0AddEquiv C).symm
        (WaldhausenKTheory.K0.mk X) =
      Additive.ofMul (stageWeakDiagonalObjectGenerator C X) := by
  rw [stageWeakDiagonalFundamentalK0AddEquiv_symm_apply,
    stageWeakDiagonalK0Encode_mk]

end CategoryTheory.Waldhausen.SConstruction

end
