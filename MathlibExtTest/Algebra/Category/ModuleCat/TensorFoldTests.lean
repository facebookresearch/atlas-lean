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

import MathlibExt.Algebra.Category.ModuleCat.TensorFold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

open CategoryTheory
open scoped TensorProduct

set_option autoImplicit false

universe v

namespace MathlibExtTest.TensorFold

abbrev P : ModuleCat.{v} ℤ := ModuleCat.of ℤ (ULift.{v} ℤ)
abbrev Z : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ

def down : P.{v} →ₗ[ℤ] ℤ where
  toFun := ULift.down
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def multiplication : ℤ →ₗ[ℤ] ℤ →ₗ[ℤ] ℤ where
  toFun x :=
    { toFun y := x * y
      map_add' := by intros; ring
      map_smul' := by
        intro r y
        change x * (r * y) = r * (x * y)
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change (x + y) * z = x * z + y * z
    ring
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    change (r * x) * y = r * (x * y)
    ring

def evaluate : ModuleCat.TensorFold.objAt.{0,v,0} ℤ P [Z, Z] →ₗ[ℤ] ℤ :=
  let pair : P.{v} ⊗[ℤ] ℤ →ₗ[ℤ] ℤ :=
    TensorProduct.lift (multiplication.comp down.{v})
  TensorProduct.lift (multiplication.comp pair)

def probe : ModuleCat.TensorFold.objAt.{0,v,0} ℤ P [Z, Z] :=
  ((ULift.up (1 : ℤ) : P) ⊗ₜ[ℤ] (2 : ℤ)) ⊗ₜ[ℤ] (3 : ℤ)

def negPrefix : P ⟶ P := ModuleCat.ofHom (-LinearMap.id)

def negIso : Z ≅ Z :=
  (show ℤ ≃ₗ[ℤ] ℤ from
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by intro x y; simp [add_comm]
      map_smul' := by intros; simp }).toModuleIso

def factors : Fin 2 → ModuleCat.{0} ℤ := fun _ => Z

def factorIsos (i : Fin 2) : factors i ≅ factors i :=
  if i = 0 then negIso else Iso.refl Z

def coefficientIso :=
  ModuleCat.TensorFold.isoAt.{0,v,0} ℤ (Iso.refl P) factors factors factorIsos

theorem probe_value : evaluate probe = 6 := by
  simp [evaluate, probe, multiplication, down]

theorem negative_prefix_value :
    evaluate ((ModuleCat.TensorFold.mapAt.{0,v,0} ℤ negPrefix [Z, Z]).hom probe) = -6 := by
  simp [evaluate, probe, negPrefix, multiplication, down,
    ModuleCat.TensorFold.mapAt_cons, ModuleCat.TensorFold.mapAt_nil]

theorem negative_prefix_nonzero :
    (ModuleCat.TensorFold.mapAt.{0,v,0} ℤ negPrefix [Z, Z]).hom probe ≠ 0 := by
  intro h
  have he := congrArg evaluate h
  rw [negative_prefix_value, map_zero] at he
  norm_num at he

theorem negative_factor_value : evaluate (coefficientIso.hom probe) = -6 := by
  simp [coefficientIso, ModuleCat.TensorFold.isoAt, factors, factorIsos, negIso,
    evaluate, probe, multiplication, down]

theorem coefficient_square :
    ModuleCat.TensorFold.mapAt.{0,v,0} ℤ negPrefix (List.ofFn factors) ≫ coefficientIso.hom =
      coefficientIso.hom ≫ ModuleCat.TensorFold.mapAt.{0,v,0} ℤ negPrefix (List.ofFn factors) := by
  exact ModuleCat.TensorFold.isoAt_naturality.{0,v,0}
    ℤ negPrefix negPrefix (Iso.refl P) (Iso.refl P) factors factors factorIsos
    (by simp)

end MathlibExtTest.TensorFold
