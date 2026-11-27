/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Quandle
import Mathlib.GroupTheory.SpecificGroups.Dihedral

open Equiv MetaMathlibExt Quandles

-- Membership in the exposed definition still reduces to preservation of the rack operation.
example (R : Type*) [Rack R] (f : Perm R) :
    f ∈ rackAut R ↔ ∀ x y, f (x ◃ y) = f x ◃ f y := Iff.rfl

-- The conjugation quandle of the centerless dihedral group of order six has no extra symmetries.
example : (MulAut.toPerm (M := DihedralGroup 3)).range = rackAut (Quandle.Conj (DihedralGroup 3)) :=
  (center_eq_bot_iff_mulAut_eq_rackAut_conj _).mp
    (DihedralGroup.center_eq_bot_of_odd_ne_one ⟨1, rfl⟩ (by decide))

-- On the cyclic group of order two, the conjugation quandle has extra symmetries.
example : (MulAut.toPerm (M := Multiplicative (ZMod 2))).range ≠
    rackAut (Quandle.Conj (Multiplicative (ZMod 2))) := by
  intro h
  have hc := (center_eq_bot_iff_mulAut_eq_rackAut_conj _).mpr h
  have hx : Multiplicative.ofAdd (1 : ZMod 2) ∈ Subgroup.center (Multiplicative (ZMod 2)) := by
    rw [CommGroup.center_eq_top]
    exact Subgroup.mem_top _
  rw [hc, Subgroup.mem_bot] at hx
  exact (by decide : (1 : ZMod 2) ≠ 0) (congrArg Multiplicative.toAdd hx)
