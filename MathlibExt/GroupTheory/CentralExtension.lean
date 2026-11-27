/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.IsPerfect

/-! # Central group extensions

Centrality and universality predicates, with uniqueness of lifts from perfect groups.
-/

@[expose] public section

universe u v w u' v'

namespace GroupExtension

variable {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]

/-- A group extension is central if the kernel of the projection lies in the center. -/
def IsCentral (S : GroupExtension N E G) : Prop :=
  S.rightHom.ker ≤ Subgroup.center E

/-- Universality among central extensions with explicitly chosen kernel and total universes. -/
def IsUniversalFor (S : GroupExtension N E G) : Prop :=
  S.IsCentral ∧ ∀ {N' : Type u'} {E' : Type v'} [Group N'] [Group E'] (S' : GroupExtension N' E' G),
    S'.IsCentral → ∃! f : E →* E', S'.rightHom.comp f = S.rightHom

/-- A central extension is universal if it is central and every central extension of the same group
in the fixed universes `u` and `v` receives a unique homomorphism commuting with the projections. -/
def IsUniversal (S : GroupExtension N E G) : Prop :=
  IsUniversalFor.{u, v, w, u, v} S

/-- The original universality predicate is the fixed-universe specialization. -/
theorem isUniversalFor_self_iff (S : GroupExtension N E G) :
    IsUniversalFor.{u, v, w, u, v} S ↔ S.IsUniversal := Iff.rfl

end GroupExtension

namespace MonoidHom

variable {P : Type u} {E : Type v} {G : Type w} [Group P] [Group E] [Group G]

open Subgroup
open scoped commutatorElement

/-- If `q` has central kernel and `q ∘ f = q ∘ g`, then `f = g` for perfect `P`. -/
theorem eq_of_comp_eq_of_ker_le_center {q : E →* G} (hq : q.ker ≤ Subgroup.center E)
    {f g : P →* E} (h : q.comp f = q.comp g) [hP : Group.IsPerfect P] : f = g := by
  have h_comm_le : commutator P ≤ f.eqLocus g := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    change f ⁅x, y⁆ = g ⁅x, y⁆
    rw [map_commutatorElement, map_commutatorElement]
    let cx := f x * (g x)⁻¹
    let cy := f y * (g y)⁻¹
    have hq_eq : ∀ t : P, q (f t) = q (g t) := by
      intro t
      have ht := DFunLike.congr_fun h t
      simpa [MonoidHom.comp_apply] using ht
    have hcx_ker : cx ∈ q.ker := by
      rw [MonoidHom.mem_ker]
      change q (f x * (g x)⁻¹) = 1
      rw [map_mul, map_inv, hq_eq x, mul_inv_cancel]
    have hcy_ker : cy ∈ q.ker := by
      rw [MonoidHom.mem_ker]
      change q (f y * (g y)⁻¹) = 1
      rw [map_mul, map_inv, hq_eq y, mul_inv_cancel]
    have hcx_center : cx ∈ Subgroup.center E := hq hcx_ker
    have hcy_center : cy ∈ Subgroup.center E := hq hcy_ker
    have hcx_comm : ∀ a : E, Commute cx a := by
      intro a
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hcx_center a).symm
    have hcy_comm : ∀ a : E, Commute cy a := by
      intro a
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hcy_center a).symm
    -- re-express f x, f y
    have hfx : f x = cx * g x := by
      simp [cx]
    have hfy : f y = cy * g y := by
      simp [cy]
    rw [hfx, hfy]
    have h_comm_cx : ∀ b : E, ⁅cx, b⁆ = 1 := fun b => (hcx_comm b).commutator_eq
    have h_comm_cy : ∀ b : E, ⁅b, cy⁆ = 1 := fun b => ((hcy_comm b).symm).commutator_eq
    -- also need ⁅g x, cy⁆ = 1 via centrality of cy
    have h_gx_cy : ⁅g x, cy⁆ = 1 := h_comm_cy (g x)
    -- central conjugation collapses
    have h_conj_cx : ∀ b : E, cx * b * cx⁻¹ = b := fun b => (hcx_comm b).mul_inv_cancel
    have h_conj_cy : ∀ b : E, cy * b * cy⁻¹ = b := fun b => (hcy_comm b).mul_inv_cancel
    calc ⁅cx * g x, cy * g y⁆
        = cx * ⁅g x, cy * g y⁆ * cx⁻¹ * ⁅cx, cy * g y⁆ := by
            rw [commutatorElement_mul_left_eq_conj_mul]
        _ = cx * ⁅g x, cy * g y⁆ * cx⁻¹ * 1 := by rw [h_comm_cx (cy * g y)]
        _ = cx * ⁅g x, cy * g y⁆ * cx⁻¹ := by rw [mul_one]
        _ = ⁅g x, cy * g y⁆ := by rw [h_conj_cx]
        _ = ⁅g x, cy⁆ * cy * ⁅g x, g y⁆ * cy⁻¹ := by
            rw [commutatorElement_mul_right_eq_mul_conj]
        _ = 1 * cy * ⁅g x, g y⁆ * cy⁻¹ := by rw [h_gx_cy]
        _ = cy * ⁅g x, g y⁆ * cy⁻¹ := by rw [one_mul]
        _ = ⁅g x, g y⁆ := by rw [h_conj_cy]
  have h_eqOn : Set.EqOn f g (⊤ : Subgroup P) := by
    intro x _
    have hx : x ∈ commutator P := Group.IsPerfect.mem_commutator
    have hx' : x ∈ f.eqLocus g := h_comm_le hx
    have hx_eq : f x = g x := by
      change f x = g x at hx'
      exact hx'
    exact hx_eq
  exact MonoidHom.eq_of_eqOn_top h_eqOn

end MonoidHom

end
