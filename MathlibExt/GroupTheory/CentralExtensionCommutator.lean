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

public import MathlibExt.GroupTheory.CentralExtension
public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Commutator lifts in central extensions
-/

/-! Central commutator lifts for central group extensions. -/

@[expose] public section

universe u v w

namespace GroupExtension

variable {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]

open scoped commutatorElement

/-- Commutator lift via the chosen section `surjInvRightHom`. -/
noncomputable def liftCommutator (S : GroupExtension N E G) (g h : G) : E :=
  ⁅S.surjInvRightHom g, S.surjInvRightHom h⁆

@[simp]
theorem rightHom_liftCommutator (S : GroupExtension N E G) (g h : G) :
    S.rightHom (S.liftCommutator g h) = ⁅g, h⁆ := by
  simp [liftCommutator, map_commutatorElement]

/-- Central kernel: commutators depend only on `rightHom` images. -/
theorem IsCentral.commutator_eq_of_rightHom_eq {S : GroupExtension N E G}
    (hS : S.IsCentral) {a a' b b' : E}
    (ha : S.rightHom a = S.rightHom a') (hb : S.rightHom b = S.rightHom b') :
    ⁅a, b⁆ = ⁅a', b'⁆ := by
  let cx := a * a'⁻¹
  let cy := b * b'⁻¹
  have hcx_ker : cx ∈ S.rightHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha, mul_inv_cancel]
  have hcy_ker : cy ∈ S.rightHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb, mul_inv_cancel]
  have hcx_center : cx ∈ Subgroup.center E := hS hcx_ker
  have hcy_center : cy ∈ Subgroup.center E := hS hcy_ker
  have hcx_comm : ∀ x : E, Commute cx x := by
    intro x
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp hcx_center x).symm
  have hcy_comm : ∀ x : E, Commute cy x := by
    intro x
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp hcy_center x).symm
  have ha_eq : a = cx * a' := by
    simp [cx]
  have hb_eq : b = cy * b' := by
    simp [cy]
  rw [ha_eq, hb_eq]
  have h_comm_cx : ∀ x : E, ⁅cx, x⁆ = 1 := fun x => (hcx_comm x).commutator_eq
  have h_comm_cy : ∀ x : E, ⁅x, cy⁆ = 1 := fun x => ((hcy_comm x).symm).commutator_eq
  have h_conj_cx : ∀ x : E, cx * x * cx⁻¹ = x := fun x => (hcx_comm x).mul_inv_cancel
  have h_conj_cy : ∀ x : E, cy * x * cy⁻¹ = x := fun x => (hcy_comm x).mul_inv_cancel
  -- central commutator cancellations
  calc ⁅cx * a', cy * b'⁆
      = cx * ⁅a', cy * b'⁆ * cx⁻¹ * ⁅cx, cy * b'⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul]
    _ = cx * ⁅a', cy * b'⁆ * cx⁻¹ * 1 := by rw [h_comm_cx (cy * b')]
    _ = cx * ⁅a', cy * b'⁆ * cx⁻¹ := by rw [mul_one]
    _ = ⁅a', cy * b'⁆ := by rw [h_conj_cx]
    _ = ⁅a', cy⁆ * cy * ⁅a', b'⁆ * cy⁻¹ := by
        rw [commutatorElement_mul_right_eq_mul_conj]
    _ = 1 * cy * ⁅a', b'⁆ * cy⁻¹ := by rw [h_comm_cy a']
    _ = cy * ⁅a', b'⁆ * cy⁻¹ := by rw [one_mul]
    _ = ⁅a', b'⁆ := by rw [h_conj_cy]

/-- Any commutator equals the canonical `liftCommutator` of its projections. -/
theorem IsCentral.liftCommutator_eq {S : GroupExtension N E G}
    (hS : S.IsCentral) {a b : E} {g h : G}
    (ha : S.rightHom a = g) (hb : S.rightHom b = h) :
    ⁅a, b⁆ = S.liftCommutator g h := by
  have ha' : S.rightHom a = S.rightHom (S.surjInvRightHom g) := by
    rw [ha, Section.rightHom_section]
  have hb' : S.rightHom b = S.rightHom (S.surjInvRightHom h) := by
    rw [hb, Section.rightHom_section]
  have h := hS.commutator_eq_of_rightHom_eq ha' hb'
  simp only [liftCommutator] at h ⊢
  exact h

private theorem mem_ker_liftCommutator_of_commute {S : GroupExtension N E G}
    {g h : G} (hComm : Commute g h) :
    S.liftCommutator g h ∈ S.rightHom.ker := by
  rw [MonoidHom.mem_ker, rightHom_liftCommutator, hComm.commutator_eq]

/-- `liftCommutator` is trivial when the left argument is `1`. -/
theorem IsCentral.liftCommutator_one_left {S : GroupExtension N E G}
    (hS : S.IsCentral) (h : G) : S.liftCommutator 1 h = 1 := by
  have hEq : ⁅(1 : E), S.surjInvRightHom h⁆ = S.liftCommutator 1 h :=
    hS.liftCommutator_eq (by simp) (S.surjInvRightHom.rightInverse_rightHom h)
  rw [← hEq, commutatorElement_one_left]

/-- `liftCommutator` is trivial when the right argument is `1`. -/
theorem IsCentral.liftCommutator_one_right {S : GroupExtension N E G}
    (hS : S.IsCentral) (g : G) : S.liftCommutator g 1 = 1 := by
  have hEq : ⁅S.surjInvRightHom g, (1 : E)⁆ = S.liftCommutator g 1 :=
    hS.liftCommutator_eq (S.surjInvRightHom.rightInverse_rightHom g) (by simp)
  rw [← hEq, commutatorElement_one_right]

/-- Multiplicativity of `liftCommutator` in the first argument when the second commutator
    lies over a commuting pair. -/
theorem IsCentral.liftCommutator_mul_left {S : GroupExtension N E G}
    (hS : S.IsCentral) {g₁ g₂ h : G} (h₂ : Commute g₂ h) :
    S.liftCommutator (g₁ * g₂) h = S.liftCommutator g₁ h * S.liftCommutator g₂ h := by
  let a₁ := S.surjInvRightHom g₁
  let a₂ := S.surjInvRightHom g₂
  let b := S.surjInvRightHom h
  have ha : S.rightHom (a₁ * a₂) = g₁ * g₂ := by
    change S.rightHom (S.surjInvRightHom g₁ * S.surjInvRightHom g₂) = g₁ * g₂
    simp [map_mul]
  have hb : S.rightHom b = h :=
    S.surjInvRightHom.rightInverse_rightHom h
  have hLift' : ⁅a₁ * a₂, b⁆ = S.liftCommutator (g₁ * g₂) h :=
    hS.liftCommutator_eq ha hb
  have hLiftEq : S.liftCommutator (g₁ * g₂) h = ⁅a₁ * a₂, b⁆ := hLift'.symm
  have hMem2 : ⁅a₂, b⁆ ∈ S.rightHom.ker :=
    mem_ker_liftCommutator_of_commute h₂
  have hCenter2 : ⁅a₂, b⁆ ∈ Subgroup.center E := hS hMem2
  -- conjugation by `a₁` fixes the central element `⁅a₂, b⁆`
  have hComm_a1_c2 : Commute a₁ ⁅a₂, b⁆ := by
    rw [commute_iff_eq]
    exact Subgroup.mem_center_iff.mp hCenter2 a₁
  have hComm_c1_c2 : Commute ⁅a₁, b⁆ ⁅a₂, b⁆ := by
    rw [commute_iff_eq]
    exact Subgroup.mem_center_iff.mp hCenter2 ⁅a₁, b⁆
  have hConj : a₁ * ⁅a₂, b⁆ * a₁⁻¹ = ⁅a₂, b⁆ := hComm_a1_c2.mul_inv_cancel
  have hExpand : ⁅a₁ * a₂, b⁆ = a₁ * ⁅a₂, b⁆ * a₁⁻¹ * ⁅a₁, b⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul]
  calc S.liftCommutator (g₁ * g₂) h
      = ⁅a₁ * a₂, b⁆ := hLiftEq
    _ = a₁ * ⁅a₂, b⁆ * a₁⁻¹ * ⁅a₁, b⁆ := hExpand
    _ = ⁅a₂, b⁆ * ⁅a₁, b⁆ := by rw [hConj]
    _ = ⁅a₁, b⁆ * ⁅a₂, b⁆ := by rw [hComm_c1_c2.eq]
    _ = S.liftCommutator g₁ h * S.liftCommutator g₂ h := rfl

/-- Multiplicativity of `liftCommutator` in the second argument when the second commutator
    lies over a commuting pair. -/
theorem IsCentral.liftCommutator_mul_right {S : GroupExtension N E G}
    (hS : S.IsCentral) {g h₁ h₂ : G} (hg₂ : Commute g h₂) :
    S.liftCommutator g (h₁ * h₂) = S.liftCommutator g h₁ * S.liftCommutator g h₂ := by
  let a := S.surjInvRightHom g
  let b₁ := S.surjInvRightHom h₁
  let b₂ := S.surjInvRightHom h₂
  have ha : S.rightHom a = g :=
    S.surjInvRightHom.rightInverse_rightHom g
  have hb : S.rightHom (b₁ * b₂) = h₁ * h₂ := by
    change S.rightHom (S.surjInvRightHom h₁ * S.surjInvRightHom h₂) = h₁ * h₂
    simp [map_mul]
  have hLift' : ⁅a, b₁ * b₂⁆ = S.liftCommutator g (h₁ * h₂) :=
    hS.liftCommutator_eq ha hb
  have hLiftEq : S.liftCommutator g (h₁ * h₂) = ⁅a, b₁ * b₂⁆ := hLift'.symm
  have hMem2 : ⁅a, b₂⁆ ∈ S.rightHom.ker :=
    mem_ker_liftCommutator_of_commute hg₂
  have hCenter2 : ⁅a, b₂⁆ ∈ Subgroup.center E := hS hMem2
  have hComm_b1_c2 : Commute b₁ ⁅a, b₂⁆ := by
    rw [commute_iff_eq]
    exact Subgroup.mem_center_iff.mp hCenter2 b₁
  have hConj : b₁ * ⁅a, b₂⁆ * b₁⁻¹ = ⁅a, b₂⁆ := hComm_b1_c2.mul_inv_cancel
  have hExpand : ⁅a, b₁ * b₂⁆ = ⁅a, b₁⁆ * (b₁ * ⁅a, b₂⁆ * b₁⁻¹) := by
    simpa only [mul_assoc] using commutatorElement_mul_right_eq_mul_conj a b₁ b₂
  calc S.liftCommutator g (h₁ * h₂)
      = ⁅a, b₁ * b₂⁆ := hLiftEq
    _ = ⁅a, b₁⁆ * (b₁ * ⁅a, b₂⁆ * b₁⁻¹) := hExpand
    _ = ⁅a, b₁⁆ * ⁅a, b₂⁆ := by rw [hConj]
    _ = S.liftCommutator g h₁ * S.liftCommutator g h₂ := rfl

end GroupExtension

end
