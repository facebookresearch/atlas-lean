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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatExtension

/-! # Extension second-component commutation

Minimal bridge from the paired extension to commutation of its permutation
component. The second projection is a homomorphism; its image centralizes the
right action, and the central permutations commute with it.
-/

@[expose] public section

universe u

open Matrix

namespace MatsumotoTitsBruhatFiber

section LeftExtensionCommutation

variable (F : Type u) [Field F] (n : ℕ)

open Matrix.GeneralLinearGroup

/-- Second-component projection of the paired left extension. -/
def leftExtensionSndHom :
    leftExtensionSubgroup F n →* Equiv.Perm (X F n) where
  toFun p := p.val.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem leftExtensionSndHom_apply
    (p : leftExtensionSubgroup F n) :
    leftExtensionSndHom F n p = p.val.2 :=
  rfl

theorem leftExtensionSndHom_coe
    (p : leftExtensionSubgroup F n) :
    (p.val.2 : Equiv.Perm (X F n)) = leftExtensionSndHom F n p :=
  rfl

theorem leftExtensionPairGenerators_le_comap_centralizer_rightActionSubgroup :
    leftExtensionPairGenerators F n ≤
      (Subgroup.comap
        (MonoidHom.snd
          (Matrix.SpecialLinearGroup (Fin n) F)
          (Equiv.Perm (X F n)))
        (Subgroup.centralizer
          (rightActionSubgroup F n :
            Set (Equiv.Perm (X F n)))) : Set _) := by
  intro p hp
  apply Subgroup.mem_comap.mpr
  -- `MonoidHom.snd p = p.2` definitionally
  rcases hp with h12 | ⟨c, rfl⟩
  · rcases h12 with ⟨u, rfl⟩ | ⟨i, j, hij, rfl⟩
    · have hMemLeft :
          leftUpperPerm (F := F) (n := n) u ∈ leftActionSubgroup F n :=
        leftUpperPerm_mem_leftActionSubgroup F u
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (leftActionSubgroup_rightActionSubgroup_comm (F := F) hMemLeft hg).symm
    · have hMemLeft :
          leftWeylPerm (F := F) hij ∈ leftActionSubgroup F n :=
        leftWeylPerm_mem_leftActionSubgroup F hij
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (leftActionSubgroup_rightActionSubgroup_comm (F := F) hMemLeft hg).symm
  · exact centralActionSubgroup_le_centralizer_rightActionSubgroup F n
      (centralPerm_mem_centralActionSubgroup F c)

/-- Paired extension second component lies in the centralizer of the right
action subgroup. -/
theorem leftExtension_snd_mem_centralizer_rightActionSubgroup
    (p : leftExtensionSubgroup F n) :
    (p.val.2 : Equiv.Perm (X F n)) ∈
      Subgroup.centralizer
        (rightActionSubgroup F n : Set (Equiv.Perm (X F n))) := by
  have hLe : leftExtensionSubgroup F n ≤
      Subgroup.comap
        (MonoidHom.snd
          (Matrix.SpecialLinearGroup (Fin n) F)
          (Equiv.Perm (X F n)))
        (Subgroup.centralizer
          (rightActionSubgroup F n : Set (Equiv.Perm (X F n)))) := by
    apply (Subgroup.closure_le (K :=
      Subgroup.comap
        (MonoidHom.snd
          (Matrix.SpecialLinearGroup (Fin n) F)
          (Equiv.Perm (X F n)))
        (Subgroup.centralizer
          (rightActionSubgroup F n :
            Set (Equiv.Perm (X F n)))))).mpr
    exact leftExtensionPairGenerators_le_comap_centralizer_rightActionSubgroup F n
  have hMem : p.val ∈
      Subgroup.comap
        (MonoidHom.snd
          (Matrix.SpecialLinearGroup (Fin n) F)
          (Equiv.Perm (X F n)))
        (Subgroup.centralizer
          (rightActionSubgroup F n : Set (Equiv.Perm (X F n)))) :=
    hLe p.prop
  rw [Subgroup.mem_comap] at hMem
  -- `MonoidHom.snd p.val = p.val.2` definitionally
  simpa using hMem

theorem leftExtension_snd_commutes_rightAction
    (p : leftExtensionSubgroup F n) (g : Equiv.Perm (X F n))
    (hg : g ∈ rightActionSubgroup F n) :
    Commute p.val.2 g := by
  have hCent := leftExtension_snd_mem_centralizer_rightActionSubgroup F n p
  have hComm : Commute g p.val.2 :=
    (Subgroup.mem_centralizer_iff.mp hCent) g hg
  exact hComm.symm

theorem leftExtension_snd_commutes_central
    (p : leftExtensionSubgroup F n)
    (c : Multiplicative (MilnorK F 2)) :
    Commute p.val.2 (centralPerm (F := F) (n := n) c) := by
  have hCenterMem : centralPairHom (F := F) (n := n) c ∈
      Subgroup.center (leftExtensionSubgroup F n) :=
    centralPairHom_range_le_center (F := F) (n := n)
      (MonoidHom.mem_range.mpr ⟨c, rfl⟩)
  have hEq : p * centralPairHom F n c = centralPairHom F n c * p :=
    Subgroup.mem_center_iff.mp hCenterMem p
  have hValEq : p.val * (centralPairHom F n c).val =
      (centralPairHom F n c).val * p.val :=
    congrArg Subtype.val hEq
  have hValEq' : p.val * ((1 : Matrix.SpecialLinearGroup (Fin n) F),
        centralPerm (F := F) (n := n) c) =
      ((1 : Matrix.SpecialLinearGroup (Fin n) F),
        centralPerm (F := F) (n := n) c) * p.val := by
    simpa [centralPairHom_val] using hValEq
  have hSndEq : p.val.2 * centralPerm (F := F) (n := n) c =
      centralPerm (F := F) (n := n) c * p.val.2 :=
    congrArg Prod.snd hValEq'
  exact hSndEq

end LeftExtensionCommutation

end MatsumotoTitsBruhatFiber

end
