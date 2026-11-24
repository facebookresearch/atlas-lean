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

public import MathlibExt.KTheory.Ring.K2.MatsumotoStableExtensionDiagram
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatExtension
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatKernelEquality
public import MathlibExt.KTheory.Ring.StableElementary.Basic
public import MathlibExt.KTheory.Ring.StableElementary.Inclusions
public import MathlibExt.GroupTheory.CentralExtension
public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Stable central extensions for Matsumoto symbols
-/

@[expose] public section

open CategoryTheory Limits
open Matrix.GeneralLinearGroup
open MatsumotoTitsBruhatFiber
open MatsumotoStableExtensionDiagram
open AlgebraicKTheory

universe u

noncomputable section

namespace MatsumotoStableExtensionDiagram

variable (F : Type u) [Field F]

/-! ### Finite-stage representation -/

theorem stableExtension_exists_rep (x : StableExtensionGroup F) :
    ∃ (k : ℕ) (p : leftExtensionSubgroup F (k + 2)),
      (stableExtensionIncl F k).hom p = x := by
  have hsurj :=
    Functor.ιColimitType_jointly_surjective
      (F := leftExtensionDiagram F ⋙ forget GrpCat.{u}) x
  obtain ⟨k, p, hp⟩ := hsurj
  exact ⟨k, p, hp⟩

/-! ### Surjectivity of the stable projection -/

private theorem two_le_of_ne_fin {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    2 ≤ n := by
  by_contra h
  have hn_lt2 : n < 2 := Nat.lt_of_not_ge h
  interval_cases n
  · have hi : (i : Fin 0).val < 0 := i.isLt
    omega
  · have hi_val : i.val = 0 := by omega
    have hj_val : j.val = 0 := by omega
    have hij_val : i.val = j.val := by rw [hi_val, hj_val]
    exact hij (Fin.eq_of_val_eq hij_val)

theorem stableProjection_surjective :
    Function.Surjective (stableProjection (F := F)).hom := by
  rw [← MonoidHom.range_eq_top]
  have h_top :
      Subgroup.closure
          ((stableElementarySubgroup (R := F)).subtype ⁻¹'
            stableElementarySet (R := F)) = ⊤ :=
    Subgroup.closure_preimage_eq_top (stableElementarySet (R := F))
  have h_le :
      Subgroup.closure
          ((stableElementarySubgroup (R := F)).subtype ⁻¹'
            stableElementarySet (R := F)) ≤
        MonoidHom.range (stableProjection (F := F)).hom := by
    rw [Subgroup.closure_le]
    intro y hy
    have h_mem : (y : StableGL F) ∈ stableElementarySet (R := F) := hy
    obtain ⟨n, i, j, hij, a, h_eq⟩ := h_mem
    have h2 : 2 ≤ n := two_le_of_ne_fin hij
    obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    subst hk
    have h_y_eq : y = StableE.elementary (R := F) (k + 2) i j hij a := by
      apply Subtype.ext
      simp only [StableE.coe_elementary]
      exact h_eq
    let e : Matrix.GeneralLinearGroup.elementarySubgroup (Fin (k + 2)) F :=
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary i j hij a
    have h_from : StableE.fromFinite F (k + 2) e = y := by
      have h_elem : StableE.fromFinite F (k + 2) e =
          StableE.elementary (R := F) (k + 2) i j hij a := rfl
      rw [h_elem, h_y_eq]
    obtain ⟨g, hg⟩ :=
      MatsumotoTitsBruhatFiber.slToElementaryHom_surjective (R := F) (k + 2) e
    have h_surj := leftExtensionProjHom_surjective (F := F) (n := k + 2) (by omega)
    obtain ⟨p, hp⟩ := h_surj g
    have h_stage : leftExtensionStageProj F k p = y := by
      simp only [leftExtensionStageProj, MonoidHom.comp_apply]
      rw [hp, hg, h_from]
    have h_incl : (stableProjection F).hom ((stableExtensionIncl F k).hom p) =
        leftExtensionStageProj F k p :=
      stableProjection_ι F k p
    rw [h_stage] at h_incl
    exact MonoidHom.mem_range.mpr ⟨(stableExtensionIncl F k).hom p, h_incl⟩
  have h_top_le : (⊤ : Subgroup (StableE F)) ≤ MonoidHom.range (stableProjection (F := F)).hom :=
    h_top ▸ h_le
  exact le_antisymm le_top h_top_le

/-! ### Kernel equality -/

theorem stableProjection_ker_eq_central_range :
    (stableProjection (F := F)).hom.ker = (stableCentralHom F).range := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨k, p, hp⟩ := stableExtension_exists_rep F x
    have h_proj : leftExtensionStageProj F k p = 1 := by
      have h_ι := stableProjection_ι (F := F) k p
      have h_eq : (stableProjection F).hom ((stableExtensionIncl F k).hom p) =
          leftExtensionStageProj F k p := h_ι
      have h_x : (stableProjection F).hom x = 1 := hx
      rw [← hp] at h_x
      rw [h_eq] at h_x
      exact h_x
    have h_from :
        StableE.fromFinite F (k + 2)
            (MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
              (MatsumotoTitsBruhatFiber.leftExtensionProjHom F (k + 2) p)) = 1 := by
      simpa [leftExtensionStageProj] using h_proj
    have h_from_one :
        StableE.fromFinite F (k + 2)
            (1 : Matrix.GeneralLinearGroup.elementarySubgroup (Fin (k + 2)) F) = 1 := by
      simp
    have h_eq_from :
        StableE.fromFinite F (k + 2)
            (MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
              (MatsumotoTitsBruhatFiber.leftExtensionProjHom F (k + 2) p)) =
          StableE.fromFinite F (k + 2) 1 := by
      rw [h_from, h_from_one]
    have h_sl :
        MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
            (MatsumotoTitsBruhatFiber.leftExtensionProjHom F (k + 2) p) = 1 :=
      StableE.fromFinite_injective (R := F) (k + 2) h_eq_from
    have h_sl_one :
        MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
            (1 : Matrix.SpecialLinearGroup (Fin (k + 2)) F) = 1 := by
      simp
    have h_eq_sl :
        MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
            (MatsumotoTitsBruhatFiber.leftExtensionProjHom F (k + 2) p) =
          MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2) 1 := by
      rw [h_sl, h_sl_one]
    have h_left :
        MatsumotoTitsBruhatFiber.leftExtensionProjHom F (k + 2) p = 1 :=
      MatsumotoTitsBruhatFiber.slToElementaryHom_injective (R := F) (k + 2) h_eq_sl
    have h_mem_ker :
        p ∈ (MatsumotoTitsBruhatFiber.leftExtensionProjHom F (k + 2)).ker := by
      rw [MonoidHom.mem_ker, h_left]
    have h_ker_eq :=
      leftExtensionProjHom_ker_eq_centralPairHom_range (F := F) (n := k + 2) (by omega)
    have h_mem_range : p ∈ (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2)).range := by
      rw [← h_ker_eq]
      exact h_mem_ker
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h_mem_range
    have h_p_eq : p = MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c := by
      -- hc : centralPairHom c = p
      exact hc.symm ▸ rfl
    have h_incl : (stableExtensionIncl F k).hom p = stableCentralHom F c := by
      rw [h_p_eq]
      exact stableExtensionIncl_central F k c
    rw [← hp, h_incl]
    exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
  · intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [MonoidHom.mem_ker]
    exact stableProjection_central F c

/-! ### Centrality -/

theorem stableCentralHom_range_le_center :
    (stableCentralHom (F := F)).range ≤ Subgroup.center (StableExtensionGroup F) := by
  intro y hy
  rw [MonoidHom.mem_range] at hy
  obtain ⟨c, rfl⟩ := hy
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨k, p, hp⟩ := stableExtension_exists_rep F z
  have h_central : stableCentralHom F c =
      (stableExtensionIncl F k).hom
          (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) :=
    (stableExtensionIncl_central F k c).symm
  have h_z : z = (stableExtensionIncl F k).hom p := hp.symm
  have h_fin_mem :
      MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c ∈
        (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2)).range :=
    MonoidHom.mem_range.mpr ⟨c, rfl⟩
  have h_fin_center :
      MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c ∈
        Subgroup.center (leftExtensionSubgroup F (k + 2)) :=
    centralPairHom_range_le_center (F := F) (n := k + 2) h_fin_mem
  have h_fin_comm :
      Commute (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) p := by
    have h := (Subgroup.mem_center_iff.mp h_fin_center) p
    rw [Commute, SemiconjBy]
    exact h.symm
  have h_eq_fin :
      MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c * p =
        p * MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c :=
    h_fin_comm.eq
  let f : leftExtensionSubgroup F (k + 2) →* StableExtensionGroup F := by
    change ↑((leftExtensionDiagram F).obj k) →* StableExtensionGroup F
    exact (stableExtensionIncl F k).hom
  have h_comm_stable :
      f (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) * f p =
        f p * f (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) := by
    calc f (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) * f p
        = f (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c * p) := by
          rw [← map_mul]
      _ = f (p * MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) := by
          rw [h_eq_fin]
      _ = f p * f (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) := by
          rw [map_mul]
  calc z * stableCentralHom F c
      = f p * f (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) := by
        rw [h_z, h_central]
        rfl
    _ = f (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) * f p := by
        rw [h_comm_stable]
    _ = stableCentralHom F c * z := by
        rw [h_central, h_z]
        rfl

/-! ### Stable Matsumoto extension -/

noncomputable def stableMatsumotoExtension :
    GroupExtension (Multiplicative (MilnorK F 2))
      (StableExtensionGroup F) (StableE F) where
  inl := stableCentralHom F
  rightHom := (stableProjection F).hom
  inl_injective := stableCentralHom_injective (F := F)
  range_inl_eq_ker_rightHom := by
    have h := stableProjection_ker_eq_central_range (F := F)
    exact h.symm
  rightHom_surjective := stableProjection_surjective (F := F)

@[simp]
theorem stableMatsumotoExtension_inl (c : Multiplicative (MilnorK F 2)) :
    (stableMatsumotoExtension (F := F)).inl c = stableCentralHom F c :=
  rfl

@[simp]
theorem stableMatsumotoExtension_rightHom (x : StableExtensionGroup F) :
    (stableMatsumotoExtension (F := F)).rightHom x = (stableProjection F).hom x :=
  rfl

theorem stableMatsumotoExtension_isCentral :
    (stableMatsumotoExtension (F := F)).IsCentral := by
  change (stableProjection F).hom.ker ≤ Subgroup.center (StableExtensionGroup F)
  rw [stableProjection_ker_eq_central_range (F := F)]
  exact stableCentralHom_range_le_center (F := F)

@[simp]
theorem stableProjection_stableExtensionIncl (k : ℕ)
    (p : leftExtensionSubgroup F (k + 2)) :
    (stableProjection F).hom ((stableExtensionIncl F k).hom p) =
      leftExtensionStageProj F k p :=
  stableProjection_ι F k p

end MatsumotoStableExtensionDiagram

end
