/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.Cardinal.LargeCardinal.Measurable
public import Mathlib.Order.Filter.CardinalInter
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

open Set Cardinal Filter

namespace MathlibExtTest.SetTheory.Cardinal.LargeCardinal.Measurable

open MetaMathlibExt

-- Logic 50: Measurable cardinal

theorem _root_.MetaMathlibExt.IsMeasurable.isRegular.{u} {κ : Cardinal.{u}} (h : IsMeasurable κ) : κ.IsRegular := by
  obtain ⟨hκ, I, hI, U, hcomp, hnp⟩ := h
  haveI := hcomp
  refine ⟨hκ.le, ?_⟩
  rw [← Ordinal.cof_toType, Order.le_cof_iff]
  intro S hS
  by_contra hlt
  replace hlt : #S < κ := not_le.1 hlt
  obtain ⟨e⟩ : Nonempty (I ≃ κ.ord.ToType) := by
    rw [← Cardinal.eq, hI, Cardinal.mk_ord_toType]
  have hcov : (⋃ a : S, e ⁻¹' Set.Iic (a : κ.ord.ToType)) = Set.univ := by
    have := isCofinal_iff_iUnion_Iic_eq_univ.1 hS
    rw [Set.biUnion_eq_iUnion] at this
    rw [← Set.preimage_iUnion, this, Set.preimage_univ]
  have hsingle : ∀ x : I, ({x} : Set I)ᶜ ∈ (U : Filter I) := fun x =>
    hnp (Filter.mem_cofinite.2 (by simp))
  have hsmall : ∀ T : Set I, #T < κ → T ∉ U := by
    intro T hT hTU
    have hcompl : Tᶜ ∈ (U : Filter I) := by
      have hrw : Tᶜ = ⋂ x, ⋂ _ : x ∈ T, ({x} : Set I)ᶜ := by
        ext y
        simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_singleton_iff]
        exact ⟨fun hy i hi hyi => hy (hyi ▸ hi), fun hy hyT => hy y hyT rfl⟩
      rw [hrw]
      exact (Filter.cardinal_bInter_mem hT).2 fun x _ => hsingle x
    exact (Ultrafilter.compl_mem_iff_notMem.1 hcompl) hTU
  obtain ⟨a, ha⟩ : ∃ a : S, e ⁻¹' Set.Iic (a : κ.ord.ToType) ∈ U := by
    by_contra hcon
    rw [not_exists] at hcon
    have hint : (⋂ a : S, (e ⁻¹' Set.Iic (a : κ.ord.ToType))ᶜ) ∈ (U : Filter I) :=
      (Filter.cardinal_iInter_mem (by simpa using hlt)).2 fun a =>
        Ultrafilter.compl_mem_iff_notMem.2 (hcon a)
    rw [← Set.compl_iUnion, hcov, Set.compl_univ] at hint
    exact U.empty_notMem hint
  refine hsmall _ ?_ ha
  rw [Cardinal.mk_preimage_equiv]
  have hIic : Set.Iic (a : κ.ord.ToType) = Set.Iio (a : κ.ord.ToType) ∪ {(a : κ.ord.ToType)} := by
    ext y; simp [Set.mem_Iic, le_iff_lt_or_eq]
  rw [hIic]
  refine lt_of_le_of_lt (Cardinal.mk_union_le _ _) ?_
  have hIio : #(Set.Iio (a : κ.ord.ToType)) < κ := by
    have h' := Cardinal.mk_Iio_lt (α := κ.ord.ToType) (a : κ.ord.ToType)
      (by rw [Cardinal.mk_ord_toType, Ordinal.type_toType])
    rwa [Cardinal.mk_ord_toType] at h'
  refine Cardinal.add_lt_of_lt hκ.le hIio ?_
  rw [Cardinal.mk_singleton]
  exact one_lt_aleph0.trans hκ

end MathlibExtTest.SetTheory.Cardinal.LargeCardinal.Measurable

end
