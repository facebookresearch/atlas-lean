/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology.lean`
and
`P2M/Sol/S_AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection

@[expose] public section

namespace AddSubgroup

/-- A discrete additive subgroup of a finite-dimensional real normed space
is a lattice in its real span: after a continuous linear identification of
the ambient space with a product of coordinate spaces, the subgroup is
exactly the integral points of the first factor. -/
theorem exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : AddSubgroup V) [DiscreteTopology L] :
    ∃ (a b : ℕ) (T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V),
      ∀ x : V, x ∈ L ↔ ∃ k : Fin a → ℤ, T (fun i => (k i : ℝ), 0) = x := by
  classical
  set L₁ : Submodule ℤ V := AddSubgroup.toIntSubmodule L with hL₁
  haveI : DiscreteTopology L₁ := inferInstanceAs (DiscreteTopology L)
  set W : Submodule ℝ V := Submodule.span ℝ (L₁ : Set V) with hW
  set L₂ : Submodule ℤ W := ZLattice.comap ℝ L₁ W.subtype with hL₂
  have hmemL₂ : ∀ x : W, x ∈ L₂ ↔ (x : V) ∈ L := by
    intro x
    rw [hL₂, ← SetLike.mem_coe, ZLattice.coe_comap]
    rfl
  haveI hdisc : DiscreteTopology L₂ :=
    ZLattice.comap_discreteTopology ℝ L₁ (by fun_prop) Subtype.val_injective
  haveI hlat : IsZLattice ℝ L₂ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    apply le_antisymm
    · exact Submodule.span_le.mpr (by
        rintro _ ⟨x, hx, rfl⟩
        exact Submodule.subset_span ((hmemL₂ x).mp hx))
    · have hsub : (L₁ : Set V) ⊆ ⇑W.subtype '' (L₂ : Set W) := by
        intro v hv
        have hvW : v ∈ W := Submodule.subset_span hv
        exact ⟨⟨v, hvW⟩, (hmemL₂ _).mpr hv, rfl⟩
      intro v hv
      exact Submodule.span_mono hsub hv
  haveI : Module.Free ℤ L₂ := ZLattice.module_free ℝ L₂
  haveI : Module.Finite ℤ L₂ := ZLattice.module_finite ℝ L₂
  set a : ℕ := Module.finrank ℤ L₂ with ha
  set bZ : Module.Basis (Fin a) ℤ L₂ := Module.finBasis ℤ L₂ with hbZ
  set BW : Module.Basis (Fin a) ℝ W := Module.Basis.ofZLatticeBasis ℝ L₂ bZ with hBW
  have hBW : ∀ i, BW i = (bZ i : W) :=
    fun i => Module.Basis.ofZLatticeBasis_apply ℝ L₂ bZ i
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  set b : ℕ := Module.finrank ℝ W' with hb
  set BW' : Module.Basis (Fin b) ℝ W' := Module.finBasis ℝ W' with hBW'
  set e₁ : ((Fin a → ℝ) × (Fin b → ℝ)) ≃ₗ[ℝ] (W × W') :=
    LinearEquiv.prodCongr BW.equivFun.symm BW'.equivFun.symm with he₁
  set e₂ : (W × W') ≃ₗ[ℝ] V := Submodule.prodEquivOfIsCompl W W' hWW' with he₂
  set T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V :=
    (e₁.trans e₂).toContinuousLinearEquiv with hT
  have hTapply : ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      T (w, z) = ((BW.equivFun.symm w : W) : V) +
        ((BW'.equivFun.symm z : W') : V) := by
    intro w z
    rfl
  have hT0 : ∀ k : Fin a → ℤ,
      T ((fun i => (k i : ℝ)), 0) = ∑ i, (k i) • ((bZ i : W) : V) := by
    intro k
    rw [hTapply, map_zero, ZeroMemClass.coe_zero, add_zero,
      Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, hBW, Int.cast_smul_eq_zsmul]
  refine ⟨a, b, T, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have hxW : x ∈ W := Submodule.subset_span (show x ∈ L₁ from hx)
    have hxL₂ : (⟨x, hxW⟩ : W) ∈ L₂ := (hmemL₂ _).mpr hx
    set k : Fin a → ℤ := bZ.equivFun ⟨⟨x, hxW⟩, hxL₂⟩ with hk
    refine ⟨k, ?_⟩
    rw [hT0]
    have h := bZ.sum_equivFun ⟨⟨x, hxW⟩, hxL₂⟩
    have h' := congrArg (fun z : L₂ => ((z : W) : V)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h'
    exact h'
  · rintro ⟨k, rfl⟩
    rw [hT0]
    refine L.sum_mem fun i _ => L.zsmul_mem ?_ _
    exact (hmemL₂ _).mp (bZ i).2

end AddSubgroup
