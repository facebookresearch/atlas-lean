/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker`
`.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker`
`.lean`,
`Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced`
`.lean` and
`P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced`
`.lean`
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

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Reduced subschemes cut out by vanishing ideals

The subscheme cut out by the vanishing ideal of a closed subset is
reduced, its ideal sheaf is contained in the kernel of any map from a
reduced scheme landing in the subset, and maps from reduced schemes into
a closed immersion with range containing the image lift uniquely.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

private theorem isRadical_vanishingIdeal_ideal {X : Scheme.{u}} (Z : Closeds X)
    (U : X.affineOpens) : ((vanishingIdeal Z).ideal U).IsRadical := by
  rw [vanishingIdeal_ideal]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- The subscheme cut out by a vanishing ideal is reduced. -/
theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  let I := vanishingIdeal Z
  have h : ∀ U : X.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := by
    intro U
    have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_vanishingIdeal_ideal Z U)
    change IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  haveI : ∀ i : I.subschemeCover.openCover.I₀,
      IsReduced (I.subschemeCover.openCover.X i) := h
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

theorem range_subschemeι_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    Set.range (vanishingIdeal Z).subschemeι = (Z : Set X) := by
  rw [range_subschemeι]
  rfl

private theorem basicOpen_inter_eq_empty_of_mem_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X)
    (U : X.affineOpens) {s : Γ(X, U)} (hs : s ∈ (vanishingIdeal Z).ideal U) :
    (X.basicOpen s : Set X) ∩ Z = ∅ := by
  rw [vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hs
  ext z
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hzZ
  have hzU : z ∈ (U : Set X) := X.basicOpen_le s hz
  rw [← U.2.range_fromSpec] at hzU
  obtain ⟨p, rfl⟩ := hzU
  have hp : s ∈ p.asIdeal := hs p hzZ
  have hp' : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := hz
  rw [U.2.fromSpec_preimage_basicOpen] at hp'
  exact absurd hp ((PrimeSpectrum.mem_basicOpen _ _).mp hp')

/-- The vanishing ideal of a closed subset is contained in the kernel of
any map from a reduced scheme landing in the subset. -/
theorem vanishingIdeal_le_ker {X : Scheme.{u}} {T : Scheme.{u}} [IsReduced T] (Z : Closeds X)
    (f : T ⟶ X) (hf : Set.range f ⊆ Z) : vanishingIdeal Z ≤ f.ker := by
  rw [Scheme.Hom.ker, le_ofIdeals_iff]
  intro U s hs
  rw [RingHom.mem_ker]
  have hb : T.basicOpen ((f.app U).hom s) = ⊥ := by
    rw [← Scheme.preimage_basicOpen]
    ext t
    simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot,
      Set.mem_empty_iff_false, iff_false]
    intro ht
    have hmem : f t ∈ (X.basicOpen s : Set X) ∩ Z := ⟨ht, hf ⟨t, rfl⟩⟩
    rw [basicOpen_inter_eq_empty_of_mem_vanishingIdeal Z U hs] at hmem
    exact hmem
  exact (basicOpen_eq_bot_iff _).mp hb

/-- A map from a reduced scheme landing in a closed subset lifts uniquely
to the subscheme cut out by the vanishing ideal. -/
theorem exists_lift_subschemeι_vanishingIdeal {X : Scheme.{u}} {T : Scheme.{u}} [IsReduced T]
    (Z : Closeds X) (f : T ⟶ X) (hf : Set.range f ⊆ Z) :
    ∃! g : T ⟶ (vanishingIdeal Z).subscheme, g ≫ (vanishingIdeal Z).subschemeι = f := by
  refine ⟨IsClosedImmersion.lift (vanishingIdeal Z).subschemeι f ?_,
    IsClosedImmersion.lift_fac _ _ _, ?_⟩
  · rw [ker_subschemeι]
    exact vanishingIdeal_le_ker Z f hf
  · intro g hg
    rw [← cancel_mono (vanishingIdeal Z).subschemeι, hg, IsClosedImmersion.lift_fac]

/-- The subscheme cut out by a vanishing ideal is reduced, and its ideal
sheaf is contained in the kernel of any map from a reduced scheme landing
in the subset. -/
theorem isReduced_subscheme_vanishingIdeal_and_le_ker {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme ∧
      ∀ {T : Scheme.{u}} [IsReduced T] (f : T ⟶ X), Set.range f ⊆ Z →
        vanishingIdeal Z ≤ f.ker :=
  ⟨isReduced_subscheme_vanishingIdeal Z, fun f hf => vanishingIdeal_le_ker Z f hf⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

/-- A map from a reduced scheme into a closed immersion whose range
contains the image lifts uniquely. -/
theorem IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    {X Y T : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (f : T ⟶ X) [IsReduced T]
    (H : Set.range f.base ⊆ Set.range i.base) :
    ∃! g : T ⟶ Y, g ≫ i = f := by
  have hZ : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hle : i.ker ≤ f.ker := by
    obtain ⟨-, h2⟩ := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      (⟨Set.range i.base, hZ⟩ : Closeds X)
    refine le_trans ?_ (h2 f H)
    have hsupp : i.ker.support = ⟨Set.range i.base, hZ⟩ := by
      ext1
      rw [Scheme.Hom.support_ker]
      exact hZ.closure_eq
    rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.le_radical _
  refine ⟨IsClosedImmersion.lift i f hle, IsClosedImmersion.lift_fac i f hle, fun g hg => ?_⟩
  rw [← cancel_mono i, hg, IsClosedImmersion.lift_fac]

end AlgebraicGeometry
