/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean`,
`P2M/Sol/S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.lean`,
`Theorems/Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField.lean`
and
`P2M/Sol/S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import MathlibExt.AlgebraicGeometry.Curve.GluedChartsAffine
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.SeparablyGenerated

/-!
# Existence of curve models

Let `K` be an infinite perfect field and `L / K` a field extension containing an element `x`,
transcendental over `K`, with `L` finite over `K(x)`. Then `L / K` has a curve model
(`AlgebraicCurve.CurveModel.nonempty_of_perfectField`): a smooth proper integral curve over `K`
with function field `L`, whose closed points correspond to the places of `L / K`, the local ring
at each closed point being the valuation ring of its place, and in which every finite set of
points lies in an affine open.

Since `K` is perfect, `L` has a separating transcendence basis `{t}` over `K`, and the curve model
is the two-chart scheme `AlgebraicCurve.CurveModel.glued K t`
(`AlgebraicCurve.CurveModel.ofGenerator`).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry IntermediateField

universe u v

namespace AlgebraicCurve

namespace CurveModel

section Generator

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

theorem adjoin_inv_eq_adjoin (t : L) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  refine le_antisymm ?_ ?_
  · exact adjoin_simple_le_iff.mpr (inv_mem (mem_adjoin_simple_self K t))
  · refine adjoin_simple_le_iff.mpr ?_
    have h : t = (t⁻¹)⁻¹ := (inv_inv t).symm
    rw [h]
    exact inv_mem (by rw [← h]; exact mem_adjoin_simple_self K t⁻¹)

theorem finiteDimensional_adjoin_inv (t : L) [FiniteDimensional K⟮t⟯ L] :
    FiniteDimensional K⟮t⁻¹⟯ L := by
  rw [adjoin_inv_eq_adjoin K t]; infer_instance

theorem isSeparable_adjoin_inv (t : L) [Algebra.IsSeparable K⟮t⟯ L] :
    Algebra.IsSeparable K⟮t⁻¹⟯ L := by
  rw [adjoin_inv_eq_adjoin K t]; infer_instance

/-- The curve model `glued K t` of `L / K`, for an infinite perfect field `K` and an element `t`
transcendental over `K` such that `L` is finite and separable over `K(t)`. -/
def ofGenerator [PerfectField K] [Infinite K] (t : L) [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [Algebra.IsSeparable K⟮t⟯ L] (ht : Transcendental K t) : CurveModel K L :=
  haveI := finiteDimensional_adjoin_inv K t
  haveI := isSeparable_adjoin_inv K t
  haveI := smoothOfRelativeDimension_one_gluedToBase K t ht
  { C := glued K t
    toBase := gluedToBase K t
    ffEquiv := gluedFunctionFieldEquiv K t
    ffEquiv_algebraMap := gluedFunctionFieldEquiv_algebraMap K t
    placeOfPoint := gluedPlaceOfPoint K t ht
    placeOfPoint_bijective := gluedPlaceOfPoint_bijective K t ht
    range_stalk_eq := range_stalk_eq_gluedPlaceOfPoint K t ht
    finset_subset_affineOpen := finset_subset_affineOpen_glued K t }

end Generator

section Separating

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

private theorem essFiniteType_of_hfg
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L) :
    Algebra.EssFiniteType K L := by
  obtain ⟨x, -, hfin⟩ := hfg
  have : Algebra.EssFiniteType K K⟮x⟯ :=
    IntermediateField.essFiniteType_iff.mpr ⟨{x}, by simp⟩
  have : Algebra.EssFiniteType K⟮x⟯ L := inferInstance
  exact Algebra.EssFiniteType.comp K K⟮x⟯ L

open scoped _root_.IntermediateField.algebraAdjoinAdjoin in
private theorem isTranscendenceBasis_of_hfg {x : L} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ L] : IsTranscendenceBasis K ![x] := by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2
    ⟨algebraicIndependent_iff_transcendental.2 hx, ?_⟩
  have hr : Set.range ![x] = {x} := by
    ext y; simp
  rw [hr]
  have : Algebra.IsAlgebraic K⟮x⟯ L := Algebra.IsAlgebraic.of_finite K⟮x⟯ L
  exact Algebra.IsAlgebraic.trans (Algebra.adjoin K ({x} : Set L)) K⟮x⟯ L

end Separating

private theorem nonempty_same_universe (K : Type u) [Field K] [PerfectField K] [Infinite K]
    (L : Type u) [Field L] [Algebra K L]
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L) :
    Nonempty (CurveModel K L) := by
  have hess := essFiniteType_of_hfg hfg
  obtain ⟨x, hx, hfin⟩ := hfg
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have hxb : IsTranscendenceBasis K ![x] := isTranscendenceBasis_of_hfg hx
  have hcard : s.card = 1 := by
    have h := hxb.lift_cardinalMk_eq hs
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype, Fintype.card_fin, Fintype.card_coe] at h
    norm_num at h
    exact_mod_cast h.symm
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  have ht : Transcendental K t := hs.1.transcendental ⟨t, Finset.mem_singleton_self t⟩
  have : Fact (t ≠ 0) := ⟨fun h0 => ht (h0 ▸ isAlgebraic_zero)⟩
  have hcoe : ((({t} : Finset L) : Set L)) = {t} := Finset.coe_singleton t
  have hsep' : Algebra.IsSeparable K⟮t⟯ L := by
    rw [hcoe] at hsep
    exact hsep
  have : Algebra.IsAlgebraic K⟮t⟯ L := by
    have h := hs.isAlgebraic_field
    have hr : Set.range ((↑) : (({t} : Finset L)) → L) = {t} := by
      ext y; simp
    rw [hr] at h
    exact h
  have : Algebra.EssFiniteType K⟮t⟯ L := Algebra.EssFiniteType.of_comp K K⟮t⟯ L
  have : FiniteDimensional K⟮t⟯ L := Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact ⟨ofGenerator K t ht⟩

private theorem small_of_hfg {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L) : Small.{u} L := by
  obtain ⟨x, hx, hfin⟩ := hfg
  have e1 : K⟮x⟯ ≃ₐ[K] RatFunc K := (RatFunc.algEquivOfTranscendental x hx).symm
  have : Small.{u} K⟮x⟯ := small_of_injective e1.injective
  let b := Module.finBasis K⟮x⟯ L
  exact small_of_injective b.equivFun.injective

private theorem transcendental_algEquiv {K : Type u} [Field K] {L L' : Type*} [Field L] [Field L']
    [Algebra K L] [Algebra K L'] (e : L' ≃ₐ[K] L) {x : L} (hx : Transcendental K x) :
    Transcendental K (e.symm x) := by
  intro halg
  apply hx
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h := congrArg e hp
  rw [Polynomial.aeval_algHom_apply, map_zero, e.apply_symm_apply] at h
  exact h

private theorem finiteDimensional_algEquiv {K : Type u} [Field K] {L L' : Type*} [Field L]
    [Field L'] [Algebra K L] [Algebra K L'] (e : L' ≃ₐ[K] L) (x : L)
    [FiniteDimensional K⟮x⟯ L] : FiniteDimensional K⟮e.symm x⟯ L' := by
  have hmap : (K⟮x⟯).map (e.symm : L →ₐ[K] L') = K⟮e.symm x⟯ := by
    rw [adjoin_map]
    simp
  let e₁ : K⟮x⟯ ≃+* K⟮e.symm x⟯ :=
    (((K⟮x⟯).equivMap (e.symm : L →ₐ[K] L')).trans (equivOfEq hmap)).toRingEquiv
  exact Module.Finite.of_equiv_equiv e₁ (e.symm : L ≃ₐ[K] L').toRingEquiv (by ext y; rfl)

/-- A field extension `L / K` of an infinite perfect field that is finite over `K(x)` for some
`x ∈ L` transcendental over `K` has a curve model: a smooth proper integral curve over `K` with
function field `L`, whose closed points correspond to the places of `L / K`, the local ring at
each closed point being the valuation ring of its place, and in which every finite set of points
lies in an affine open. -/
theorem nonempty_of_perfectField (K : Type u) (L : Type v) [Field K] [PerfectField K]
    [Infinite K] [Field L] [Algebra K L]
    (hfg : ∃ x : L, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L) :
    Nonempty (CurveModel K L) := by
  have := small_of_hfg hfg
  let e : Shrink.{u} L ≃ₐ[K] L := Shrink.algEquiv K L
  have hfg' : ∃ x : Shrink.{u} L,
      Transcendental K x ∧ FiniteDimensional K⟮x⟯ (Shrink.{u} L) := by
    obtain ⟨x, hx, hfin⟩ := hfg
    exact ⟨e.symm x, transcendental_algEquiv e hx, finiteDimensional_algEquiv e x⟩
  obtain ⟨M⟩ := nonempty_same_universe K (Shrink.{u} L) hfg'
  exact ⟨congr e M⟩

end CurveModel

end AlgebraicCurve
