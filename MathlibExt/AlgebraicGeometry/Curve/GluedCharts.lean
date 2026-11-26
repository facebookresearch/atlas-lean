/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean`
and
`P2M/Sol/S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.lean`
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

public import Mathlib.AlgebraicGeometry.Limits
public import MathlibExt.AlgebraicGeometry.Curve.ChartRingSmooth
public import MathlibExt.AlgebraicGeometry.Curve.CurveModel
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The two-chart model of a one-variable function field

Let `t ∈ L` be nonzero with `L` finite and separable over `K(t)`. Gluing `Spec` of the chart
rings of `{t}` and `{t⁻¹}` along `Spec` of the chart ring of `{t, t⁻¹}` gives an integral scheme
`AlgebraicCurve.CurveModel.glued K t` with a morphism `AlgebraicCurve.CurveModel.gluedToBase K t`
to `Spec K`. This file identifies its function field with `L`
(`AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv`), proves that it is smooth of relative
dimension one over `Spec K` when `K` is perfect and `t` is transcendental
(`AlgebraicCurve.CurveModel.smoothOfRelativeDimension_one_gluedToBase`), and, for transcendental
`t`, that its closed points correspond bijectively to the places of `L / K`
(`AlgebraicCurve.CurveModel.gluedPlaceOfPoint`), the local ring at a closed point being the
valuation ring of its place.

Properness is proved in `MathlibExt.AlgebraicGeometry.Curve.GluedChartsProper`, and affine
opens through finite sets of points in `MathlibExt.AlgebraicGeometry.Curve.GluedChartsAffine`.
-/

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField IsDedekindDomain
open Topology TopCat

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)

section Charts

theorem singleton_subset_pair : ({t} : Set L) ⊆ {t, t⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

theorem singleton_inv_subset_pair : ({t⁻¹} : Set L) ⊆ {t, t⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The inclusion of the chart ring of `{t}` into that of `{t, t⁻¹}`. -/
abbrev incl₀ : chartRing K ({t} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L) :=
  chartIncl K (singleton_subset_pair t)

/-- The inclusion of the chart ring of `{t⁻¹}` into that of `{t, t⁻¹}`. -/
abbrev inclInf : chartRing K ({t⁻¹} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L) :=
  chartIncl K (singleton_inv_subset_pair t)

/-- The element `t` of the chart ring of `{t}`. -/
def tChart : chartRing K ({t} : Set L) := ⟨t, subset_chartRing K {t} (Set.mem_singleton t)⟩

/-- The element `t⁻¹` of the chart ring of `{t⁻¹}`. -/
def tInvChart : chartRing K ({t⁻¹} : Set L) :=
  ⟨t⁻¹, subset_chartRing K {t⁻¹} (Set.mem_singleton t⁻¹)⟩

@[simp] theorem coe_tChart : (tChart K t : L) = t := rfl

@[simp] theorem coe_tInvChart : (tInvChart K t : L) = t⁻¹ := rfl

private theorem isUnit_incl₀_tChart (ht : t ≠ 0) : IsUnit (incl₀ K t (tChart K t)) := by
  refine IsUnit.of_mul_eq_one ⟨t⁻¹, subset_chartRing K {t, t⁻¹} (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_tChart]
  exact mul_inv_cancel₀ ht

private theorem isUnit_inclInf_tInvChart (ht : t ≠ 0) : IsUnit (inclInf K t (tInvChart K t)) := by
  refine IsUnit.of_mul_eq_one ⟨t, subset_chartRing K {t, t⁻¹} (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_tInvChart]
  exact inv_mul_cancel₀ ht

theorem isLocalization_away_incl₀ (ht : t ≠ 0) :
    letI := (incl₀ K t).toRingHom.toAlgebra
    IsLocalization.Away (tChart K t) (chartRing K ({t, t⁻¹} : Set L)) := by
  let := (incl₀ K t).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_incl₀_tChart K t ht).pow n
  · intro z
    have hz : (z : L) ∈ chartRing K (insert t⁻¹ ({t} : Set L)) := by
      rw [show insert t⁻¹ ({t} : Set L) = {t, t⁻¹} from Set.pair_comm _ _]
      exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing (K := K) (Set.mem_singleton t) ht hz
    refine ⟨(⟨t ^ n * z, hn⟩, ⟨tChart K t ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_tChart]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective K _ h]

private theorem isLocalization_away_inclInf (ht : t ≠ 0) :
    letI := (inclInf K t).toRingHom.toAlgebra
    IsLocalization.Away (tInvChart K t) (chartRing K ({t, t⁻¹} : Set L)) := by
  let := (inclInf K t).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclInf_tInvChart K t ht).pow n
  · intro z
    have hz : (z : L) ∈ chartRing K (insert t⁻¹⁻¹ ({t⁻¹} : Set L)) := by
      rw [inv_inv]
      exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing (K := K) (Set.mem_singleton t⁻¹)
      (inv_ne_zero ht) hz
    refine ⟨(⟨t⁻¹ ^ n * z, hn⟩, ⟨tInvChart K t ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_tInvChart]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective K _ h]

/-- The chart `Spec` of the chart ring of `{t}`. -/
abbrev X₀ : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t} : Set L)))

/-- The chart `Spec` of the chart ring of `{t⁻¹}`. -/
abbrev XInf : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t⁻¹} : Set L)))

/-- The overlap `Spec` of the chart ring of `{t, t⁻¹}`. -/
abbrev XOverlap : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

/-- The open immersion of the overlap into the chart of `{t}`. -/
abbrev f₀ : XOverlap K t ⟶ X₀ K t := Spec.map (CommRingCat.ofHom (incl₀ K t).toRingHom)

/-- The open immersion of the overlap into the chart of `{t⁻¹}`. -/
abbrev fInf : XOverlap K t ⟶ XInf K t := Spec.map (CommRingCat.ofHom (inclInf K t).toRingHom)

variable [Fact (t ≠ 0)]

instance isOpenImmersion_f₀ : IsOpenImmersion (f₀ K t) := by
  let := (incl₀ K t).toRingHom.toAlgebra
  have := isLocalization_away_incl₀ K t (Fact.out)
  exact IsOpenImmersion.of_isLocalization (tChart K t)

instance isOpenImmersion_fInf : IsOpenImmersion (fInf K t) := by
  let := (inclInf K t).toRingHom.toAlgebra
  have := isLocalization_away_inclInf K t (Fact.out)
  exact IsOpenImmersion.of_isLocalization (tInvChart K t)

end Charts

section Glue

variable [Fact (t ≠ 0)]

/-- For nonzero `t`, the scheme glued from the charts of `{t}` and `{t⁻¹}` along their overlap. -/
def glued : Scheme.{u} := pushout (f₀ K t) (fInf K t)

/-- The inclusion of the chart of `{t}` into the glued scheme. -/
def ι₀ : X₀ K t ⟶ glued K t := pushout.inl (f₀ K t) (fInf K t)

/-- The inclusion of the chart of `{t⁻¹}` into the glued scheme. -/
def ιInf : XInf K t ⟶ glued K t := pushout.inr (f₀ K t) (fInf K t)

@[reassoc]
theorem glue_condition : f₀ K t ≫ ι₀ K t = fInf K t ≫ ιInf K t := pushout.condition

instance isOpenImmersion_ι₀ : IsOpenImmersion (ι₀ K t) :=
  (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).map_prop WalkingSpan.left

instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf K t) :=
  (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).map_prop WalkingSpan.right

omit [Fact (t ≠ 0)] in
theorem f₀_toBase_eq_fInf_toBase :
    f₀ K t ≫ Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L)))) =
      fInf K t ≫ Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))) := by
  have h : (incl₀ K t).toRingHom.comp (algebraMap K (chartRing K ({t} : Set L))) =
      (inclInf K t).toRingHom.comp (algebraMap K (chartRing K ({t⁻¹} : Set L))) :=
    RingHom.ext fun a => ((incl₀ K t).commutes a).trans ((inclInf K t).commutes a).symm
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The structure morphism of the glued scheme to `Spec K`. -/
def gluedToBase : glued K t ⟶ Spec (CommRingCat.of K) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L)))))
    (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))))
    (f₀_toBase_eq_fInf_toBase K t)

@[reassoc (attr := simp)]
theorem ι₀_gluedToBase : ι₀ K t ≫ gluedToBase K t =
    Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L)))) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem ιInf_gluedToBase : ιInf K t ≫ gluedToBase K t =
    Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))) :=
  pushout.inr_desc _ _ _

private theorem smoothOfRelativeDimension_one_gluedToBase_of_charts
    (h₀ : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L))))))
    (hInf : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))))) :
    SmoothOfRelativeDimension 1 (gluedToBase K t) := by
  have h₀' : SmoothOfRelativeDimension 1 (ι₀ K t ≫ gluedToBase K t) := by
    rwa [ι₀_gluedToBase]
  have hInf' : SmoothOfRelativeDimension 1 (ιInf K t ≫ gluedToBase K t) := by
    rwa [ιInf_gluedToBase]
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))) ?_
  rintro (_ | _ | _)
  · have key : (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).f none ≫
        gluedToBase K t = f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t) := by
      change colimit.ι (span (f₀ K t) (fInf K t)) none ≫ gluedToBase K t = _
      rw [← colimit.w (span (f₀ K t) (fInf K t)) WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    have := h₀'
    exact inferInstanceAs
      (SmoothOfRelativeDimension (0 + 1) (f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t)))
  · change SmoothOfRelativeDimension 1 (ι₀ K t ≫ gluedToBase K t)
    exact h₀'
  · change SmoothOfRelativeDimension 1 (ιInf K t ≫ gluedToBase K t)
    exact hInf'

theorem mem_range_ι₀_or_mem_range_ιInf (x : glued K t) :
    x ∈ Set.range (ι₀ K t).base ∨ x ∈ Set.range (ιInf K t).base := by
  obtain ⟨i, y, hy⟩ :=
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).exists_eq x
  rcases i with (_ | _ | _)
  · have hw : (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).f none =
        f₀ K t ≫ ι₀ K t :=
      (colimit.w (span (f₀ K t) (fInf K t)) WalkingSpan.Hom.fst).symm
    refine Or.inl ⟨(f₀ K t).base y, ?_⟩
    rw [← hy, hw]
    rfl
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

private theorem range_ιInf_inter_range_ι₀_nonempty :
    (Set.range (ιInf K t).base ∩ Set.range (ι₀ K t).base).Nonempty := by
  obtain ⟨z⟩ := (inferInstance : Nonempty (XOverlap K t))
  refine ⟨(f₀ K t ≫ ι₀ K t).base z, ⟨(fInf K t).base z, ?_⟩, ⟨(f₀ K t).base z, rfl⟩⟩
  rw [glue_condition]
  rfl

end Glue

section Qualities

variable [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L]

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
instance isIntegral_glued : IsIntegral (glued K t) := by
  let 𝒰 := Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))
  have : ∀ i, IsReduced (𝒰.X i) := by
    rintro (_ | _ | _)
    · change IsReduced (XOverlap K t); infer_instance
    · change IsReduced (X₀ K t); infer_instance
    · change IsReduced (XInf K t); infer_instance
  have : IsReduced (glued K t) := IsReduced.of_openCover _ 𝒰
  have hA : IsIrreducible (Set.range (ι₀ K t).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (X₀ K t)).image _
      (ι₀ K t).base.hom.continuous.continuousOn
  have hB : IsIrreducible (Set.range (ιInf K t).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (XInf K t)).image _
      (ιInf K t).base.hom.continuous.continuousOn
  have hBA : Set.range (ιInf K t).base ⊆ closure (Set.range (ι₀ K t).base) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hB.isPreirreducible
      (ι₀ K t).isOpenEmbedding.isOpen_range (range_ιInf_inter_range_ι₀_nonempty K t)).trans
      (closure_mono Set.inter_subset_right)
  have huniv : closure (Set.range (ι₀ K t).base) = Set.univ :=
    Set.eq_univ_of_univ_subset fun x _ =>
      (mem_range_ι₀_or_mem_range_ιInf K t x).elim (fun h => subset_closure h) fun h => hBA h
  have : IrreducibleSpace (glued K t) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← huniv]
    exact hA.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Over a perfect field `K`, for transcendental `t` with `L` finite and separable over `K(t)`, the
glued scheme is smooth of relative dimension one over `Spec K`. -/
theorem smoothOfRelativeDimension_one_gluedToBase [PerfectField K] (ht : Transcendental K t) :
    SmoothOfRelativeDimension 1 (gluedToBase K t) :=
  smoothOfRelativeDimension_one_gluedToBase_of_charts K t
    (smoothOfRelativeDimension_one_Spec_chartRing K t ht)
    (smoothOfRelativeDimension_one_Spec_chartRing K t⁻¹ fun h => ht (IsAlgebraic.inv_iff.mp h))

instance isFractionRing_overlap : IsFractionRing (chartRing K ({t, t⁻¹} : Set L)) L :=
  IsFractionRing.of_field (chartRing K ({t, t⁻¹} : Set L)) L fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := chartRing K ({t} : Set L)) z
    exact ⟨⟨a, chartRing_mono K (singleton_subset_pair t) a.2⟩,
      ⟨b, chartRing_mono K (singleton_subset_pair t) b.2⟩, rfl⟩

instance algebra_overlap_functionField :
    Algebra (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
    (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

instance isFractionRing_overlap_functionField :
    IsFractionRing (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

/-- For `L` finite over `K(t)`, `L` is the function field of the overlap chart. -/
def overlapFunctionFieldAlgEquiv :
    L ≃ₐ[chartRing K ({t, t⁻¹} : Set L)] (XOverlap K t).functionField :=
  IsLocalization.algEquiv (nonZeroDivisors (chartRing K ({t, t⁻¹} : Set L))) L _

/-- The inclusion of the overlap chart into the glued scheme. -/
def ιU : XOverlap K t ⟶ glued K t := f₀ K t ≫ ι₀ K t

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
theorem ιU_eq : ιU K t = f₀ K t ≫ ι₀ K t := rfl

instance isOpenImmersion_ιU : IsOpenImmersion (ιU K t) :=
  inferInstanceAs (IsOpenImmersion (f₀ K t ≫ ι₀ K t))

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
theorem ιU_gluedToBase : ιU K t ≫ gluedToBase K t =
    Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t, t⁻¹} : Set L)))) := by
  have h : (incl₀ K t).toRingHom.comp (algebraMap K (chartRing K ({t} : Set L))) =
      algebraMap K (chartRing K ({t, t⁻¹} : Set L)) :=
    RingHom.ext fun a => (incl₀ K t).commutes a
  rw [ιU_eq, Category.assoc, ι₀_gluedToBase]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
theorem ιU_genericPoint :
    (ιU K t).base (genericPoint (XOverlap K t)) = genericPoint (glued K t) :=
  genericPoint_eq_of_isOpenImmersion (ιU K t)

/-- The function field of the glued scheme is that of the overlap chart. -/
def gluedFunctionFieldIsoOverlap :
    (glued K t).functionField ≅ (XOverlap K t).functionField :=
  (glued K t).presheaf.stalkCongr (.of_eq (ιU_genericPoint K t).symm) ≪≫
    asIso ((ιU K t).stalkMap (genericPoint (XOverlap K t)))

/-- For nonzero `t` with `L` finite over `K(t)`, the identification of `L` with the function field
of the glued scheme. -/
def gluedFunctionFieldEquiv : L ≃+* (glued K t).functionField :=
  (overlapFunctionFieldAlgEquiv K t).toRingEquiv.trans
    (gluedFunctionFieldIsoOverlap K t).commRingCatIsoToRingEquiv.symm

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem gluedFunctionFieldIsoOverlap_baseToFunctionField (a : K) :
    (gluedFunctionFieldIsoOverlap K t).hom (baseToFunctionField (gluedToBase K t) a) =
      algebraMap (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField
        (algebraMap K (chartRing K ({t, t⁻¹} : Set L)) a) := by
  change (ιU K t).stalkMap (genericPoint (XOverlap K t))
      ((glued K t).presheaf.stalkSpecializes
        (Inseparable.of_eq (ιU_genericPoint K t).symm).ge
        ((glued K t).presheaf.germ ⊤ (genericPoint (glued K t)) trivial
          ((gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)))) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  change (XOverlap K t).presheaf.germ ⊤ (genericPoint (XOverlap K t)) trivial
      ((ιU K t ≫ gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) = _
  rw [ιU_gluedToBase]
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t, t⁻¹} : Set L))))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))).inv
        (algebraMap K (chartRing K ({t, t⁻¹} : Set L)) a) := by
    have := congrArg (fun f : CommRingCat.of K ⟶ Γ(XOverlap K t, ⊤) => f a)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap K (chartRing K ({t, t⁻¹} : Set L)))))
    exact this.symm
  rw [h1]
  rfl

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
theorem gluedFunctionFieldEquiv_algebraMap (a : K) :
    gluedFunctionFieldEquiv K t (algebraMap K L a) =
      baseToFunctionField (gluedToBase K t) a := by
  change (gluedFunctionFieldIsoOverlap K t).commRingCatIsoToRingEquiv.symm
      (overlapFunctionFieldAlgEquiv K t (algebraMap K L a)) = _
  rw [RingEquiv.symm_apply_eq]
  change _ = (gluedFunctionFieldIsoOverlap K t).hom (baseToFunctionField (gluedToBase K t) a)
  rw [gluedFunctionFieldIsoOverlap_baseToFunctionField,
    IsScalarTower.algebraMap_apply K (chartRing K ({t, t⁻¹} : Set L)) L a, AlgEquiv.commutes]

end Qualities

instance isIntegral_adjoin_chartRing (S : Set L) :
    Algebra.IsIntegral (Algebra.adjoin K S) (chartRing K S) :=
  IsIntegralClosure.isIntegral_algebra (Algebra.adjoin K S) (A := chartRing K S) L

private theorem not_isField_chartRing (ht : Transcendental K t) :
    ¬ IsField (chartRing K ({t} : Set L)) := fun hF =>
  Polynomial.not_isField (R := K)
    (MulEquiv.isField
      (isField_of_isIntegral_of_isField
        (R := Algebra.adjoin K ({t} : Set L)) (S := chartRing K ({t} : Set L))
        (fun _ _ h => Subtype.ext (congrArg Subtype.val h :)) hF)
      (Polynomial.algEquivOfTranscendental K t ht).toMulEquiv)

theorem isMaximal_iff_ne_bot (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ L]
    [Algebra.IsSeparable K⟮t⟯ L]
    (𝔭 : Ideal (chartRing K ({t} : Set L))) [𝔭.IsPrime] : 𝔭.IsMaximal ↔ 𝔭 ≠ ⊥ :=
  ⟨fun h => Ring.ne_bot_of_isMaximal_of_not_isField h (not_isField_chartRing K t ht),
   fun h => Ideal.IsPrime.isMaximal inferInstance h⟩

section FiniteType

variable [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L]

instance locallyOfFiniteType_gluedToBase : LocallyOfFiniteType (gluedToBase K t) := by
  have h₀' : LocallyOfFiniteType (ι₀ K t ≫ gluedToBase K t) := by
    rw [ι₀_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hInf' : LocallyOfFiniteType (ιInf K t ≫ gluedToBase K t) := by
    rw [ιInf_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))) ?_
  rintro (_ | _ | _)
  · have key : (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).f none ≫
        gluedToBase K t = f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t) := by
      change colimit.ι (span (f₀ K t) (fInf K t)) none ≫ gluedToBase K t = _
      rw [← colimit.w (span (f₀ K t) (fInf K t)) WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    have := h₀'
    exact inferInstanceAs (LocallyOfFiniteType (f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t)))
  · change LocallyOfFiniteType (ι₀ K t ≫ gluedToBase K t)
    exact h₀'
  · change LocallyOfFiniteType (ιInf K t ≫ gluedToBase K t)
    exact hInf'

instance jacobsonSpace_glued : JacobsonSpace (glued K t) :=
  LocallyOfFiniteType.jacobsonSpace (gluedToBase K t)

theorem ι₀_mem_closedPoints_iff (x : X₀ K t) :
    (ι₀ K t).base x ∈ closedPoints (glued K t) ↔ x ∈ closedPoints (X₀ K t) := by
  rw [← Set.mem_preimage, (ι₀ K t).isOpenEmbedding.preimage_closedPoints]

theorem ιInf_mem_closedPoints_iff (x : XInf K t) :
    (ιInf K t).base x ∈ closedPoints (glued K t) ↔ x ∈ closedPoints (XInf K t) := by
  rw [← Set.mem_preimage, (ιInf K t).isOpenEmbedding.preimage_closedPoints]

end FiniteType

section Overlap

variable [Fact (t ≠ 0)]

theorem ι₀_eq_ιInf_iff (x₀ : X₀ K t) (xi : XInf K t) :
    (ι₀ K t).base x₀ = (ιInf K t).base xi ↔
      ∃ u : XOverlap K t, (f₀ K t).base u = x₀ ∧ (fInf K t).base u = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, u, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (f₀ K t) (fInf K t))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · cases fi
      cases fj
      exact ⟨u, h₁, h₂⟩
    · cases fj
    · cases fi
  · rintro ⟨u, rfl, rfl⟩
    change (f₀ K t ≫ ι₀ K t).base u = (fInf K t ≫ ιInf K t).base u
    rw [glue_condition]

private theorem range_fInf : Set.range (fInf K t).base =
    ((PrimeSpectrum.basicOpen (tInvChart K t) :
        TopologicalSpace.Opens (PrimeSpectrum (chartRing K ({t⁻¹} : Set L)))) :
      Set (PrimeSpectrum (chartRing K ({t⁻¹} : Set L)))) := by
  let := (inclInf K t).toRingHom.toAlgebra
  have := isLocalization_away_inclInf K t (Fact.out : t ≠ 0)
  exact PrimeSpectrum.localization_away_comap_range (chartRing K ({t, t⁻¹} : Set L))
    (tInvChart K t)

theorem range_f₀ : Set.range (f₀ K t).base =
    ((PrimeSpectrum.basicOpen (tChart K t) :
        TopologicalSpace.Opens (PrimeSpectrum (chartRing K ({t} : Set L)))) :
      Set (PrimeSpectrum (chartRing K ({t} : Set L)))) := by
  let := (incl₀ K t).toRingHom.toAlgebra
  have := isLocalization_away_incl₀ K t (Fact.out : t ≠ 0)
  exact PrimeSpectrum.localization_away_comap_range (chartRing K ({t, t⁻¹} : Set L))
    (tChart K t)

theorem ιInf_mem_range_ι₀_iff (xi : XInf K t) :
    (ιInf K t).base xi ∈ Set.range (ι₀ K t).base ↔ tInvChart K t ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨u, -, hu⟩ := (ι₀_eq_ιInf_iff K t x₀ xi).mp h
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(f₀ K t).base u, (ι₀_eq_ιInf_iff K t _ _).mpr ⟨u, rfl, rfl⟩⟩

theorem ι₀_mem_range_ιInf_iff (x₀ : X₀ K t) :
    (ι₀ K t).base x₀ ∈ Set.range (ιInf K t).base ↔ tChart K t ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_f₀, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨u, hu, -⟩ := (ι₀_eq_ιInf_iff K t x₀ xi).mp h.symm
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(fInf K t).base u, ((ι₀_eq_ιInf_iff K t _ _).mpr ⟨u, rfl, rfl⟩).symm⟩

end Overlap

section StalkRange

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]

variable (A : Subalgebra K L) (i : A →ₐ[K] chartRing K ({t, t⁻¹} : Set L))
  (hi : ∀ a : A, (i a : L) = a)
  (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
  (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in
scoped instance stalkAlgebra_spec (p : Spec (CommRingCat.of A)) :
    Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
  StructureSheaf.stalkAlgebra (↥A) p

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in
scoped instance isLocalization_stalk_spec (p : Spec (CommRingCat.of A)) :
    IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p) p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk (↥A) p

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in
private theorem specMap_genericPoint :
    (Spec.map (CommRingCat.ofHom i.toRingHom)).base (genericPoint (XOverlap K t)) =
      genericPoint (Spec (CommRingCat.of A)) :=
  genericPoint_eq_of_isOpenImmersion _

/-- For `L` finite over `K(t)` and a `K`-subalgebra `A` of `L` such that `i` makes the overlap
chart an open subscheme of `Spec A`, the map to `L` from the stalk of `Spec A` at `p`, through the
function field of the overlap chart. -/
def thetaHom (p : Spec (CommRingCat.of A)) : (Spec (CommRingCat.of A)).presheaf.stalk p →+* L :=
  ((overlapFunctionFieldAlgEquiv K t).symm : (XOverlap K t).functionField →+* L).comp
    (((Spec.map (CommRingCat.ofHom i.toRingHom)).stalkMap (genericPoint (XOverlap K t))).hom.comp
      ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
        (by rw [specMap_genericPoint]; exact genericPoint_specializes p)).hom)

include hi in
omit [Fact (t ≠ 0)] in
theorem thetaHom_toStalk (p : Spec (CommRingCat.of A)) (a : A) :
    thetaHom K t A i p (StructureSheaf.toStalk A p a) = a := by
  change (overlapFunctionFieldAlgEquiv K t).symm
      (((Spec.map (CommRingCat.ofHom i.toRingHom)).stalkMap (genericPoint (XOverlap K t)))
        (((Spec (CommRingCat.of A)).presheaf.stalkSpecializes _)
          (StructureSheaf.toStalk A p a))) = _
  erw [StructureSheaf.toStalk_stalkSpecializes_apply]
  erw [AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom i.toRingHom)
    (genericPoint (XOverlap K t)) a]
  change (overlapFunctionFieldAlgEquiv K t).symm
      (algebraMap (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField (i a)) = _
  rw [AlgEquiv.commutes]
  exact hi a

include hi in
omit [Fact (t ≠ 0)] in
private theorem thetaHom_mk' (p : Spec (CommRingCat.of A)) (a : A) (b : p.asIdeal.primeCompl) :
    thetaHom K t A i p (IsLocalization.mk' _ a b) = (a : L) * ((b : A) : L)⁻¹ := by
  have hb : ((b : A) : L) ≠ 0 := by
    intro h
    have : (b : A) = 0 := Subtype.ext h
    exact b.2 (this ▸ p.asIdeal.zero_mem)
  rw [eq_mul_inv_iff_mul_eq₀ hb]
  have := congrArg (thetaHom K t A i p)
    (IsLocalization.mk'_spec ((Spec (CommRingCat.of A)).presheaf.stalk p) a b)
  rw [map_mul] at this
  rw [← thetaHom_toStalk K t A i hi p a, ← thetaHom_toStalk K t A i hi p b]
  exact this

include hi in
omit [Fact (t ≠ 0)] in
private theorem range_thetaHom (p : Spec (CommRingCat.of A)) :
    Set.range (thetaHom K t A i p) =
      {y : L | ∃ a b : A, b ∉ p.asIdeal ∧ y = (a : L) * ((b : A) : L)⁻¹} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl s
    exact ⟨a, b, b.2, thetaHom_mk' K t A i hi p a b⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨IsLocalization.mk' _ a ⟨b, hb⟩, thetaHom_mk' K t A i hi p a ⟨b, hb⟩⟩

include comm in
omit [IsOpenImmersion ιA] in
theorem ffEquiv_symm_algebraMap_stalk (p : Spec (CommRingCat.of A))
    (s : (glued K t).presheaf.stalk (ιA.base p)) :
    (gluedFunctionFieldEquiv K t).symm
        (algebraMap ((glued K t).presheaf.stalk (ιA.base p)) (glued K t).functionField s) =
      thetaHom K t A i p ((ιA.stalkMap p) s) := by
  change (overlapFunctionFieldAlgEquiv K t).symm
      (((ιU K t).stalkMap (genericPoint (XOverlap K t)))
        (((glued K t).presheaf.stalkSpecializes
            (Inseparable.of_eq (ιU_genericPoint K t).symm).ge)
          (((glued K t).presheaf.stalkSpecializes _) s))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]
  rw [Scheme.Hom.stalkMap_congr_hom _ _ comm.symm]
  rw [CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_comp_apply, Scheme.Hom.stalkMap_comp]
  change (overlapFunctionFieldAlgEquiv K t).symm
      (((Spec.map (CommRingCat.ofHom i.toRingHom)).stalkMap (genericPoint (XOverlap K t)))
        ((ιA.stalkMap
            ((Spec.map (CommRingCat.ofHom i.toRingHom)).base (genericPoint (XOverlap K t))))
          (((glued K t).presheaf.stalkSpecializes _) s))) = _
  have hsp : (Spec.map (CommRingCat.ofHom i.toRingHom)).base (genericPoint (XOverlap K t)) ⤳ p := by
    rw [specMap_genericPoint]; exact genericPoint_specializes p
  erw [Scheme.Hom.stalkSpecializes_stalkMap_apply ιA _ _ hsp]
  rfl

include hi comm in
theorem range_ffEquiv_symm_comp_algebraMap_stalk (p : Spec (CommRingCat.of A)) :
    (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
        (algebraMap ((glued K t).presheaf.stalk (ιA.base p)) (glued K t).functionField)).range =
      {y : L | ∃ a b : A, b ∉ p.asIdeal ∧ y = (a : L) * ((b : A) : L)⁻¹} := by
  rw [← range_thetaHom K t A i hi p]
  ext y
  simp only [RingHom.coe_range, Set.mem_range, RingHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, (ffEquiv_symm_algebraMap_stalk K t A i ιA comm p s).symm⟩
  · rintro ⟨s', rfl⟩
    obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (ιA.stalkMap p)).2 s'
    exact ⟨s, ffEquiv_symm_algebraMap_stalk K t A i ιA comm p s⟩

end StalkRange

section PlaceMap

variable [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L]

omit [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
theorem transcendental_inv (ht : Transcendental K t) : Transcendental K t⁻¹ :=
  fun h => ht (IsAlgebraic.inv_iff.mp h)

/-- For transcendental `t`, the height-one prime of the chart ring of `{t}` at a closed point of
the first chart. -/
def primeOfι₀ (ht : Transcendental K t) (x₀ : X₀ K t)
    (hx : (ι₀ K t).base x₀ ∈ closedPoints (glued K t)) :
    HeightOneSpectrum (chartRing K ({t} : Set L)) :=
  ⟨x₀.asIdeal, x₀.isPrime,
    (isMaximal_iff_ne_bot K t ht _).mp ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x₀).mp
      ((ι₀_mem_closedPoints_iff K t x₀).mp hx))⟩

/-- For transcendental `t`, the height-one prime of the chart ring of `{t⁻¹}` at a closed point of
the second chart. -/
def primeOfιInf (ht : Transcendental K t) (xi : XInf K t)
    (hx : (ιInf K t).base xi ∈ closedPoints (glued K t)) :
    HeightOneSpectrum (chartRing K ({t⁻¹} : Set L)) :=
  ⟨xi.asIdeal, xi.isPrime,
    (isMaximal_iff_ne_bot K t⁻¹ (transcendental_inv K t ht) _).mp
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal xi).mp
        ((ιInf_mem_closedPoints_iff K t xi).mp hx))⟩

@[simp] theorem primeOfι₀_asIdeal (ht : Transcendental K t) (x₀ : X₀ K t) (hx) :
    (primeOfι₀ K t ht x₀ hx).asIdeal = x₀.asIdeal := rfl

@[simp] theorem primeOfιInf_asIdeal (ht : Transcendental K t) (xi : XInf K t) (hx) :
    (primeOfιInf K t ht xi hx).asIdeal = xi.asIdeal := rfl

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
theorem mem_range_ιInf_of_not_mem_range_ι₀ {x : glued K t}
    (h : x ∉ Set.range (ι₀ K t).base) : x ∈ Set.range (ιInf K t).base :=
  (mem_range_ι₀_or_mem_range_ιInf K t x).resolve_left h

open scoped Classical in
/-- For transcendental `t` with `L` finite and separable over `K(t)`, the place of `L / K`
attached to a closed point of the glued scheme. -/
def gluedPlaceOfPoint (ht : Transcendental K t) (x : closedPoints (glued K t)) : Place K L :=
  if h : x.1 ∈ Set.range (ι₀ K t).base then
    Place.ofHeightOneSpectrum (K := K)
      (primeOfι₀ K t ht (Classical.choose h) (by rw [Classical.choose_spec h]; exact x.2))
  else
    Place.ofHeightOneSpectrum (K := K)
      (primeOfιInf K t ht (Classical.choose (mem_range_ιInf_of_not_mem_range_ι₀ K t h))
        (by rw [Classical.choose_spec (mem_range_ιInf_of_not_mem_range_ι₀ K t h)]; exact x.2))

theorem gluedPlaceOfPoint_ι₀ (ht : Transcendental K t) (x₀ : X₀ K t)
    (hx : (ι₀ K t).base x₀ ∈ closedPoints (glued K t)) :
    gluedPlaceOfPoint K t ht ⟨(ι₀ K t).base x₀, hx⟩ =
      Place.ofHeightOneSpectrum (K := K) (primeOfι₀ K t ht x₀ hx) := by
  have h : (ι₀ K t).base x₀ ∈ Set.range (ι₀ K t).base := ⟨x₀, rfl⟩
  have hc : Classical.choose h = x₀ :=
    (ι₀ K t).isOpenEmbedding.injective (Classical.choose_spec h)
  have key : ∀ (y : X₀ K t) (hy) (_ : y = x₀), primeOfι₀ K t ht y hy = primeOfι₀ K t ht x₀ hx := by
    rintro y hy rfl; rfl
  unfold gluedPlaceOfPoint
  rw [dite_eq_left h, key _ _ hc]

theorem gluedPlaceOfPoint_of_not_mem (ht : Transcendental K t) (x : closedPoints (glued K t))
    (h : x.1 ∉ Set.range (ι₀ K t).base) (xi : XInf K t) (hxi : (ιInf K t).base xi = x.1) :
    gluedPlaceOfPoint K t ht x =
      Place.ofHeightOneSpectrum (K := K) (primeOfιInf K t ht xi (by rw [hxi]; exact x.2)) := by
  have hc : Classical.choose (mem_range_ιInf_of_not_mem_range_ι₀ K t h) = xi :=
    (ιInf K t).isOpenEmbedding.injective
      ((Classical.choose_spec (mem_range_ιInf_of_not_mem_range_ι₀ K t h)).trans hxi.symm)
  have key : ∀ (y : XInf K t) (hy) (_ : y = xi),
      primeOfιInf K t ht y hy = primeOfιInf K t ht xi (by rw [hxi]; exact x.2) := by
    rintro y hy rfl; rfl
  unfold gluedPlaceOfPoint
  rw [dite_eq_right h, key _ _ hc]

private theorem t_mem_of_ι₀ (ht : Transcendental K t) (x₀ : X₀ K t) (hx) :
    t ∈ (Place.ofHeightOneSpectrum (K := K) (primeOfι₀ K t ht x₀ hx)).toValuationSubring :=
  mem_ofHeightOneSpectrum K t _

private theorem t_not_mem_of_ιInf (ht : Transcendental K t) (xi : XInf K t) (hx)
    (hxi : tInvChart K t ∈ xi.asIdeal) :
    t ∉ (Place.ofHeightOneSpectrum (K := K) (primeOfιInf K t ht xi hx)).toValuationSubring := by
  intro htmem
  set 𝔮 := primeOfιInf K t ht xi hx
  have h1 : 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) 𝔮 (tInvChart K t)).mpr hxi
  have h2 : 𝔮.valuation L t ≤ 1 := by
    rwa [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
      at htmem
  have h3 : 𝔮.valuation L (t * t⁻¹) < 1 := by
    rw [map_mul]
    calc 𝔮.valuation L t * 𝔮.valuation L t⁻¹
        ≤ 1 * 𝔮.valuation L t⁻¹ := mul_le_mul' h2 le_rfl
      _ = 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) := by
          rw [one_mul, coe_tInvChart]
      _ < 1 := h1
  rw [mul_inv_cancel₀ (Fact.out : t ≠ 0), map_one] at h3
  exact lt_irrefl _ h3

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem tInvChart_mem_of_not_mem_range (xi : XInf K t)
    (h : (ιInf K t).base xi ∉ Set.range (ι₀ K t).base) : tInvChart K t ∈ xi.asIdeal := by
  by_contra hne
  exact h ((ιInf_mem_range_ι₀_iff K t xi).mpr hne)

theorem gluedPlaceOfPoint_injective (ht : Transcendental K t) :
    Function.Injective (gluedPlaceOfPoint K t ht) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  by_cases h₁ : x ∈ Set.range (ι₀ K t).base <;> by_cases h₂ : y ∈ Set.range (ι₀ K t).base
  · obtain ⟨x₀, rfl⟩ := h₁
    obtain ⟨y₀, rfl⟩ := h₂
    rw [gluedPlaceOfPoint_ι₀, gluedPlaceOfPoint_ι₀] at hxy
    have h' := Place.ofHeightOneSpectrum_injective (K := K) hxy
    have hxy' : x₀ = y₀ := PrimeSpectrum.ext (congrArg HeightOneSpectrum.asIdeal h')
    subst hxy'
    rfl
  · exfalso
    obtain ⟨x₀, rfl⟩ := h₁
    obtain ⟨yi, hyi⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h₂
    rw [gluedPlaceOfPoint_ι₀, gluedPlaceOfPoint_of_not_mem K t ht ⟨y, hy⟩ h₂ yi hyi] at hxy
    refine t_not_mem_of_ιInf K t ht yi _ (tInvChart_mem_of_not_mem_range K t yi ?_)
      (hxy ▸ t_mem_of_ι₀ K t ht x₀ hx)
    rwa [hyi]
  · exfalso
    obtain ⟨y₀, rfl⟩ := h₂
    obtain ⟨xi, hxi⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h₁
    rw [gluedPlaceOfPoint_ι₀, gluedPlaceOfPoint_of_not_mem K t ht ⟨x, hx⟩ h₁ xi hxi] at hxy
    refine t_not_mem_of_ιInf K t ht xi _ (tInvChart_mem_of_not_mem_range K t xi ?_)
      (hxy ▸ t_mem_of_ι₀ K t ht y₀ hy)
    rwa [hxi]
  · obtain ⟨xi, hxi⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h₁
    obtain ⟨yi, hyi⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h₂
    rw [gluedPlaceOfPoint_of_not_mem K t ht ⟨x, hx⟩ h₁ xi hxi,
      gluedPlaceOfPoint_of_not_mem K t ht ⟨y, hy⟩ h₂ yi hyi] at hxy
    have h' := Place.ofHeightOneSpectrum_injective (K := K) hxy
    have hxy' : xi = yi := PrimeSpectrum.ext (congrArg HeightOneSpectrum.asIdeal h')
    subst hxy'
    exact Subtype.ext (hxi.symm.trans hyi)

theorem gluedPlaceOfPoint_surjective (ht : Transcendental K t) :
    Function.Surjective (gluedPlaceOfPoint K t ht) := by
  intro v
  by_cases hv : t ∈ v.toValuationSubring
  · obtain ⟨𝔭, h𝔭⟩ := exists_ofHeightOneSpectrum_eq K t v hv
    let x₀ : X₀ K t := ⟨𝔭.asIdeal, 𝔭.isPrime⟩
    have hx₀ : x₀ ∈ closedPoints (X₀ K t) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal x₀).mpr 𝔭.isMaximal
    refine ⟨⟨(ι₀ K t).base x₀, (ι₀_mem_closedPoints_iff K t x₀).mpr hx₀⟩, ?_⟩
    rw [gluedPlaceOfPoint_ι₀, ← h𝔭]
    rfl
  · have hv' : t⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem t).resolve_left hv
    obtain ⟨𝔮, h𝔮⟩ := exists_ofHeightOneSpectrum_eq K t⁻¹ v hv'
    let xi : XInf K t := ⟨𝔮.asIdeal, 𝔮.isPrime⟩
    have hxi : xi ∈ closedPoints (XInf K t) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal xi).mpr 𝔮.isMaximal
    have hmem : tInvChart K t ∈ xi.asIdeal := by
      change tInvChart K t ∈ 𝔮.asIdeal
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
      have hvt : ¬ 𝔮.valuation L t ≤ 1 := by
        rwa [← Valuation.mem_valuationSubring_iff,
          ← Place.ofHeightOneSpectrum_toValuationSubring (K := K) 𝔮, h𝔮]
      have hprod : 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) *
          𝔮.valuation L t = 1 := by
        rw [← map_mul, coe_tInvChart, inv_mul_cancel₀ (Fact.out : t ≠ 0), map_one]
      by_contra hge
      have hge' : 1 ≤ 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) :=
        not_lt.mp hge
      have : (1 : WithZero (Multiplicative ℤ)) < 1 :=
        calc (1 : WithZero (Multiplicative ℤ)) < 𝔮.valuation L t := not_le.mp hvt
          _ = 1 * 𝔮.valuation L t := (one_mul _).symm
          _ ≤ 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) *
                𝔮.valuation L t := mul_le_mul' hge' le_rfl
          _ = 1 := hprod
      exact lt_irrefl _ this
    have hnot : (ιInf K t).base xi ∉ Set.range (ι₀ K t).base :=
      fun hr => ((ιInf_mem_range_ι₀_iff K t xi).mp hr) hmem
    refine ⟨⟨(ιInf K t).base xi, (ιInf_mem_closedPoints_iff K t xi).mpr hxi⟩, ?_⟩
    rw [gluedPlaceOfPoint_of_not_mem K t ht _ hnot xi rfl, ← h𝔮]
    rfl

/-- For transcendental `t` with `L` finite and separable over `K(t)`, the map attaching a place of
`L / K` to each closed point of the glued scheme is a bijection. -/
theorem gluedPlaceOfPoint_bijective (ht : Transcendental K t) :
    Function.Bijective (gluedPlaceOfPoint K t ht) :=
  ⟨gluedPlaceOfPoint_injective K t ht, gluedPlaceOfPoint_surjective K t ht⟩

/-- For transcendental `t` with `L` finite and separable over `K(t)`, the local ring of the glued
scheme at a closed point, carried into `L` by the identification of the function field with `L`, is
the valuation ring of the place attached to that point. -/
theorem range_stalk_eq_gluedPlaceOfPoint (ht : Transcendental K t) (x : closedPoints (glued K t)) :
    (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
        (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
      (gluedPlaceOfPoint K t ht x).toValuationSubring.toSubring := by
  obtain ⟨x, hx⟩ := x
  by_cases h : x ∈ Set.range (ι₀ K t).base
  · obtain ⟨x₀, rfl⟩ := h
    rw [gluedPlaceOfPoint_ι₀, Place.ofHeightOneSpectrum_toValuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := L) (v := primeOfι₀ K t ht x₀ hx),
      HeightOneSpectrum.valuationSubringAtPrime_toSubring]
    apply SetLike.ext'
    erw [range_ffEquiv_symm_comp_algebraMap_stalk K t (chartRing K ({t} : Set L)) (incl₀ K t)
      (fun a => coe_chartIncl K _ a) (ι₀ K t) rfl x₀]
    ext y
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
  · obtain ⟨xi, rfl⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h
    rw [gluedPlaceOfPoint_of_not_mem K t ht _ h xi rfl,
      Place.ofHeightOneSpectrum_toValuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := L) (v := primeOfιInf K t ht xi hx),
      HeightOneSpectrum.valuationSubringAtPrime_toSubring]
    apply SetLike.ext'
    erw [range_ffEquiv_symm_comp_algebraMap_stalk K t (chartRing K ({t⁻¹} : Set L)) (inclInf K t)
      (fun a => coe_chartIncl K _ a) (ιInf K t) (glue_condition K t).symm xi]
    ext y
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩

end PlaceMap

end CurveModel

end AlgebraicCurve
