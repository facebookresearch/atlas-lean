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

public import MathlibExt.AlgebraicGeometry.Curve.GluedChartsProper

/-!
# Affine opens of the two-chart model

Let `t` be nonzero with `L` finite over `K(t)`. For `a ∈ K` with `t ≠ a`, the union of the loci
`t ≠ a` in the first chart and `1 - a t⁻¹ ≠ 0` in the second chart is an affine open of
`AlgebraicCurve.CurveModel.glued K t`. Over an infinite field every finite set of points lies in
one of these affine opens (`AlgebraicCurve.CurveModel.finset_subset_affineOpen_glued`).
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField IsDedekindDomain
open Topology TopCat

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)

open TopologicalSpace

section ChartGerms

variable (A : Subalgebra K L)

/-- An element of `A`, as a global section of `Spec A`. -/
def secTop (r : A) : Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv r

private theorem mem_basicOpen_secTop (r : A) (p : Spec (CommRingCat.of A)) :
    p ∈ (Spec (CommRingCat.of A)).basicOpen (secTop K A r) ↔ r ∉ p.asIdeal := by
  rw [secTop, basicOpen_eq_of_affine]
  exact Iff.rfl

private theorem germ_res_secTop (r : A) (V : (Spec (CommRingCat.of A)).Opens)
    (p : Spec (CommRingCat.of A))
    (hp : p ∈ V) :
    (Spec (CommRingCat.of A)).presheaf.germ V p hp
        ((Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (secTop K A r)) =
      algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) r := by
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

variable [Fact (t ≠ 0)] (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]

private theorem stalkMap_germ_appIso_inv (V : (Spec (CommRingCat.of A)).Opens)
    (τ : Γ(Spec (CommRingCat.of A), V)) (p : Spec (CommRingCat.of A)) (hp : p ∈ V) :
    ιA.stalkMap p ((glued K t).presheaf.germ (ιA ''ᵁ V) (ιA.base p) ⟨p, hp, rfl⟩
        ((ιA.appIso V).inv τ)) = (Spec (CommRingCat.of A)).presheaf.germ V p hp τ := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have : ιA.app (ιA ''ᵁ V) ((ιA.appIso V).inv τ) =
      (Spec (CommRingCat.of A)).presheaf.map (eqToHom (ιA.preimage_image_eq V)).op τ := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_app]
  rw [this, TopCat.Presheaf.germ_res_apply]

/-- The constant `a`, as a section of the glued scheme over `W`. -/
def cSec (a : K) (W : (glued K t).Opens) : Γ(glued K t, W) :=
  (glued K t).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
    ((gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

omit [IsOpenImmersion ιA] in
private theorem stalkMap_germ_cSec
    (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (a : K) (W : (glued K t).Opens) (p : Spec (CommRingCat.of A)) (hp : ιA.base p ∈ W) :
    ιA.stalkMap p ((glued K t).presheaf.germ W (ιA.base p) hp (cSec K t a W)) =
      algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) (algebraMap K A a) := by
  rw [cSec, TopCat.Presheaf.germ_res_apply]
  have : (glued K t).presheaf.germ ⊤ (ιA.base p) trivial
      ((gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
      (gluedToBase K t).stalkMap (ιA.base p)
        (StructureSheaf.toStalk (CommRingCat.of K) _ a) :=
    (Scheme.Hom.germ_stalkMap_apply (gluedToBase K t) ⊤ (ιA.base p) trivial _).symm
  rw [this]
  exact stalkMap_chart_toStalk K t A ιA ιA_toBase p a

private theorem isUnit_stalkMap_iff (p : Spec (CommRingCat.of A))
    (y : (glued K t).presheaf.stalk (ιA.base p)) : IsUnit (ιA.stalkMap p y) ↔ IsUnit y := by
  change IsUnit (stalkChartEquiv K t A ιA p y) ↔ IsUnit y
  exact ⟨fun h => by simpa using h.map (stalkChartEquiv K t A ιA p).symm, fun h => h.map _⟩

variable [FiniteDimensional K⟮t⟯ L]
variable (i : A →ₐ[K] chartRing K ({t, t⁻¹} : Set L)) (hi : ∀ a : A, (i a : L) = a)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
  (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)

include hi in
omit [Fact (t ≠ 0)] [IsOpenImmersion ιA] in
private theorem thetaHom_algebraMap (p : Spec (CommRingCat.of A)) (r : A) :
    thetaHom K t A i p (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) r) = r :=
  thetaHom_toStalk K t A i hi p r

include hi comm in
private theorem ffEquiv_symm_germ_appIso_inv (V : (Spec (CommRingCat.of A)).Opens)
    (τ : Γ(Spec (CommRingCat.of A), V)) (p : Spec (CommRingCat.of A)) (hp : p ∈ V)
    (hη : genericPoint (glued K t) ∈ ιA ''ᵁ V) :
    (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (ιA ''ᵁ V) (genericPoint (glued K t)) hη ((ιA.appIso V).inv τ)) =
      thetaHom K t A i p ((Spec (CommRingCat.of A)).presheaf.germ V p hp τ) := by
  have _ := hi
  have hsp : genericPoint (glued K t) ⤳ ιA.base p := genericPoint_specializes _
  have e := CategoryTheory.ConcreteCategory.congr_hom
    (TopCat.Presheaf.germ_stalkSpecializes (glued K t).presheaf (U := ιA ''ᵁ V) ⟨p, hp, rfl⟩ hsp)
    ((ιA.appIso V).inv τ)
  rw [CommRingCat.comp_apply] at e
  rw [← e]
  have h2 := ffEquiv_symm_algebraMap_stalk K t A i ιA comm p
    ((glued K t).presheaf.germ (ιA ''ᵁ V) (ιA.base p) ⟨p, hp, rfl⟩ ((ιA.appIso V).inv τ))
  rw [stalkMap_germ_appIso_inv] at h2
  exact h2

end ChartGerms

section LocalSections

variable (a : K)

/-- The element `t - a` of the chart ring of `{t}`. -/
def tma : chartRing K ({t} : Set L) := tChart K t - algebraMap K _ a

/-- The element `1 - a t⁻¹` of the chart ring of `{t⁻¹}`. -/
def gInf : chartRing K ({t⁻¹} : Set L) := 1 - algebraMap K _ a * tInvChart K t

theorem coe_tma : (tma K t a : L) = t - algebraMap K L a := by
  rw [tma, Subalgebra.coe_sub, coe_tChart, Subalgebra.coe_algebraMap]

theorem coe_gInf : (gInf K t a : L) = 1 - algebraMap K L a * t⁻¹ := by
  rw [gInf, Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul, coe_tInvChart,
    Subalgebra.coe_algebraMap]

private theorem incl₀_tma [Fact (t ≠ 0)] :
    incl₀ K t (tma K t a) = incl₀ K t (tChart K t) * inclInf K t (gInf K t a) := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_chartIncl, coe_tma, coe_tChart,
    coe_gInf, mul_sub, mul_one, mul_left_comm, mul_inv_cancel₀ (Fact.out : t ≠ 0), mul_one]

private theorem gInf_add : gInf K t a + algebraMap K _ a * tInvChart K t = 1 := by
  rw [gInf, sub_add_cancel]

private theorem tma_add : tma K t a + algebraMap K _ a = tChart K t := by
  rw [tma, sub_add_cancel]

/-- The locus `t ≠ a` in the chart of `{t}`. -/
def U₁ : (X₀ K t).Opens := (X₀ K t).basicOpen (secTop K (chartRing K ({t} : Set L)) (tma K t a))

/-- The locus `1 - a t⁻¹ ≠ 0` in the chart of `{t⁻¹}`. -/
def U₂ : (XInf K t).Opens :=
  (XInf K t).basicOpen (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a))

theorem mem_U₁_iff (p : X₀ K t) : p ∈ U₁ K t a ↔ tma K t a ∉ p.asIdeal :=
  mem_basicOpen_secTop K _ _ p

theorem mem_U₂_iff (q : XInf K t) : q ∈ U₂ K t a ↔ gInf K t a ∉ q.asIdeal :=
  mem_basicOpen_secTop K _ _ q

theorem isUnit_res_tma : IsUnit ((X₀ K t).presheaf.map
    (homOfLE ((X₀ K t).basicOpen_le (secTop K (chartRing K ({t} : Set L)) (tma K t a)))).op
    (secTop K (chartRing K ({t} : Set L)) (tma K t a))) :=
  RingedSpace.isUnit_res_basicOpen (X := (X₀ K t).toLocallyRingedSpace.toSheafedSpace) _

theorem isUnit_res_gInf : IsUnit ((XInf K t).presheaf.map
    (homOfLE ((XInf K t).basicOpen_le (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a)))).op
    (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a))) :=
  RingedSpace.isUnit_res_basicOpen (X := (XInf K t).toLocallyRingedSpace.toSheafedSpace) _

/-- The section `1 / (t - a)` over `U₁`. -/
def σ₁ : Γ(X₀ K t, U₁ K t a) := (((isUnit_res_tma K t a).unit⁻¹ : (Γ(X₀ K t, U₁ K t a))ˣ) : _)

/-- The section `t⁻¹ / (1 - a t⁻¹)` over `U₂`. -/
def σ₂ : Γ(XInf K t, U₂ K t a) :=
  (XInf K t).presheaf.map (homOfLE (le_top : U₂ K t a ≤ ⊤)).op
      (secTop K (chartRing K ({t⁻¹} : Set L)) (tInvChart K t)) *
    (((isUnit_res_gInf K t a).unit⁻¹ : (Γ(XInf K t, U₂ K t a))ˣ) : _)

private theorem germ_σ₁_mul (p : X₀ K t) (hp : p ∈ U₁ K t a) :
    (X₀ K t).presheaf.germ (U₁ K t a) p hp (σ₁ K t a) *
      algebraMap _ ((X₀ K t).presheaf.stalk p) (tma K t a) = 1 := by
  have hu : σ₁ K t a * (X₀ K t).presheaf.map (homOfLE (le_top : U₁ K t a ≤ ⊤)).op
      (secTop K (chartRing K ({t} : Set L)) (tma K t a)) = 1 := Units.inv_mul _
  rw [← germ_res_secTop K (chartRing K ({t} : Set L)) (tma K t a) (U₁ K t a) p hp, ← map_mul, hu,
    map_one]

private theorem germ_σ₂_mul (q : XInf K t) (hq : q ∈ U₂ K t a) :
    (XInf K t).presheaf.germ (U₂ K t a) q hq (σ₂ K t a) *
      algebraMap _ ((XInf K t).presheaf.stalk q) (gInf K t a) =
    algebraMap _ ((XInf K t).presheaf.stalk q) (tInvChart K t) := by
  have hu : ((((isUnit_res_gInf K t a).unit⁻¹ : (Γ(XInf K t, U₂ K t a))ˣ) : Γ(XInf K t, U₂ K t a)) *
      (XInf K t).presheaf.map (homOfLE (le_top : U₂ K t a ≤ ⊤)).op
        (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a))) = 1 := Units.inv_mul _
  rw [← germ_res_secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a) (U₂ K t a) q hq,
    ← germ_res_secTop K (chartRing K ({t⁻¹} : Set L)) (tInvChart K t) (U₂ K t a) q hq, ← map_mul,
    σ₂, mul_assoc, hu, mul_one]

end LocalSections

section Values

variable [Fact (t ≠ 0)] (a : K)

/-- The image of `U₁` in the glued scheme. -/
def V₁ : (glued K t).Opens := ι₀ K t ''ᵁ U₁ K t a

/-- The image of `U₂` in the glued scheme. -/
def V₂ : (glued K t).Opens := ιInf K t ''ᵁ U₂ K t a

/-- The open `V₁ ∪ V₂` of the glued scheme, which is affine when `t ≠ a`. -/
def Ua : (glued K t).Opens := V₁ K t a ⊔ V₂ K t a

private theorem isAffineOpen_V₁ : IsAffineOpen (V₁ K t a) :=
  ((isAffineOpen_top (X₀ K t)).basicOpen _).image_of_isOpenImmersion (ι₀ K t)

private theorem isAffineOpen_V₂ : IsAffineOpen (V₂ K t a) :=
  ((isAffineOpen_top (XInf K t)).basicOpen _).image_of_isOpenImmersion (ιInf K t)

/-- The section `1 / (t - a)` over `V₁`. -/
def f₁' : Γ(glued K t, V₁ K t a) := ((ι₀ K t).appIso (U₁ K t a)).inv (σ₁ K t a)

/-- The section `1 / (t - a)` over `V₂`. -/
def f₂' : Γ(glued K t, V₂ K t a) := ((ιInf K t).appIso (U₂ K t a)).inv (σ₂ K t a)

variable (ha : (t - algebraMap K L a) ≠ 0)

include ha in
omit [Fact (t ≠ 0)] in
private theorem one_sub_ne_zero [Fact (t ≠ 0)] : (1 - algebraMap K L a * t⁻¹) ≠ 0 := by
  intro h
  apply ha
  have : t * (1 - algebraMap K L a * t⁻¹) = t - algebraMap K L a := by
    rw [mul_sub, mul_one, mul_left_comm, mul_inv_cancel₀ (Fact.out : t ≠ 0), mul_one]
  rw [← this, h, mul_zero]

include ha in
omit [Fact (t ≠ 0)] in
private theorem genericPoint_mem_U₁ : genericPoint (X₀ K t) ∈ U₁ K t a := by
  rw [mem_U₁_iff, genericPoint_eq_bot_of_affine]
  intro h
  apply ha
  have h' : (tma K t a : L) = 0 := by
    rw [(Ideal.mem_bot.mp h : tma K t a = 0)]; rfl
  rwa [coe_tma] at h'

include ha in
private theorem genericPoint_mem_U₂ : genericPoint (XInf K t) ∈ U₂ K t a := by
  rw [mem_U₂_iff, genericPoint_eq_bot_of_affine]
  intro h
  apply one_sub_ne_zero K t a ha
  have h' : (gInf K t a : L) = 0 := by
    rw [(Ideal.mem_bot.mp h : gInf K t a = 0)]; rfl
  rwa [coe_gInf] at h'

include ha in
private theorem genericPoint_mem : genericPoint (glued K t) ∈ V₁ K t a ⊓ V₂ K t a :=
  ⟨⟨genericPoint (X₀ K t), genericPoint_mem_U₁ K t a ha,
    genericPoint_eq_of_isOpenImmersion (ι₀ K t)⟩,
   ⟨genericPoint (XInf K t), genericPoint_mem_U₂ K t a ha,
    genericPoint_eq_of_isOpenImmersion (ιInf K t)⟩⟩

variable [FiniteDimensional K⟮t⟯ L]

include ha in
private theorem val_f₁' (hη : genericPoint (glued K t) ∈ V₁ K t a) :
    (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (V₁ K t a) (genericPoint (glued K t)) hη (f₁' K t a)) =
      (t - algebraMap K L a)⁻¹ := by
  have hp := genericPoint_mem_U₁ K t a ha
  have h1 : (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (V₁ K t a) (genericPoint (glued K t)) hη (f₁' K t a)) =
      thetaHom K t (chartRing K ({t} : Set L)) (incl₀ K t) (genericPoint (X₀ K t))
        ((X₀ K t).presheaf.germ (U₁ K t a) _ hp (σ₁ K t a)) :=
    ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t} : Set L)) (ι₀ K t) (incl₀ K t)
      (fun b => coe_chartIncl K _ b) rfl (U₁ K t a) (σ₁ K t a) _ hp hη
  rw [h1]
  have h := congrArg (thetaHom K t (chartRing K ({t} : Set L)) (incl₀ K t) (genericPoint (X₀ K t)))
    (germ_σ₁_mul K t a _ hp)
  rw [map_mul, map_one, thetaHom_algebraMap K t _ (incl₀ K t) (fun b => coe_chartIncl K _ b),
    coe_tma] at h
  exact eq_inv_of_mul_eq_one_left h

include ha in
private theorem val_f₂' (hη : genericPoint (glued K t) ∈ V₂ K t a) :
    (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (V₂ K t a) (genericPoint (glued K t)) hη (f₂' K t a)) =
      t⁻¹ * (1 - algebraMap K L a * t⁻¹)⁻¹ := by
  have hq := genericPoint_mem_U₂ K t a ha
  have h1 : (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (V₂ K t a) (genericPoint (glued K t)) hη (f₂' K t a)) =
      thetaHom K t (chartRing K ({t⁻¹} : Set L)) (inclInf K t) (genericPoint (XInf K t))
        ((XInf K t).presheaf.germ (U₂ K t a) _ hq (σ₂ K t a)) :=
    ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t⁻¹} : Set L)) (ιInf K t) (inclInf K t)
      (fun b => coe_chartIncl K _ b) (glue_condition K t).symm (U₂ K t a) (σ₂ K t a) _ hq hη
  rw [h1]
  have h := congrArg (thetaHom K t (chartRing K ({t⁻¹} : Set L)) (inclInf K t)
    (genericPoint (XInf K t))) (germ_σ₂_mul K t a _ hq)
  rw [map_mul, thetaHom_algebraMap K t _ (inclInf K t) (fun b => coe_chartIncl K _ b),
    thetaHom_algebraMap K t _ (inclInf K t) (fun b => coe_chartIncl K _ b), coe_gInf,
    coe_tInvChart] at h
  exact (eq_mul_inv_iff_mul_eq₀ (one_sub_ne_zero K t a ha)).mpr h

include ha in
private theorem res_f₁'_eq_res_f₂' (W : (glued K t).Opens) (h₁ : W ≤ V₁ K t a) (h₂ : W ≤ V₂ K t a)
    (hη : genericPoint (glued K t) ∈ W) :
    (glued K t).presheaf.map (homOfLE h₁).op (f₁' K t a) =
    (glued K t).presheaf.map (homOfLE h₂).op (f₂' K t a) := by
  apply germ_injective_of_isIntegral (glued K t) (genericPoint (glued K t)) hη
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  apply (gluedFunctionFieldEquiv K t).symm.injective
  rw [val_f₁' K t a ha, val_f₂' K t a ha, ← mul_inv, mul_sub, mul_one, mul_left_comm,
    mul_inv_cancel₀ (Fact.out : t ≠ 0), mul_one]

/-- The cover of `Ua` by `V₁` and `V₂`. -/
def cover : Bool → (glued K t).Opens := fun b => cond b (V₁ K t a) (V₂ K t a)

include ha in
private theorem exists_glued_section : ∃ f : Γ(glued K t, Ua K t a),
    (glued K t).presheaf.map (homOfLE (le_sup_left : V₁ K t a ≤ Ua K t a)).op f = f₁' K t a ∧
    (glued K t).presheaf.map (homOfLE (le_sup_right : V₂ K t a ≤ Ua K t a)).op f = f₂' K t a := by
  have hη := genericPoint_mem K t a ha
  let sf : ∀ b : Bool, Γ(glued K t, cover K t a b) := fun b =>
    match b with
    | true => f₁' K t a
    | false => f₂' K t a
  have hcompat : TopCat.Presheaf.IsCompatible (glued K t).sheaf.1 (cover K t a) sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact (res_f₁'_eq_res_f₂' K t a ha (V₂ K t a ⊓ V₁ K t a) inf_le_right inf_le_left
        ⟨hη.2, hη.1⟩).symm
    · exact res_f₁'_eq_res_f₂' K t a ha (V₁ K t a ⊓ V₂ K t a) inf_le_left inf_le_right hη
    · rfl
  obtain ⟨f, hf, -⟩ := (glued K t).sheaf.existsUnique_gluing' (cover K t a) (Ua K t a)
    (fun b => match b with
      | true => homOfLE le_sup_left
      | false => homOfLE le_sup_right)
    (by change V₁ K t a ⊔ V₂ K t a ≤ iSup (cover K t a); rw [iSup_bool_eq]; exact le_rfl) sf hcompat
  exact ⟨f, hf true, hf false⟩

end Values

section Affine

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] (a : K) (ha : (t - algebraMap K L a) ≠ 0)

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in
private theorem f₀_appTop_secTop (r : chartRing K ({t} : Set L)) :
    (f₀ K t).appTop (secTop K _ r) = secTop K _ (incl₀ K t r) := by
  have := congrArg (fun g : CommRingCat.of (chartRing K ({t} : Set L)) ⟶ Γ(XOverlap K t, ⊤) => g r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (incl₀ K t).toRingHom))
  exact this.symm

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in
private theorem fInf_appTop_secTop (r : chartRing K ({t⁻¹} : Set L)) :
    (fInf K t).appTop (secTop K _ r) = secTop K _ (inclInf K t r) := by
  have := congrArg (fun g : CommRingCat.of (chartRing K ({t⁻¹} : Set L)) ⟶ Γ(XOverlap K t, ⊤) =>
    g r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclInf K t).toRingHom))
  exact this.symm

omit [FiniteDimensional K⟮t⟯ L] in
private theorem tma_not_mem_iff (p : X₀ K t) (q : XInf K t)
    (h : (ι₀ K t).base p = (ιInf K t).base q) :
    tma K t a ∉ p.asIdeal ↔ gInf K t a ∉ q.asIdeal := by
  obtain ⟨u, hu₀, hui⟩ := (ι₀_eq_ιInf_iff K t p q).mp h
  have key : incl₀ K t (tma K t a) ∉ u.asIdeal ↔ inclInf K t (gInf K t a) ∉ u.asIdeal := by
    rw [incl₀_tma]
    have ht : incl₀ K t (tChart K t) ∉ u.asIdeal := fun hmem =>
      u.isPrime.ne_top (u.asIdeal.eq_top_of_isUnit_mem hmem
        (IsUnit.of_mul_eq_one _ (incl₀_tChart_mul_inclInf_tInvChart K t)))
    constructor
    · exact fun hn hg => hn (u.asIdeal.mul_mem_left _ hg)
    · intro hg hn
      rcases u.isPrime.mem_or_mem hn with h' | h'
      · exact ht h'
      · exact hg h'
  rw [← hu₀, ← hui, ← mem_U₁_iff, ← mem_U₂_iff, ← Scheme.Hom.mem_preimage (f₀ K t),
    ← Scheme.Hom.mem_preimage (fInf K t), U₁, U₂, Scheme.preimage_basicOpen_top,
    Scheme.preimage_basicOpen_top, f₀_appTop_secTop, fInf_appTop_secTop, mem_basicOpen_secTop,
    mem_basicOpen_secTop]
  exact key

variable (f : Γ(glued K t, Ua K t a))
  (hf₁ : (glued K t).presheaf.map (homOfLE (le_sup_left : V₁ K t a ≤ Ua K t a)).op f = f₁' K t a)
  (hf₂ : (glued K t).presheaf.map (homOfLE (le_sup_right : V₂ K t a ≤ Ua K t a)).op f = f₂' K t a)

/-- The section `1 + a f` over `Ua`, which is `t / (t - a)` when `f` is `1 / (t - a)`. -/
def fTwo : Γ(glued K t, Ua K t a) := 1 + cSec K t a (Ua K t a) * f

omit [FiniteDimensional K⟮t⟯ L] in
private theorem span_eq_top : Ideal.span ({f, fTwo K t a f} : Set Γ(glued K t, Ua K t a)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
  exact ⟨-cSec K t a (Ua K t a), 1, by rw [fTwo]; ring⟩

include hf₁ in
omit [FiniteDimensional K⟮t⟯ L] in
private theorem stalkMap_germ_f_V₁ (p : X₀ K t) (hp : p ∈ U₁ K t a) :
    (ι₀ K t).stalkMap p ((glued K t).presheaf.germ (Ua K t a) ((ι₀ K t).base p)
        (le_sup_left (α := (glued K t).Opens) ⟨p, hp, rfl⟩) f) =
      (X₀ K t).presheaf.germ (U₁ K t a) p hp (σ₁ K t a) := by
  have e : (glued K t).presheaf.germ (V₁ K t a) ((ι₀ K t).base p) ⟨p, hp, rfl⟩
      ((glued K t).presheaf.map (homOfLE (le_sup_left : V₁ K t a ≤ Ua K t a)).op f) =
      (glued K t).presheaf.germ (Ua K t a) ((ι₀ K t).base p)
        (le_sup_left (α := (glued K t).Opens) ⟨p, hp, rfl⟩) f :=
    TopCat.Presheaf.germ_res_apply (glued K t).presheaf _ _ _ f
  rw [← e, hf₁]
  exact stalkMap_germ_appIso_inv K t _ (ι₀ K t) (U₁ K t a) (σ₁ K t a) p hp

include hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in
private theorem stalkMap_germ_f_V₂ (q : XInf K t) (hq : q ∈ U₂ K t a) :
    (ιInf K t).stalkMap q ((glued K t).presheaf.germ (Ua K t a) ((ιInf K t).base q)
        (le_sup_right (α := (glued K t).Opens) ⟨q, hq, rfl⟩) f) =
      (XInf K t).presheaf.germ (U₂ K t a) q hq (σ₂ K t a) := by
  have e : (glued K t).presheaf.germ (V₂ K t a) ((ιInf K t).base q) ⟨q, hq, rfl⟩
      ((glued K t).presheaf.map (homOfLE (le_sup_right : V₂ K t a ≤ Ua K t a)).op f) =
      (glued K t).presheaf.germ (Ua K t a) ((ιInf K t).base q)
        (le_sup_right (α := (glued K t).Opens) ⟨q, hq, rfl⟩) f :=
    TopCat.Presheaf.germ_res_apply (glued K t).presheaf _ _ _ f
  rw [← e, hf₂]
  exact stalkMap_germ_appIso_inv K t _ (ιInf K t) (U₂ K t a) (σ₂ K t a) q hq

include hf₁ in
omit [FiniteDimensional K⟮t⟯ L] in
private theorem stalkMap_germ_fTwo_V₁ (p : X₀ K t) (hp : p ∈ U₁ K t a) :
    (ι₀ K t).stalkMap p ((glued K t).presheaf.germ (Ua K t a) ((ι₀ K t).base p)
        (le_sup_left (α := (glued K t).Opens) ⟨p, hp, rfl⟩) (fTwo K t a f)) =
      1 + algebraMap (chartRing K ({t} : Set L)) ((X₀ K t).presheaf.stalk p) (algebraMap K _ a) *
        (X₀ K t).presheaf.germ (U₁ K t a) p hp (σ₁ K t a) := by
  simp only [fTwo, map_add, map_one, map_mul]
  rw [stalkMap_germ_cSec K t _ (ι₀ K t) (ι₀_gluedToBase K t), stalkMap_germ_f_V₁ K t a f hf₁ p hp]

include hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in
private theorem stalkMap_germ_fTwo_V₂ (q : XInf K t) (hq : q ∈ U₂ K t a) :
    (ιInf K t).stalkMap q ((glued K t).presheaf.germ (Ua K t a) ((ιInf K t).base q)
        (le_sup_right (α := (glued K t).Opens) ⟨q, hq, rfl⟩) (fTwo K t a f)) =
      1 + algebraMap (chartRing K ({t⁻¹} : Set L)) ((XInf K t).presheaf.stalk q)
          (algebraMap K _ a) * (XInf K t).presheaf.germ (U₂ K t a) q hq (σ₂ K t a) := by
  simp only [fTwo, map_add, map_one, map_mul]
  rw [stalkMap_germ_cSec K t _ (ιInf K t) (ιInf_gluedToBase K t),
    stalkMap_germ_f_V₂ K t a f hf₂ q hq]

include hf₁ hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in
private theorem basicOpen_f : (glued K t).basicOpen f = V₁ K t a := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hunit⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hx
    rcases Opens.mem_sup.mp hxU with h₁ | h₂
    · exact h₁
    · obtain ⟨q, hq, hqx⟩ := h₂
      have hq' : q ∈ U₂ K t a := hq
      have hunit' : IsUnit ((glued K t).presheaf.germ (Ua K t a) ((ιInf K t).base q)
          (le_sup_right (α := (glued K t).Opens) ⟨q, hq', rfl⟩) f) := by
        subst hqx; exact hunit
      have hu := (isUnit_stalkMap_iff K t _ (ιInf K t) q _).mpr hunit'
      rw [stalkMap_germ_f_V₂ K t a f hf₂ q hq'] at hu
      have hg : IsUnit (algebraMap (chartRing K ({t⁻¹} : Set L)) ((XInf K t).presheaf.stalk q)
          (gInf K t a)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff ((XInf K t).presheaf.stalk q) q.asIdeal
          (gInf K t a)).mpr ((mem_U₂_iff K t a q).mp hq')
      have hu' := hu.mul hg
      rw [germ_σ₂_mul] at hu'
      have htinv : tInvChart K t ∉ q.asIdeal :=
        (IsLocalization.AtPrime.isUnit_to_map_iff ((XInf K t).presheaf.stalk q) q.asIdeal _).mp hu'
      obtain ⟨p, hp⟩ := (ιInf_mem_range_ι₀_iff K t q).mpr htinv
      rw [← hqx]
      refine ⟨p, ?_, hp⟩
      rw [SetLike.mem_coe, mem_U₁_iff, tma_not_mem_iff K t a p q hp, ← mem_U₂_iff]
      exact hq'
  · rintro x ⟨p, hp, hpx⟩
    have hp' : p ∈ U₁ K t a := hp
    subst hpx
    change (ι₀ K t).base p ∈ (glued K t).basicOpen f
    refine (Scheme.mem_basicOpen'' _ _ _).mpr
      ⟨le_sup_left (α := (glued K t).Opens) ⟨p, hp', rfl⟩, ?_⟩
    refine (isUnit_stalkMap_iff K t _ (ι₀ K t) p _).mp ?_
    rw [stalkMap_germ_f_V₁ K t a f hf₁ p hp']
    exact IsUnit.of_mul_eq_one _ (germ_σ₁_mul K t a p hp')

include hf₁ hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in
private theorem basicOpen_fTwo : (glued K t).basicOpen (fTwo K t a f) = V₂ K t a := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hunit⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hx
    rcases Opens.mem_sup.mp hxU with h₁ | h₂
    · obtain ⟨p, hp, hpx⟩ := h₁
      have hp' : p ∈ U₁ K t a := hp
      have hunit' : IsUnit ((glued K t).presheaf.germ (Ua K t a) ((ι₀ K t).base p)
          (le_sup_left (α := (glued K t).Opens) ⟨p, hp', rfl⟩) (fTwo K t a f)) := by
        subst hpx; exact hunit
      have hu := (isUnit_stalkMap_iff K t _ (ι₀ K t) p _).mpr hunit'
      rw [stalkMap_germ_fTwo_V₁ K t a f hf₁ p hp'] at hu
      have htma : IsUnit (algebraMap (chartRing K ({t} : Set L)) ((X₀ K t).presheaf.stalk p)
          (tma K t a)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff ((X₀ K t).presheaf.stalk p) p.asIdeal
          (tma K t a)).mpr ((mem_U₁_iff K t a p).mp hp')
      have hu' := hu.mul htma
      rw [add_mul, one_mul, mul_assoc, germ_σ₁_mul, mul_one, ← map_add, tma_add] at hu'
      have htc : tChart K t ∉ p.asIdeal :=
        (IsLocalization.AtPrime.isUnit_to_map_iff ((X₀ K t).presheaf.stalk p) p.asIdeal _).mp hu'
      obtain ⟨q, hq⟩ := (ι₀_mem_range_ιInf_iff K t p).mpr htc
      rw [← hpx]
      refine ⟨q, ?_, hq⟩
      rw [SetLike.mem_coe, mem_U₂_iff, ← tma_not_mem_iff K t a p q hq.symm, ← mem_U₁_iff]
      exact hp'
    · exact h₂
  · rintro x ⟨q, hq, hqx⟩
    have hq' : q ∈ U₂ K t a := hq
    subst hqx
    change (ιInf K t).base q ∈ (glued K t).basicOpen (fTwo K t a f)
    refine (Scheme.mem_basicOpen'' _ _ _).mpr
      ⟨le_sup_right (α := (glued K t).Opens) ⟨q, hq', rfl⟩, ?_⟩
    refine (isUnit_stalkMap_iff K t _ (ιInf K t) q _).mp ?_
    rw [stalkMap_germ_fTwo_V₂ K t a f hf₂ q hq']
    refine IsUnit.of_mul_eq_one (algebraMap _ ((XInf K t).presheaf.stalk q) (gInf K t a)) ?_
    rw [add_mul, one_mul, mul_assoc, germ_σ₂_mul, ← map_mul, ← map_add, gInf_add, map_one]

include hf₁ hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in
private theorem isAffineOpen_Ua_of : IsAffineOpen (Ua K t a) := by
  apply isAffineOpen_of_isAffineOpen_basicOpen (Ua K t a) {f, fTwo K t a f} (span_eq_top K t a f)
  intro g hg
  rcases hg with hg | hg
  · rw [hg, basicOpen_f K t a f hf₁ hf₂]; exact isAffineOpen_V₁ K t a
  · rw [Set.mem_singleton_iff.mp hg, basicOpen_fTwo K t a f hf₁ hf₂]; exact isAffineOpen_V₂ K t a

include ha in
theorem isAffineOpen_Ua : IsAffineOpen (Ua K t a) := by
  obtain ⟨f, hf₁, hf₂⟩ := exists_glued_section K t a ha
  exact isAffineOpen_Ua_of K t a f hf₁ hf₂

omit [FiniteDimensional K⟮t⟯ L] in
private theorem ιInf_mem_Ua (q : XInf K t) (hq : gInf K t a ∉ q.asIdeal) :
    (ιInf K t).base q ∈ Ua K t a :=
  Opens.mem_sup.mpr (Or.inr ⟨q, (mem_U₂_iff K t a q).mpr hq, rfl⟩)

omit [FiniteDimensional K⟮t⟯ L] in
private theorem ι₀_mem_Ua (p : X₀ K t) (hp : tma K t a ∉ p.asIdeal) : (ι₀ K t).base p ∈ Ua K t a :=
  Opens.mem_sup.mpr (Or.inl ⟨p, (mem_U₁_iff K t a p).mpr hp, rfl⟩)

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in
private theorem subsingleton_gInf_mem (q : XInf K t) :
    {a : K | gInf K t a ∈ q.asIdeal}.Subsingleton := by
  intro a ha' b hb'
  by_contra hab
  have hsub : gInf K t b - gInf K t a = algebraMap K _ (a - b) * tInvChart K t := by
    rw [gInf, gInf, map_sub]; ring
  have hmem : algebraMap K _ (a - b) * tInvChart K t ∈ q.asIdeal := hsub ▸ q.asIdeal.sub_mem hb' ha'
  have hunit : IsUnit (algebraMap K (chartRing K ({t⁻¹} : Set L)) (a - b)) :=
    (IsUnit.mk0 _ (sub_ne_zero.mpr hab)).map _
  have htinv : tInvChart K t ∈ q.asIdeal := by
    rcases q.isPrime.mem_or_mem hmem with h | h
    · exact absurd (q.asIdeal.eq_top_of_isUnit_mem h hunit) q.isPrime.ne_top
    · exact h
  have h1 : (1 : chartRing K ({t⁻¹} : Set L)) ∈ q.asIdeal := by
    have := q.asIdeal.add_mem ha' (q.asIdeal.mul_mem_left (algebraMap K _ a) htinv)
    rwa [gInf, sub_add_cancel] at this
  exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

omit [FiniteDimensional K⟮t⟯ L] in
private theorem finite_setOf_not_mem_Ua (x : glued K t) : {a : K | x ∉ Ua K t a}.Finite := by
  have hInf : ∀ q : XInf K t, {a : K | (ιInf K t).base q ∉ Ua K t a}.Finite := fun q =>
    (subsingleton_gInf_mem K t q).finite.subset fun a ha' => by
      by_contra h
      exact ha' (ιInf_mem_Ua K t a q h)
  rcases mem_range_ι₀_or_mem_range_ιInf K t x with ⟨p, hpx⟩ | ⟨q, hqx⟩
  · by_cases htc : tChart K t ∈ p.asIdeal
    · refine (Set.finite_singleton (0 : K)).subset fun a ha' => ?_
      by_contra h0
      apply ha'
      rw [← hpx]
      apply ι₀_mem_Ua
      intro hmem
      have hal : algebraMap K _ a ∈ p.asIdeal := by
        have := p.asIdeal.sub_mem htc hmem
        rwa [← tma_add K t a, add_sub_cancel_left] at this
      exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hal ((IsUnit.mk0 _ h0).map _))
    · obtain ⟨q, hq⟩ := (ι₀_mem_range_ιInf_iff K t p).mpr htc
      rw [← hpx, ← hq]
      exact hInf q
  · rw [← hqx]
    exact hInf q

end Affine

section Packaging

variable [Infinite K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]

/-- **Finite sets of points lie in affine opens.** For an infinite field `K` and nonzero `t` with
`L` finite over `K(t)`, every finite set of points of the glued scheme lies in an affine open. -/
public theorem finset_subset_affineOpen_glued :
    ∀ F : Finset (glued K t), ∃ U : (glued K t).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  intro F
  have hfin : ((⋃ x ∈ (F : Set (glued K t)), {a : K | x ∉ Ua K t a}) ∪
      {a : K | t - algebraMap K L a = 0}).Finite := by
    refine (F.finite_toSet.biUnion fun x _ => finite_setOf_not_mem_Ua K t x).union ?_
    refine Set.Subsingleton.finite fun a ha' b hb' => ?_
    apply (algebraMap K L).injective
    have ha'' : t - algebraMap K L a = 0 := ha'
    have hb'' : t - algebraMap K L b = 0 := hb'
    rw [sub_eq_zero] at ha'' hb''
    rw [← ha'', ← hb'']
  obtain ⟨a, ha⟩ := hfin.exists_notMem
  refine ⟨Ua K t a, isAffineOpen_Ua K t a (fun h => ha (Or.inr h)), fun x hx => ?_⟩
  by_contra h
  exact ha (Or.inl (Set.mem_iUnion₂.mpr ⟨x, Finset.mem_coe.mpr hx, h⟩))

end Packaging

end CurveModel

end AlgebraicCurve
