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

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import MathlibExt.AlgebraicGeometry.Curve.GluedCharts
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Properness of the two-chart model

For nonzero `t` with `L` finite and separable over `K(t)`, the two-chart scheme
`AlgebraicCurve.CurveModel.glued K t` is proper over `Spec K`
(`AlgebraicCurve.CurveModel.isProper_gluedToBase`): it is quasi-compact and quasi-separated of
finite type, and satisfies the existence and uniqueness parts of the valuative criterion.
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

open IsLocalRing

section Compact

variable [Fact (t ≠ 0)]

instance compactSpace_glued : CompactSpace (glued K t) := by
  refine ⟨?_⟩
  have h : Set.range (ι₀ K t).base ∪ Set.range (ιInf K t).base = Set.univ :=
    Set.eq_univ_of_forall fun x => mem_range_ι₀_or_mem_range_ιInf K t x
  rw [← h]
  exact (isCompact_range (ι₀ K t).base.hom.continuous).union
    (isCompact_range (ιInf K t).base.hom.continuous)

instance quasiCompact_gluedToBase : QuasiCompact (gluedToBase K t) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

end Compact

section Noetherian

variable [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L]

instance isLocallyNoetherian_glued : IsLocallyNoetherian (glued K t) := by
  refine (isLocallyNoetherian_iff_openCover (X := glued K t)
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t)))).mpr ?_
  rintro (_ | _ | _)
  · change IsLocallyNoetherian (XOverlap K t)
    have : IsNoetherianRing (chartRing K ({t, t⁻¹} : Set L)) := by
      let := (incl₀ K t).toRingHom.toAlgebra
      have := isLocalization_away_incl₀ K t (Fact.out : t ≠ 0)
      exact IsLocalization.isNoetherianRing (Submonoid.powers (tChart K t)) _ inferInstance
    infer_instance
  · change IsLocallyNoetherian (X₀ K t)
    infer_instance
  · change IsLocallyNoetherian (XInf K t)
    infer_instance

instance quasiSeparated_gluedToBase : QuasiSeparated (gluedToBase K t) :=
  QuasiSeparated.of_quasiSeparatedSpace _

end Noetherian

section RingLemmas

variable {B R F : Type*} [CommRing B] [CommRing R] [CommRing F]

/-- A ring map with values in the range of an injective ring map `j`, lifted through `j`. -/
private def liftOfRange (j : R →+* F) (hj : Function.Injective j) (g : B →+* F)
    (h : ∀ b, g b ∈ j.range) : B →+* R :=
  (RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩).symm.toRingHom.comp
    (g.codRestrict j.range h)

private theorem liftOfRange_spec (j : R →+* F) (hj : Function.Injective j) (g : B →+* F)
    (h : ∀ b, g b ∈ j.range) (b : B) : j (liftOfRange j hj g h b) = g b := by
  set e := RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩
  have : e (e.symm ⟨g b, h b⟩) = ⟨g b, h b⟩ := e.apply_symm_apply _
  exact congrArg Subtype.val this

end RingLemmas

section SpecLemmas

private theorem SpecMap_cancel {R F Y : CommRingCat.{u}} (j : R ⟶ F) (hj : Function.Injective j)
    (u v : Spec R ⟶ Spec Y) (h : Spec.map j ≫ u = Spec.map j ≫ v) : u = v := by
  have : Mono j := ConcreteCategory.mono_of_injective j hj
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [cancel_mono] at h'
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, h']

private theorem fromSpecStalk_comp {X : Scheme.{u}} {A : CommRingCat.{u}} (f : X ⟶ Spec A) (x : X) :
    X.fromSpecStalk x ≫ f =
      Spec.map (StructureSheaf.toStalk A (f.base x) ≫ f.stalkMap x) := by
  rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq']
  rfl

end SpecLemmas

section LiftLemma

variable [Fact (t ≠ 0)]

private theorem exists_eq_SpecMap_comp_fromSpecStalk {F : Type u} [Field F]
    (f : Spec (.of F) ⟶ glued K t)
    {x : glued K t} (hx : f.base (closedPoint F) = x) :
    ∃ φ : (glued K t).presheaf.stalk x ⟶ CommRingCat.of F,
      IsLocalHom φ.hom ∧ f = Spec.map φ ≫ (glued K t).fromSpecStalk x := by
  subst hx
  exact ⟨_, inferInstance, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk f).symm⟩

private theorem hasLift_of_range (S : ValuativeCommSq (gluedToBase K t)) {x P : glued K t}
    (hsp : x ⤳ P)
    (φ : (glued K t).presheaf.stalk x ⟶ CommRingCat.of S.K)
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk x)
    (hrange : ∀ s : (glued K t).presheaf.stalk P,
      φ ((glued K t).presheaf.stalkSpecializes hsp s) ∈ (algebraMap S.R S.K).range) :
    S.commSq.HasLift := by
  let ψ : (glued K t).presheaf.stalk P →+* S.R :=
    liftOfRange (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K)
      (φ.hom.comp ((glued K t).presheaf.stalkSpecializes hsp).hom) hrange
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap S.R S.K) =
      (glued K t).presheaf.stalkSpecializes hsp ≫ φ := by
    ext s
    exact liftOfRange_spec (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) _ hrange s
  let l : Spec (.of S.R) ⟶ glued K t := Spec.map (CommRingCat.ofHom ψ) ≫ (glued K t).fromSpecStalk P
  have fac_left : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁ := by
    rw [h₁, ← Spec.map_comp_assoc, hψ, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  refine CommSq.HasLift.mk' ⟨l, fac_left, ?_⟩
  apply SpecMap_cancel (CommRingCat.ofHom (algebraMap S.R S.K)) (IsFractionRing.injective S.R S.K)
  rw [← Category.assoc, fac_left, S.commSq.w]

private theorem ringCompat (S : ValuativeCommSq (gluedToBase K t)) {x : glued K t}
    (φ : (glued K t).presheaf.stalk x ⟶ CommRingCat.of S.K)
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk x) :
    (StructureSheaf.toStalk (CommRingCat.of K) ((gluedToBase K t).base x) ≫
        (gluedToBase K t).stalkMap x) ≫ φ =
      Spec.preimage S.i₂ ≫ CommRingCat.ofHom (algebraMap S.R S.K) := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← fromSpecStalk_comp, Spec.map_comp, Spec.map_preimage, ← Category.assoc,
    ← h₁]
  exact S.commSq.w

end LiftLemma

section Generic

variable [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L]

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem stalkMap_toStalk_genericPoint (a : K) :
    (gluedToBase K t).stalkMap (genericPoint (glued K t))
        (StructureSheaf.toStalk (CommRingCat.of K) _ a) =
      baseToFunctionField (gluedToBase K t) a := by
  change (gluedToBase K t).stalkMap (genericPoint (glued K t))
      ((Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

variable (S : ValuativeCommSq (gluedToBase K t))
  (φ : (glued K t).presheaf.stalk (genericPoint (glued K t)) ⟶ CommRingCat.of S.K)

/-- The map from `L` to the fraction field of a valuative square, through the generic stalk. -/
private def gL : L →+* S.K := φ.hom.comp (gluedFunctionFieldEquiv K t).toRingHom

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem gL_ffEquiv_symm (y : (glued K t).functionField) :
    gL K t S φ ((gluedFunctionFieldEquiv K t).symm y) = φ y :=
  congrArg φ.hom ((gluedFunctionFieldEquiv K t).apply_symm_apply y)

/-- The valuation subring of `L` pulled back from the valuation ring of a valuative square. -/
private def pullbackVS : ValuationSubring L where
  toSubring := (algebraMap S.R S.K).range.comap (gL K t S φ)
  mem_or_inv_mem' y := by
    rcases ValuationRing.isInteger_or_isInteger S.R (gL K t S φ y) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r, hr⟩
    · exact Or.inr ⟨r, by rw [map_inv₀]; exact hr⟩

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem mem_pullbackVS_iff (y : L) :
    y ∈ pullbackVS K t S φ ↔ gL K t S φ y ∈ (algebraMap S.R S.K).range := Iff.rfl

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem algebraMap_mem_pullbackVS
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (genericPoint (glued K t))) (a : K) :
    algebraMap K L a ∈ pullbackVS K t S φ := by
  rw [mem_pullbackVS_iff]
  refine ⟨(Spec.preimage S.i₂).hom a, ?_⟩
  have h : φ ((gluedToBase K t).stalkMap (genericPoint (glued K t))
      (StructureSheaf.toStalk (CommRingCat.of K) _ a)) =
      algebraMap S.R S.K ((Spec.preimage S.i₂).hom a) :=
    congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of S.K => f a) (ringCompat K t S φ h₁)
  rw [stalkMap_toStalk_genericPoint] at h
  change _ = φ ((gluedFunctionFieldEquiv K t) (algebraMap K L a))
  rw [gluedFunctionFieldEquiv_algebraMap, h]

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem hasLift_generic_top
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (genericPoint (glued K t)))
    (hO : pullbackVS K t S φ = ⊤) : S.commSq.HasLift := by
  refine hasLift_of_range K t S (specializes_refl _) φ h₁ fun u => ?_
  have hu : (gluedFunctionFieldEquiv K t).symm
      ((glued K t).presheaf.stalkSpecializes (specializes_refl _) u) ∈ pullbackVS K t S φ := by
    rw [hO]; trivial
  rwa [mem_pullbackVS_iff, gL_ffEquiv_symm] at hu

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem hasLift_generic_centre (s : L) [FiniteDimensional K⟮s⟯ L]
    [Algebra.IsSeparable K⟮s⟯ L]
    (i : chartRing K ({s} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L))
    (hi : ∀ a : chartRing K ({s} : Set L), (i a : L) = a)
    (ιA : Spec (CommRingCat.of (chartRing K ({s} : Set L))) ⟶ glued K t) [IsOpenImmersion ιA]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
    (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (genericPoint (glued K t)))
    (hO : pullbackVS K t S φ ≠ ⊤) (hs : s ∈ pullbackVS K t S φ) : S.commSq.HasLift := by
  let 𝔮 := primeOfValuationSubring K s (pullbackVS K t S φ) (algebraMap_mem_pullbackVS K t S φ h₁)
    hs hO
  let q : Spec (CommRingCat.of (chartRing K ({s} : Set L))) := ⟨𝔮.asIdeal, 𝔮.isPrime⟩
  refine hasLift_of_range K t S (genericPoint_specializes (ιA.base q)) φ h₁ fun u => ?_
  have hmem : (gluedFunctionFieldEquiv K t).symm
      (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField u) ∈
        pullbackVS K t S φ := by
    have hr : (gluedFunctionFieldEquiv K t).symm
        (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField u) ∈
        ((((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
          (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField)).range :
            Set L) := ⟨u, rfl⟩
    rw [range_ffEquiv_symm_comp_algebraMap_stalk K t (chartRing K ({s} : Set L)) i hi ιA comm q]
      at hr
    obtain ⟨a, b, hb, e⟩ := hr
    rw [e]
    apply valuationSubringAtPrime_le K s (pullbackVS K t S φ)
      (algebraMap_mem_pullbackVS K t S φ h₁) hs hO
    exact ⟨a, b, hb, rfl⟩
  rw [mem_pullbackVS_iff, gL_ffEquiv_symm] at hmem
  exact hmem

private theorem hasLift_generic (hgen : S.i₁.base (closedPoint S.K) = genericPoint (glued K t)) :
    S.commSq.HasLift := by
  obtain ⟨φ, -, h₁⟩ := exists_eq_SpecMap_comp_fromSpecStalk K t S.i₁ hgen
  by_cases hO : pullbackVS K t S φ = ⊤
  · exact hasLift_generic_top K t S φ h₁ hO
  · rcases (pullbackVS K t S φ).mem_or_inv_mem t with ht | ht
    · exact hasLift_generic_centre K t S φ t (incl₀ K t) (fun a => coe_chartIncl K _ a) (ι₀ K t)
        rfl h₁ hO ht
    · exact hasLift_generic_centre K t S φ t⁻¹ (inclInf K t) (fun a => coe_chartIncl K _ a)
        (ιInf K t) (glue_condition K t).symm h₁ hO ht

end Generic

section Closed

variable [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L]

variable (A : Subalgebra K L) (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
  (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
  (S : ValuativeCommSq (gluedToBase K t)) (p : Spec (CommRingCat.of A))
  (φ : (glued K t).presheaf.stalk (ιA.base p) ⟶ CommRingCat.of S.K)

/-- For an open immersion `ιA` of `Spec A` into the glued scheme, the isomorphism between the
stalk of the glued scheme at `ιA p` and the stalk of `Spec A` at `p`. -/
def stalkChartEquiv :
    (glued K t).presheaf.stalk (ιA.base p) ≃+* (Spec (CommRingCat.of A)).presheaf.stalk p :=
  (asIso (ιA.stalkMap p)).commRingCatIsoToRingEquiv

/-- The map from the stalk of the chart `Spec A` at `p` to the fraction field of the square. -/
private def φA : (Spec (CommRingCat.of A)).presheaf.stalk p →+* S.K :=
  φ.hom.comp (stalkChartEquiv K t A ιA p).symm.toRingHom

/-- The map from `A` to the fraction field of the square, through the stalk at `p`. -/
private def gA : A →+* S.K := (φA K t A ιA S p φ).comp (StructureSheaf.toStalk A p).hom

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem φA_stalkMap (y : (glued K t).presheaf.stalk (ιA.base p)) :
    φA K t A ιA S p φ (ιA.stalkMap p y) = φ y := by
  change φ ((stalkChartEquiv K t A ιA p).symm ((stalkChartEquiv K t A ιA p) y)) = φ y
  rw [RingEquiv.symm_apply_apply]

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] [IsOpenImmersion ιA] in
include ιA_toBase in
theorem stalkMap_chart_toStalk (a : K) :
    ιA.stalkMap p ((gluedToBase K t).stalkMap (ιA.base p)
        (StructureSheaf.toStalk (CommRingCat.of K) _ a)) =
      StructureSheaf.toStalk A p (algebraMap K A a) := by
  change ιA.stalkMap p ((gluedToBase K t).stalkMap (ιA.base p)
      ((Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))) = _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
  change (Spec (CommRingCat.of A)).presheaf.germ ⊤ p trivial
      ((ιA ≫ gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) = _
  rw [ιA_toBase]
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap K A a) := by
    have := congrArg (fun f : CommRingCat.of K ⟶ Γ(Spec (CommRingCat.of A), ⊤) => f a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K A)))
    exact this.symm
  rw [h1]
  rfl

include ιA_toBase in
omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem gA_algebraMap (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (ιA.base p))
    (a : K) :
    gA K t A ιA S p φ (algebraMap K A a) =
      algebraMap S.R S.K ((Spec.preimage S.i₂).hom a) := by
  have h : φ ((gluedToBase K t).stalkMap (ιA.base p)
      (StructureSheaf.toStalk (CommRingCat.of K) _ a)) =
      algebraMap S.R S.K ((Spec.preimage S.i₂).hom a) :=
    congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of S.K => f a) (ringCompat K t S φ h₁)
  rw [← h, ← φA_stalkMap K t A ιA S p φ, stalkMap_chart_toStalk K t A ιA ιA_toBase p a]
  rfl

variable [hmax : p.asIdeal.IsMaximal]

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] hmax in
private theorem gA_eq_zero [IsLocalHom φ.hom] (m : A) (hm : m ∈ p.asIdeal)
    : gA K t A ιA S p φ m = 0 := by
  have hloc₁ : IsLocalHom (stalkChartEquiv K t A ιA p).symm.toRingHom :=
    isLocalHom_of_leftInverse (stalkChartEquiv K t A ιA p).toRingHom
      fun x => (stalkChartEquiv K t A ιA p).apply_symm_apply x
  have hloc : IsLocalHom (φA K t A ιA S p φ) :=
    @RingHom.isLocalHom_comp _ _ _ _ _ _ φ.hom (stalkChartEquiv K t A ιA p).symm.toRingHom _ hloc₁
  by_contra h
  have hu : IsUnit (φA K t A ιA S p φ
      (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) m)) :=
    isUnit_iff_ne_zero.mpr h
  have hu' : IsUnit (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) m) :=
    @IsUnit.of_map _ _ _ _ _ _ (φA K t A ιA S p φ) hloc _ hu
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal m).mp hu' hm

include ιA_toBase in
omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem gA_mem_range [Algebra.FiniteType K A] [IsLocalHom φ.hom]
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (ιA.base p)) (a : A) :
    gA K t A ιA S p φ a ∈ (algebraMap S.R S.K).range := by
  let := Ideal.Quotient.field p.asIdeal
  have : Module.Finite K (A ⧸ p.asIdeal) := finite_of_finite_type_of_isJacobsonRing K _
  have : IsIntegrallyClosed S.R := GCDMonoid.toIsIntegrallyClosed
  let β : K →+* S.R := (Spec.preimage S.i₂).hom
  let gbar : A ⧸ p.asIdeal →+* S.K :=
    Ideal.Quotient.lift p.asIdeal (gA K t A ιA S p φ) (gA_eq_zero K t A ιA S p φ)
  have hg : gA K t A ιA S p φ a = gbar (Ideal.Quotient.mk p.asIdeal a) :=
    (Ideal.Quotient.lift_mk _ _ _).symm
  have hcomp : (algebraMap S.R S.K).comp β = gbar.comp (algebraMap K (A ⧸ p.asIdeal)) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.lift_mk]
    exact (gA_algebraMap K t A ιA ιA_toBase S p φ h₁ c).symm
  obtain ⟨f, hf, hfa⟩ : IsIntegral K (Ideal.Quotient.mk p.asIdeal a) :=
    Algebra.IsIntegral.isIntegral _
  have hint : IsIntegral S.R (gA K t A ιA S p φ a) := by
    refine ⟨f.map β, hf.map β, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, hg, ← Polynomial.hom_eval₂]
    change gbar (Polynomial.eval₂ (algebraMap K (A ⧸ p.asIdeal)) _ f) = 0
    rw [hfa, map_zero]
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hint

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem exists_gA_mul_gA_eq_one [IsLocalHom φ.hom] (b : A) (hb : b ∉ p.asIdeal) :
    ∃ c : A, gA K t A ιA S p φ b * gA K t A ιA S p φ c = 1 := by
  let := Ideal.Quotient.field p.asIdeal
  have hb0 : Ideal.Quotient.mk p.asIdeal b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk p.asIdeal b)⁻¹
  refine ⟨c, ?_⟩
  let gbar : A ⧸ p.asIdeal →+* S.K :=
    Ideal.Quotient.lift p.asIdeal (gA K t A ιA S p φ) (gA_eq_zero K t A ιA S p φ)
  have e : ∀ x : A, gA K t A ιA S p φ x = gbar (Ideal.Quotient.mk p.asIdeal x) := fun x =>
    (Ideal.Quotient.lift_mk _ _ _).symm
  rw [e, e, ← map_mul, hc, mul_inv_cancel₀ hb0, map_one]

include ιA_toBase in
omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem φ_mem_range [Algebra.FiniteType K A] [IsLocalHom φ.hom]
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (ιA.base p))
    (s : (glued K t).presheaf.stalk (ιA.base p)) : φ s ∈ (algebraMap S.R S.K).range := by
  obtain ⟨y, rfl⟩ : ∃ y, (stalkChartEquiv K t A ιA p).symm y = s :=
    ⟨stalkChartEquiv K t A ιA p s, RingEquiv.symm_apply_apply _ _⟩
  change φA K t A ιA S p φ y ∈ _
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl y
  obtain ⟨c, hc⟩ := exists_gA_mul_gA_eq_one K t A ιA S p φ b b.2
  have hspec := congrArg (φA K t A ιA S p φ)
    (IsLocalization.mk'_spec ((Spec (CommRingCat.of A)).presheaf.stalk p) a b)
  rw [map_mul] at hspec
  have hspec' : φA K t A ιA S p φ (IsLocalization.mk' _ a b) * gA K t A ιA S p φ b =
      gA K t A ιA S p φ a := hspec
  have key : φA K t A ιA S p φ (IsLocalization.mk' _ a b) =
      gA K t A ιA S p φ a * gA K t A ιA S p φ c := by
    calc φA K t A ιA S p φ (IsLocalization.mk' _ a b)
        = φA K t A ιA S p φ (IsLocalization.mk' _ a b) *
            (gA K t A ιA S p φ b * gA K t A ιA S p φ c) := by rw [hc, mul_one]
      _ = (φA K t A ιA S p φ (IsLocalization.mk' _ a b) * gA K t A ιA S p φ b) *
            gA K t A ιA S p φ c := by ring
      _ = gA K t A ιA S p φ a * gA K t A ιA S p φ c := by rw [hspec']
  rw [key]
  exact Subring.mul_mem _ (gA_mem_range K t A ιA ιA_toBase S p φ h₁ a)
    (gA_mem_range K t A ιA ιA_toBase S p φ h₁ c)

end Closed

section ClosedLift

variable [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L]

omit [Algebra.IsSeparable K⟮t⟯ L] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    [Algebra.IsSeparable K⟮t⁻¹⟯ L] in
private theorem hasLift_closed (A : Subalgebra K L) [Algebra.FiniteType K A]
    (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
    (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (S : ValuativeCommSq (gluedToBase K t)) (p : Spec (CommRingCat.of A))
    (hp : S.i₁.base (closedPoint S.K) = ιA.base p) (hmax : p.asIdeal.IsMaximal) :
    S.commSq.HasLift := by
  obtain ⟨φ, hloc, h₁⟩ := exists_eq_SpecMap_comp_fromSpecStalk K t S.i₁ hp
  have := hloc
  have := hmax
  exact hasLift_of_range K t S (specializes_refl _) φ h₁ fun s =>
    φ_mem_range K t A ιA ιA_toBase S p φ h₁ _

/-- For nonzero `t` with `L` finite and separable over `K(t)`, the structure morphism of the glued
scheme satisfies the existence part of the valuative criterion. -/
theorem valuativeCriterion_existence : ValuativeCriterion.Existence (gluedToBase K t) := by
  intro S
  rcases mem_range_ι₀_or_mem_range_ιInf K t (S.i₁.base (closedPoint S.K)) with ⟨p, hp⟩ | ⟨q, hq⟩
  · by_cases hbot : p.asIdeal = ⊥
    · refine hasLift_generic K t S ?_
      have hη : p = genericPoint (X₀ K t) := by
        rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext hbot
      rw [← hp, hη]
      exact genericPoint_eq_of_isOpenImmersion (ι₀ K t)
    · exact hasLift_closed K t (chartRing K ({t} : Set L)) (ι₀ K t) (ι₀_gluedToBase K t) S p
        hp.symm (Ideal.IsPrime.isMaximal p.isPrime hbot)
  · by_cases hbot : q.asIdeal = ⊥
    · refine hasLift_generic K t S ?_
      have hη : q = genericPoint (XInf K t) := by
        rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext hbot
      rw [← hq, hη]
      exact genericPoint_eq_of_isOpenImmersion (ιInf K t)
    · exact hasLift_closed K t (chartRing K ({t⁻¹} : Set L)) (ιInf K t) (ιInf_gluedToBase K t) S q
        hq.symm (Ideal.IsPrime.isMaximal q.isPrime hbot)

end ClosedLift

section Uniqueness

variable [Fact (t ≠ 0)]

private theorem range_subset_of_closedPoint_mem {R : Type u} [CommRing R] [IsLocalRing R]
    (l : Spec (CommRingCat.of R) ⟶ glued K t) {X : Scheme.{u}} (ι : X ⟶ glued K t)
    [IsOpenImmersion ι] (h : l.base (closedPoint R) ∈ Set.range ι.base) :
    Set.range l.base ⊆ Set.range ι.base := by
  rintro _ ⟨z, rfl⟩
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem l (U := ι.opensRange) h
  have hz : z ∈ l ⁻¹ᵁ ι.opensRange := by rw [htop]; trivial
  exact hz

private theorem liftStruct_eq_of_mem_range {A : Type u} [CommRing A]
    (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
    (S : ValuativeCommSq (gluedToBase K t)) (l₁ l₂ : S.commSq.LiftStruct)
    (h₁ : l₁.l.base (closedPoint S.R) ∈ Set.range ιA.base)
    (h₂ : l₂.l.base (closedPoint S.R) ∈ Set.range ιA.base) : l₁ = l₂ := by
  have H₁ := range_subset_of_closedPoint_mem K t l₁.l ιA h₁
  have H₂ := range_subset_of_closedPoint_mem K t l₂.l ιA h₂
  let m₁ := IsOpenImmersion.lift ιA l₁.l H₁
  let m₂ := IsOpenImmersion.lift ιA l₂.l H₂
  have e₁ : m₁ ≫ ιA = l₁.l := IsOpenImmersion.lift_fac _ _ _
  have e₂ : m₂ ≫ ιA = l₂.l := IsOpenImmersion.lift_fac _ _ _
  have hF : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ m₁ =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ m₂ := by
    rw [← cancel_mono ιA, Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
  have : Mono (CommRingCat.ofHom (algebraMap S.R S.K)) :=
    ConcreteCategory.mono_of_injective _ (IsFractionRing.injective S.R S.K)
  have hm : m₁ = m₂ := by
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂, ← Spec.map_comp, ← Spec.map_comp] at hF
    have := Spec.map_injective hF
    rw [cancel_mono] at this
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂, this]
  ext
  rw [← e₁, ← e₂, hm]

theorem incl₀_tChart_mul_inclInf_tInvChart :
    incl₀ K t (tChart K t) * inclInf K t (tInvChart K t) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_tChart, coe_tInvChart,
      Subalgebra.coe_one, mul_inv_cancel₀ (Fact.out : t ≠ 0)])

private theorem false_of_liftStruct_cross (S : ValuativeCommSq (gluedToBase K t))
    (l₁ l₂ : S.commSq.LiftStruct)
    (h₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ι₀ K t).base)
    (h₁' : l₁.l.base (closedPoint S.R) ∉ Set.range (ιInf K t).base)
    (h₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιInf K t).base)
    (h₂' : l₂.l.base (closedPoint S.R) ∉ Set.range (ι₀ K t).base) : False := by
  have H₁ := range_subset_of_closedPoint_mem K t l₁.l (ι₀ K t) h₁
  have H₂ := range_subset_of_closedPoint_mem K t l₂.l (ιInf K t) h₂
  let G₁ : CommRingCat.of (chartRing K ({t} : Set L)) ⟶ CommRingCat.of S.R :=
    Spec.preimage (IsOpenImmersion.lift (ι₀ K t) l₁.l H₁)
  let G₂ : CommRingCat.of (chartRing K ({t⁻¹} : Set L)) ⟶ CommRingCat.of S.R :=
    Spec.preimage (IsOpenImmersion.lift (ιInf K t) l₂.l H₂)
  have e₁ : Spec.map G₁ ≫ ι₀ K t = l₁.l := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  have e₂ : Spec.map G₂ ≫ ιInf K t = l₂.l := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  have ht₁ : G₁ (tChart K t) ∈ maximalIdeal S.R := by
    by_contra hn
    apply h₁'
    rw [← e₁, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ι₀_mem_range_ιInf_iff]
    exact hn
  have ht₂ : G₂ (tInvChart K t) ∈ maximalIdeal S.R := by
    by_contra hn
    apply h₂'
    rw [← e₂, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ιInf_mem_range_ι₀_iff]
    exact hn
  let alg := CommRingCat.ofHom (algebraMap S.R S.K)
  have hov : Set.range (Spec.map alg ≫ Spec.map G₁).base ⊆ Set.range (f₀ K t).base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = closedPoint S.K := Subsingleton.elim _ _
    have hx : (ι₀ K t).base ((Spec.map alg ≫ Spec.map G₁).base (closedPoint S.K)) ∈
        Set.range (ιInf K t).base := by
      refine ⟨(Spec.map alg ≫ Spec.map G₂).base (closedPoint S.K), ?_⟩
      change ((Spec.map alg ≫ Spec.map G₂) ≫ ιInf K t).base (closedPoint S.K) =
        ((Spec.map alg ≫ Spec.map G₁) ≫ ι₀ K t).base (closedPoint S.K)
      rw [Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
    rw [ι₀_mem_range_ιInf_iff] at hx
    rw [range_f₀]
    exact hx
  let u := IsOpenImmersion.lift (f₀ K t) (Spec.map alg ≫ Spec.map G₁) hov
  have hu₀ : u ≫ f₀ K t = Spec.map alg ≫ Spec.map G₁ := IsOpenImmersion.lift_fac _ _ _
  have hui : u ≫ fInf K t = Spec.map alg ≫ Spec.map G₂ := by
    rw [← cancel_mono (ιInf K t), Category.assoc, ← glue_condition, ← Category.assoc, hu₀,
      Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
  let W := Spec.preimage u
  have hW₀ : CommRingCat.ofHom (incl₀ K t).toRingHom ≫ W = G₁ ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hu₀
  have hWi : CommRingCat.ofHom (inclInf K t).toRingHom ≫ W = G₂ ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hui
  have k₁ : W (incl₀ K t (tChart K t)) = algebraMap S.R S.K (G₁ (tChart K t)) :=
    congrArg (fun f : CommRingCat.of (chartRing K ({t} : Set L)) ⟶ CommRingCat.of S.K =>
      f (tChart K t)) hW₀
  have k₂ : W (inclInf K t (tInvChart K t)) = algebraMap S.R S.K (G₂ (tInvChart K t)) :=
    congrArg (fun f : CommRingCat.of (chartRing K ({t⁻¹} : Set L)) ⟶ CommRingCat.of S.K =>
      f (tInvChart K t)) hWi
  have hone : algebraMap S.R S.K (G₁ (tChart K t) * G₂ (tInvChart K t)) = algebraMap S.R S.K 1 := by
    rw [map_mul, map_one, ← k₁, ← k₂, ← map_mul, incl₀_tChart_mul_inclInf_tInvChart, map_one]
  have hone' := IsFractionRing.injective S.R S.K hone
  exact (maximalIdeal S.R).ne_top_iff_one.mp (maximalIdeal.isMaximal S.R).ne_top
    (hone' ▸ Ideal.mul_mem_right _ _ ht₁)

/-- For nonzero `t`, the structure morphism of the glued scheme satisfies the uniqueness part of the
valuative criterion. -/
theorem valuativeCriterion_uniqueness : ValuativeCriterion.Uniqueness (gluedToBase K t) := by
  intro S
  refine ⟨fun l₁ l₂ => ?_⟩
  by_cases a₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ι₀ K t).base <;>
    by_cases a₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ι₀ K t).base
  · exact liftStruct_eq_of_mem_range K t (ι₀ K t) S l₁ l₂ a₁ a₂
  · have b₂ := mem_range_ιInf_of_not_mem_range_ι₀ K t a₂
    by_cases b₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ιInf K t).base
    · exact liftStruct_eq_of_mem_range K t (ιInf K t) S l₁ l₂ b₁ b₂
    · exact (false_of_liftStruct_cross K t S l₁ l₂ a₁ b₁ b₂ a₂).elim
  · have b₁ := mem_range_ιInf_of_not_mem_range_ι₀ K t a₁
    by_cases b₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιInf K t).base
    · exact liftStruct_eq_of_mem_range K t (ιInf K t) S l₁ l₂ b₁ b₂
    · exact (false_of_liftStruct_cross K t S l₂ l₁ a₂ b₂ b₁ a₁).elim
  · exact liftStruct_eq_of_mem_range K t (ιInf K t) S l₁ l₂
      (mem_range_ιInf_of_not_mem_range_ι₀ K t a₁) (mem_range_ιInf_of_not_mem_range_ι₀ K t a₂)

end Uniqueness

section Proper

variable [Algebra.IsSeparable K⟮t⟯ L] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    [FiniteDimensional K⟮t⁻¹⟯ L] [Algebra.IsSeparable K⟮t⁻¹⟯ L]

/-- For nonzero `t` with `L` finite and separable over `K(t)`, the glued scheme is proper over
`Spec K`. -/
instance isProper_gluedToBase : IsProper (gluedToBase K t) :=
  IsProper.of_valuativeCriterion (gluedToBase K t)
    ((ValuativeCriterion.iff).mpr
      ⟨valuativeCriterion_existence K t, valuativeCriterion_uniqueness K t⟩)

end Proper

end CurveModel

end AlgebraicCurve
