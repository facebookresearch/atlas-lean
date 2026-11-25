/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Ext.ShortExactRepresentatives
public import MathlibExt.Algebra.Homology.ShortComplex.PullbackShear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Classification of short exact extensions by Ext¹

The quotient by endpoint-fixing isomorphisms is in bijection with Ext¹.
Each extension is compared with a pullback of an injective presentation.
Equal Ext classes yield a correction map whose pullback shear fixes both
endpoints.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe e v u

namespace CategoryTheory.ShortExactSequence.WithEndpoints

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]
  [EnoughInjectives C]
variable {X Y : C}

/-- The injective presentation sequence of the fixed kernel. -/
abbrev injectiveSequence (Y : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y))
    (cokernel.condition (Injective.ι Y))

omit [HasExt.{e} C] in
theorem injectiveSequence_shortExact (Y : C) : (injectiveSequence Y).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι Y)) }

/-- A injective lift of the extension inclusion. -/
def comparisonLift (E : WithEndpoints X Y) : E.complex.X₂ ⟶ Injective.under Y := by
  letI : Mono E.complex.f := E.complex_shortExact.mono_f
  exact Injective.factorThru (Injective.ι Y) E.complex.f

omit [HasExt.{e} C] in
@[reassoc]
theorem comparisonLift_fac (E : WithEndpoints X Y) :
    E.complex.f ≫ comparisonLift E = Injective.ι Y := by
  let : Mono E.complex.f := E.complex_shortExact.mono_f
  exact Injective.comp_factorThru (Injective.ι Y) E.complex.f

/-- The descended map to the injective-presentation cokernel,
together with its primitive cokernel equation. -/
def comparisonCokernelData (E : WithEndpoints X Y) :
    { f : X ⟶ cokernel (Injective.ι Y) //
      E.complex.g ≫ f = comparisonLift E ≫ cokernel.π (Injective.ι Y) } :=
  CokernelCofork.IsColimit.desc' E.complex_shortExact.gIsCokernel
    (comparisonLift E ≫ cokernel.π (Injective.ι Y)) (by
      rw [← Category.assoc, comparisonLift_fac, cokernel.condition])

/-- The map `X ⟶ cokernel (Injective.ι Y)` descended from `comparisonLift E`:
the value of `comparisonCokernelData E`. -/
def comparisonCokernel (E : WithEndpoints X Y) : X ⟶ cokernel (Injective.ι Y) :=
  (comparisonCokernelData E).val

omit [HasExt.{e} C] in
@[reassoc]
theorem comparisonCokernel_fac (E : WithEndpoints X Y) :
    E.complex.g ≫ comparisonCokernel E =
      comparisonLift E ≫ cokernel.π (Injective.ι Y) :=
  (comparisonCokernelData E).property

/-- The comparison to the injective-presentation sequence. -/
def comparisonHom (E : WithEndpoints X Y) : E.complex ⟶ injectiveSequence Y where
  τ₁ := 𝟙 Y
  τ₂ := comparisonLift E
  τ₃ := comparisonCokernel E
  comm₁₂ := by
    simpa only [Category.id_comp] using (comparisonLift_fac E).symm
  comm₂₃ := (comparisonCokernel_fac E).symm

/-- Extension-class naturality identifies the connecting representative. -/
theorem extClass_comparison (E : WithEndpoints X Y) :
    extClass E =
      (Abelian.Ext.mk₀ (comparisonCokernel E)).comp
        (injectiveSequence_shortExact Y).extClass (zero_add 1) := by
  have h := ShortComplex.ShortExact.extClass_naturality
    E.complex_shortExact (injectiveSequence_shortExact Y) (comparisonHom E)
  dsimp only [comparisonHom] at h
  change (extClass E).comp (Abelian.Ext.mk₀ (𝟙 Y)) (add_zero 1) =
    (Abelian.Ext.mk₀ (comparisonCokernel E)).comp
      (injectiveSequence_shortExact Y).extClass (zero_add 1) at h
  simpa only [Abelian.Ext.comp_mk₀_id] using h

/-- The literal pullback comparison of the extension. -/
def comparisonPullHom (E : WithEndpoints X Y) :
    E.complex ⟶ (injectiveSequence Y).pull (comparisonCokernel E) where
  τ₁ := 𝟙 Y
  τ₂ := pullback.lift E.complex.g (comparisonLift E) (comparisonCokernel_fac E)
  τ₃ := 𝟙 X
  comm₁₂ := by
    apply pullback.hom_ext
    · simp only [ShortComplex.pull, Category.assoc,
        pullback.lift_fst, Category.id_comp]
      simpa only [Category.assoc] using E.complex.zero.symm
    · simp only [ShortComplex.pull, Category.assoc,
        pullback.lift_snd, Category.id_comp]
      simpa only [Category.assoc] using (comparisonLift_fac E).symm
  comm₂₃ := by
    simp only [ShortComplex.pull,
      pullback.lift_fst, Category.comp_id]

/-- The pullback comparison is an isomorphism fixing both endpoints. -/
def comparisonPullIso (E : WithEndpoints X Y) :
    E.complex ≅ (injectiveSequence Y).pull (comparisonCokernel E) := by
  let φ := comparisonPullHom E
  letI : IsIso φ.τ₁ := by change IsIso (𝟙 Y); infer_instance
  letI : IsIso φ.τ₃ := by change IsIso (𝟙 X); infer_instance
  letI : IsIso φ.τ₂ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ E.complex_shortExact
      ((injectiveSequence_shortExact Y).pull (comparisonCokernel E))
  exact ShortComplex.isoMk (Iso.refl Y) (asIso φ.τ₂) (Iso.refl X)
    φ.comm₁₂ φ.comm₂₃

omit [HasExt.{e} C] in
@[simp]
theorem comparisonPullIso_hom_τ₁ (E : WithEndpoints X Y) :
    (comparisonPullIso E).hom.τ₁ = 𝟙 Y := rfl

omit [HasExt.{e} C] in
@[simp]
theorem comparisonPullIso_hom_τ₃ (E : WithEndpoints X Y) :
    (comparisonPullIso E).hom.τ₃ = 𝟙 X := rfl

omit [HasExt.{e} C] in
@[simp]
theorem comparisonPullIso_inv_τ₁ (E : WithEndpoints X Y) :
    (comparisonPullIso E).inv.τ₁ = 𝟙 Y := rfl

omit [HasExt.{e} C] in
@[simp]
theorem comparisonPullIso_inv_τ₃ (E : WithEndpoints X Y) :
    (comparisonPullIso E).inv.τ₃ = 𝟙 X := rfl

/-- The scalar correction obtained from equality of extension classes. -/
theorem comparisonDifferenceFactors {E F : WithEndpoints X Y}
    (h : extClass E = extClass F) :
    ∃ a : X ⟶ Injective.under Y,
      a ≫ cokernel.π (Injective.ι Y) = comparisonCokernel E - comparisonCokernel F := by
  let S := injectiveSequence Y
  have hS : S.ShortExact := injectiveSequence_shortExact Y
  let δ : Abelian.Ext.{e} X (cokernel (Injective.ι Y)) 0 →+ Abelian.Ext.{e} X Y 1 :=
    hS.extClass.postcomp X (rfl : 0 + 1 = 1)
  have hmk :
      Abelian.Ext.mk₀ (comparisonCokernel E - comparisonCokernel F) =
        Abelian.Ext.mk₀ (comparisonCokernel E) -
          Abelian.Ext.mk₀ (comparisonCokernel F) :=
    (Abelian.Ext.addEquiv₀ (X := X) (Y := S.X₃)).symm.map_sub _ _
  have hz :
      δ (Abelian.Ext.mk₀ (comparisonCokernel E - comparisonCokernel F)) = 0 := by
    rw [hmk, map_sub]
    change
      (Abelian.Ext.mk₀ (comparisonCokernel E)).comp hS.extClass (rfl : 0 + 1 = 1) -
        (Abelian.Ext.mk₀ (comparisonCokernel F)).comp hS.extClass (rfl : 0 + 1 = 1) = 0
    rw [← extClass_comparison E, ← extClass_comparison F, h, sub_self]
  obtain ⟨z, hza⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS
    (Abelian.Ext.mk₀ (comparisonCokernel E - comparisonCokernel F)) rfl hz
  let a : X ⟶ Injective.under Y := Abelian.Ext.homEquiv₀ z
  have ha :
      Abelian.Ext.mk₀ (a ≫ S.g) =
        Abelian.Ext.mk₀ (comparisonCokernel E - comparisonCokernel F) := by
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    change
      (Abelian.Ext.mk₀ (Abelian.Ext.homEquiv₀ z)).comp
          (Abelian.Ext.mk₀ S.g) (zero_add 0) =
        Abelian.Ext.mk₀ (comparisonCokernel E - comparisonCokernel F)
    rw [Abelian.Ext.mk₀_homEquiv₀_apply]
    exact hza
  exact ⟨a, (Abelian.Ext.mk₀_bijective X S.X₃).injective ha⟩

/-- Equal Ext-one values imply the exact endpoint-fixing relation. -/
theorem rel_of_extClass_eq {E F : WithEndpoints X Y} (h : extClass E = extClass F) :
    Rel E F := by
  obtain ⟨a, ha⟩ := comparisonDifferenceFactors h
  let e := comparisonPullIso E ≪≫
    ShortComplex.pullShearIso (injectiveSequence Y) (comparisonCokernel E)
        (comparisonCokernel F) a ha ≪≫
      (comparisonPullIso F).symm
  refine ⟨e, ?_, ?_⟩
  · simp only [e, Iso.trans_hom, ShortComplex.comp_τ₁,
      comparisonPullIso_hom_τ₁, ShortComplex.pullShearIso_hom_τ₁, Iso.symm_hom,
      comparisonPullIso_inv_τ₁, Category.id_comp]
    exact Category.id_comp (𝟙 _)
  · simp only [e, Iso.trans_hom, ShortComplex.comp_τ₃,
      comparisonPullIso_hom_τ₃, ShortComplex.pullShearIso_hom_τ₃, Iso.symm_hom,
      comparisonPullIso_inv_τ₃, Category.id_comp]
    exact Category.id_comp (𝟙 _)

/-- The quotient classifying map is injective. -/
theorem classifyingMap_injective :
    Function.Injective (classifyingMap : Classes X Y → Abelian.Ext.{e} X Y 1) := by
  intro x y h
  obtain ⟨E, rfl⟩ := _root_.Quotient.exists_rep x
  obtain ⟨F, rfl⟩ := _root_.Quotient.exists_rep y
  change extClass E = extClass F at h
  exact _root_.Quotient.sound (rel_of_extClass_eq h)

/-- The extension-class map is bijective. -/
theorem classifyingMap_bijective :
    Function.Bijective (classifyingMap : Classes X Y → Abelian.Ext.{e} X Y 1) :=
  ⟨classifyingMap_injective, classifyingMap_surjective X Y⟩

/-- The Ext-one classifier of endpoint-fixing extension classes. -/
def classifyingEquiv : Classes X Y ≃ Abelian.Ext.{e} X Y 1 :=
  Equiv.ofBijective classifyingMap classifyingMap_bijective

@[simp]
theorem classifyingEquiv_classOf (E : WithEndpoints X Y) :
    classifyingEquiv (classOf E) = extClass E :=
  rfl

end CategoryTheory.ShortExactSequence.WithEndpoints
