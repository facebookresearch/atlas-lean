/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedSectionCycles

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization Opposite

universe c vc e u w

namespace CategoryTheory.InjectiveResolution.OriginalGammaZero

variable {C : Type c} [Category.{vc} C] [Abelian C] [HasExt.{e} C]
  {A B : C}

omit [HasExt C] in
/-- Let C be an abelian category with Ext groups in a given carrier
universe, R an injective resolution of B, and f : A → B a morphism.
The augmented map ι⁰ ∘ f : A → R⁰ is a degree-zero cocycle:
d⁰ ∘ ι⁰ ∘ f = 0. Object, morphism and Ext universes may be independent. -/
theorem augmentation_cycle (R : InjectiveResolution B) (f : A ⟶ B) :
    (f ≫ R.ι.f 0) ≫ R.cocomplex.d 0 1 = 0 := by
  calc
    (f ≫ R.ι.f 0) ≫ R.cocomplex.d 0 1 =
        f ≫ (R.ι.f 0 ≫ R.cocomplex.d 0 1) := Category.assoc _ _ _
    _ = f ≫ 0 := congrArg (fun g : B ⟶ R.cocomplex.X 1 => f ≫ g)
      R.ι_f_zero_comp_complex_d
    _ = 0 := comp_zero

/-- Let C be an abelian category with Ext groups in a given carrier
universe, R an injective resolution of B, and f : A → B.
The Ext⁰(A, B) class represented by the cocycle ι⁰ ∘ f equals
the degree-zero extension class of f. No global choice of injective
resolutions beyond the given R is required. -/
theorem extMk_augmentation (R : InjectiveResolution B) (f : A ⟶ B) :
    R.extMk (f ≫ R.ι.f 0) 1 rfl (augmentation_cycle R f) = Abelian.Ext.mk₀ f := by
  let z := CochainComplex.HomComplex.Cocycle.fromSingleMk
    ((f ≫ R.ι.f 0) ≫ (R.cochainComplexXIso 0 0 rfl).inv)
    (zero_add (0 : ℤ)) 1 (by norm_num)
    (by
      simp only [R.cochainComplex_d 0 1 0 1 rfl rfl, Category.assoc,
        Iso.inv_hom_id_assoc]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g : A ⟶ R.cocomplex.X 1 =>
          g ≫ (R.cochainComplexXIso 1 1 rfl).inv) (augmentation_cycle R f)).trans
          zero_comp))
  have hz : z = CochainComplex.HomComplex.Cocycle.ofHom
      ((CochainComplex.singleFunctor C 0).map f ≫ R.ι') := by
    apply CochainComplex.HomComplex.Cocycle.ext
    apply (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (zero_add (0 : ℤ))).injective
    simp [z, CochainComplex.HomComplex.Cocycle.fromSingleMk,
      CochainComplex.HomComplex.Cochain.fromSingleEquiv,
      InjectiveResolution.ι'_f_zero, CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, Category.assoc]
    exact Category.assoc _ _ _
  have hshift (g : (CochainComplex.singleFunctor C 0).obj A ⟶ R.cochainComplex) :
      CochainComplex.HomComplex.Cocycle.equivHomShift.symm
          (CochainComplex.HomComplex.Cocycle.ofHom g) =
        ShiftedHom.mk₀ (0 : ℤ) rfl g := by
    ext
    simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
      CochainComplex.HomComplex.Cocycle.homOf,
      CochainComplex.HomComplex.Cochain.rightShift_v, ShiftedHom.mk₀,
      CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f]
  apply R.extEquivCohomologyClass.injective
  rw [R.extEquivCohomologyClass_extMk]
  change CochainComplex.HomComplex.CohomologyClass.mk z = _
  rw [hz]
  let eH := CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.{e}
    (K := (CochainComplex.singleFunctor C 0).obj A)
    (L := R.cochainComplex) (n := 0)
  let eP := SmallShiftedHom.postcompEquiv.{e}
    (W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (X := (CochainComplex.singleFunctor C 0).obj A) (a := (0 : ℤ)) R.ι'
    (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)
  apply eH.injective
  change eH (CochainComplex.HomComplex.CohomologyClass.mk
      (CochainComplex.HomComplex.Cocycle.ofHom
        ((CochainComplex.singleFunctor C 0).map f ≫ R.ι'))) =
    eH (eH.symm (eP (Abelian.Ext.mk₀ f)))
  rw [eH.apply_symm_apply]
  change (CochainComplex.HomComplex.CohomologyClass.mk
      (CochainComplex.HomComplex.Cocycle.ofHom
        ((CochainComplex.singleFunctor C 0).map f ≫ R.ι'))).toSmallShiftedHom =
    (SmallShiftedHom.mk₀ (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) 0 rfl
        ((CochainComplex.singleFunctor C 0).map f)).comp
      (SmallShiftedHom.mk₀ (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) 0 rfl R.ι')
      (zero_add (0 : ℤ))
  rw [CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom_mk, hshift]
  let : HasDerivedCategory.{max c vc} C := HasDerivedCategory.standard C
  apply (SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q).injective
  change SmallShiftedHom.equiv _ DerivedCategory.Q
      (SmallShiftedHom.mk₀ _ 0 rfl ((CochainComplex.singleFunctor C 0).map f ≫ R.ι')) = _
  simp only [SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_comp,
    ShiftedHom.mk₀_comp_mk₀, Functor.map_comp]

end CategoryTheory.InjectiveResolution.OriginalGammaZero

namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

variable (X : Scheme.{u})

/-- Let X be a scheme in universe u, c = max(u, w), and Q an
AddCommGrpCat c-valued sheaf on its small étale site. Write ℤ_X for
the constant integral sheaf and Γ_X for global sections.
For f : ℤ_X → Q, the class of the augmented degree-zero cocycle
ι⁰ ∘ f in R⁰Γ_X(Q) is the image of its global section under
Γ_X(Q) → R⁰Γ_X(Q). The global section is obtained by evaluating f on 1. -/
theorem cycleClass_augmentation_zero
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (f : integralSheaf.{u, w} X ⟶ Q) :
    cycleClass.{u, w} X Q 0 (f ≫ (injectiveResolution Q).ι.f 0)
        (CategoryTheory.InjectiveResolution.OriginalGammaZero.augmentation_cycle _ f) =
      (Γ.{u, w} X).toRightDerivedZero.app Q (integralHomSections.{u, w} X Q f) := by
  let R := injectiveResolution Q
  let G := Γ.{u, w} X
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let S := K.sc 0
  let z := sectionsCycle.{u, w} X Q 0 (f ≫ R.ι.f 0) (CategoryTheory.InjectiveResolution.OriginalGammaZero.augmentation_cycle _ f)
  have hz : S.abCyclesIso.inv z =
      R.toRightDerivedZero' G (integralHomSections.{u, w} X Q f) := by
    apply (AddCommGrpCat.mono_iff_injective S.iCycles).mp inferInstance
    rw [S.abCyclesIso_inv_apply_iCycles]
    have hι := ConcreteCategory.congr_hom
      (R.toRightDerivedZero'_comp_iCycles G) (integralHomSections.{u, w} X Q f)
    change HomologicalComplex.iCycles K 0
        (R.toRightDerivedZero' G (integralHomSections.{u, w} X Q f)) =
      G.map (R.ι.f 0) (integralHomSections.{u, w} X Q f) at hι
    change integralHomSections.{u, w} X _ (f ≫ R.ι.f 0) = _
    exact (integralHomSections_naturality.{u, w} X f (R.ι.f 0)).trans hι.symm
  have hzero := ConcreteCategory.congr_hom (R.toRightDerivedZero_eq G)
    (integralHomSections.{u, w} X Q f)
  change G.toRightDerivedZero.app Q (integralHomSections.{u, w} X Q f) =
    (R.isoRightDerivedObj G 0).inv
      (S.homologyπ (R.toRightDerivedZero' G (integralHomSections.{u, w} X Q f))) at hzero
  change (R.isoRightDerivedObj G 0).inv (S.homologyπ (S.abCyclesIso.inv z)) = _
  rw [hz]
  exact hzero.symm

/-- Let X be a scheme in universe u, c = max(u, w), and Q an
AddCommGrpCat c-valued sheaf on its small étale site. Write ℤ_X for
the constant integral sheaf and Γ_X for global sections.
In degree zero, the Ext-to-derived-sections comparison and the
canonical cohomological delta-functor comparison coincide as additive
equivalences H⁰(X, Q) ≅ R⁰Γ_X(Q). -/
theorem originalComparison_zero
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    originalComparison.{u, w} X Q 0 = CanonicalLongExactSequence.canonicalEquiv.{u, w} X Q 0 := by
  ext x
  let R := injectiveResolution Q
  let G := Γ.{u, w} X
  let f : integralSheaf.{u, w} X ⟶ Q := Abelian.Ext.addEquiv₀ x
  have hx : Abelian.Ext.mk₀ f = x := Abelian.Ext.mk₀_addEquiv₀_apply x
  have hmk := CategoryTheory.InjectiveResolution.OriginalGammaZero.extMk_augmentation R f
  have hcomp := originalComparison_extMk.{u, w} X Q 0 (f ≫ R.ι.f 0)
    (CategoryTheory.InjectiveResolution.OriginalGammaZero.augmentation_cycle _ f)
  rw [hmk, hx] at hcomp
  have hsection : originalComparison.{u, w} X Q 0 x =
      G.toRightDerivedZero.app Q (integralHomSections.{u, w} X Q f) :=
    hcomp.trans (cycleClass_augmentation_zero.{u, w} X Q f)
  let S := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)
  apply ((G.rightDerivedZeroIsoSelf.app Q).addCommGroupIsoToAddEquiv).injective
  apply ((S.app Q).addCommGroupIsoToAddEquiv).injective
  change S.hom.app Q (G.rightDerivedZeroIsoSelf.hom.app Q
      (originalComparison.{u, w} X Q 0 x)) =
    S.hom.app Q (G.rightDerivedZeroIsoSelf.hom.app Q
      (CanonicalLongExactSequence.canonicalEquiv.{u, w} X Q 0 x))
  rw [CanonicalLongExactSequence.canonicalEquiv_zero_sections, hsection]
  have hcancel := ConcreteCategory.congr_hom
    (G.rightDerivedZeroIsoSelf_inv_hom_id_app Q) (integralHomSections.{u, w} X Q f)
  change G.rightDerivedZeroIsoSelf.hom.app Q
      (G.toRightDerivedZero.app Q (integralHomSections.{u, w} X Q f)) =
    integralHomSections.{u, w} X Q f at hcancel
  rw [hcancel]
  have hterminal : S.hom.app Q (integralHomSections.{u, w} X Q f) =
      integralHomTerminal.{u, w} X Q f := by
    let a := (S.app Q).addCommGroupIsoToAddEquiv
    change a (a.symm (integralHomTerminal.{u, w} X Q f)) = _
    exact a.apply_symm_apply _
  exact hterminal.trans (smallEtaleH0Sections_eq_integralHomTerminal.{u, w} X Q x).symm

end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge
variable (X : Scheme.{u})

/-- Let X be a scheme in universe u, c = max(u, w), and Q an
AddCommGrpCat c-valued sheaf on its small étale site. Write ℤ_X for
the constant integral sheaf and Γ_X for global sections.
For every q ∈ ℕ, the Ext-to-derived-sections comparison equals
the canonical long-exact-sequence comparison
Hᑫ(X, Q) ≅ RᑫΓ_X(Q). Both use coefficient universe c. -/
theorem originalComparison_eq
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    originalComparison.{u, w} X Q q =
      CanonicalLongExactSequence.canonicalEquiv.{u, w} X Q q := by
  cases q with
  | zero => exact originalComparison_zero.{u, w} X Q
  | succ n => exact originalComparison_positive.{u, w} X Q n

/-- Let X be a scheme in universe u, c = max(u, w), and Q an
AddCommGrpCat c-valued sheaf on its small étale site. Write ℤ_X for
the constant integral sheaf and Γ_X for global sections.
Let I_Q be the chosen nonnegative injective resolution of Q and
f : ℤ_X → I_Q^q satisfy d ∘ f = 0.
The canonical equivalence Hᑫ(X, Q) ≅ RᑫΓ_X(Q) sends the extension
class of f to the class of the corresponding global-section cycle
in Γ_X(I_Q), followed by the resolution comparison. -/
theorem canonicalEquiv_extMk
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X q)
    (hf : f ≫ (injectiveResolution Q).cocomplex.d q (q + 1) = 0) :
    CanonicalLongExactSequence.canonicalEquiv.{u, w} X Q q
      ((injectiveResolution Q).extMk.{max u w, max (u + 1) w, (max u w) + 1}
        f (q + 1) rfl hf) = cycleClass.{u, w} X Q q f hf := by
  rw [← originalComparison_eq]
  exact originalComparison_extMk.{u, w} X Q q f hf

set_option backward.isDefEq.respectTransparency false in
/-- Let X be a scheme in universe u, c = max(u, w), and
S : 0 → Q₁ → Q₂ → Q₃ → 0 a short exact sequence of coefficient sheaves.
For ξ ∈ Hᑫ(X, Q₃), the canonical comparisons α commute with connecting
maps: δ_(RΓ)(α_Q₃(ξ)) = α_Q₁(δ_et(ξ)) in degree q + 1. -/
theorem canonicalEquiv_connecting
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} S.X₃ q) :
    (Functor.rightDerivedConnecting (Γ.{u, w} X) q).app ⟨S, hS⟩
      (CanonicalLongExactSequence.canonicalEquiv.{u, w} X S.X₃ q x) =
        CanonicalLongExactSequence.canonicalEquiv.{u, w} X S.X₁ (q + 1)
          (smallEtaleConnectingMap.{u, w} hS q x) := by
  let H := Functor.RightDerived.HorseshoeData.ofEndpoints S hS
    (injectiveResolution S.X₁) (injectiveResolution S.X₃)
  obtain ⟨f, hf, hx⟩ := (injectiveResolution S.X₃).extMk_surjective
    (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (X := integralSheaf.{u, w} X)
    (α := x) (q + 1) rfl
  rw [← hx]
  have hsource := canonicalEquiv_extMk.{u, w} X S.X₃ q f hf
  have hboundary := original_extMk_connecting.{u, w} X S hS H q f hf
  have htarget := canonicalEquiv_extMk_positive.{u, w} X S.X₁ q
    (H.originalConnectingRepresentative q f) (H.originalConnectingRepresentative_cycle q f hf)
  have hnative := canonicalConnecting_cycleClass.{u, w} X S hS q f hf
  exact (congrArg ((Functor.rightDerivedConnecting (Γ.{u, w} X) q).app ⟨S, hS⟩)
    hsource).trans (hnative.trans ((htarget.symm).trans
      (congrArg (CanonicalLongExactSequence.canonicalEquiv.{u, w} X S.X₁ (q + 1))
        hboundary.symm)))

set_option backward.isDefEq.respectTransparency false in
/-- Let X be a scheme in universe u, c = max(u, w), and S a
short exact sequence of AddCommGrpCat c-valued étale sheaves.
The connecting map obtained by transporting the étale Yoneda boundary
to derived global sections equals the right-derived-functor connecting
map RᑫΓ_X(S₃) → Rᑫ⁺¹Γ_X(S₁). -/
theorem derivedBoundary_eq_canonicalConnecting
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (q : ℕ) :
    AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q) =
      (Functor.rightDerivedConnecting (Γ.{u, w} X) q).app ⟨S, hS⟩ := by
  apply AddCommGrpCat.ext
  intro y
  let x := (CanonicalLongExactSequence.canonicalEquiv.{u, w} X S.X₃ q).symm y
  have hy : CanonicalLongExactSequence.canonicalEquiv.{u, w} X S.X₃ q x = y :=
    (CanonicalLongExactSequence.canonicalEquiv.{u, w} X S.X₃ q).apply_symm_apply y
  have h := canonicalEquiv_connecting.{u, w} X S hS q x
  rw [hy] at h
  have hb := CanonicalLongExactSequence.derivedBoundary_comparison.{u, w} hS q x
  rw [hy] at hb
  exact hb.trans h.symm

end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end
