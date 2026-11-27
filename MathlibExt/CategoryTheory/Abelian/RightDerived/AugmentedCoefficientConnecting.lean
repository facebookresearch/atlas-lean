/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionFunctorial
public import MathlibExt.CategoryTheory.Abelian.Injective.AugmentedExactComparisonExistence
public import MathlibExt.Algebra.Homology.CochainShortComplexAugmentation
public import MathlibExt.CategoryTheory.Abelian.Injective.SplitShortComplex
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionNaturality
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeData

/-!
# Connecting morphisms computed by exact coaugmented diagrams

In abelian categories, coaugmentation quasi-isomorphisms identifying
three nonnegative cochain complexes with a short exact sequence admit
strict comparison to an injective horseshoe. If an additive functor
maps that diagram to a short exact sequence of complexes, its
cohomology connecting map commutes with the three augmented
cohomology-to-derived comparisons.
-/


/-!
## Comparison of all three coaugmentations

The degree-zero coaugmentation squares for the two sequence maps are
required to commute. The comparison into the injective horseshoe then
preserves each coaugmentation as a cochain map.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and `H`
an injective horseshoe for `S`. Suppose a short complex of nonnegative
cochain complexes `P₁ → P₂ → P₃` has quasi-isomorphisms
`ι_k : X_k[0] → P_k` whose degree-zero squares commute with `S.f,S.g`.
There is a map of diagrams `P → H` preserving all three coaugmentations. -/
theorem exists_strictAugmentedHorseshoeComparison
    (S : ShortComplex C) (hS : S.ShortExact) (H : HorseshoeData S hS)
    (P : ShortComplex (CochainComplex C ℕ))
    (ι₁ : (CochainComplex.single₀ C).obj S.X₁ ⟶ P.X₁)
    (ι₂ : (CochainComplex.single₀ C).obj S.X₂ ⟶ P.X₂)
    (ι₃ : (CochainComplex.single₀ C).obj S.X₃ ⟶ P.X₃)
    [QuasiIso ι₁] [QuasiIso ι₂] [QuasiIso ι₃]
    (hf : ι₁.f 0 ≫ P.f.f 0 = S.f ≫ ι₂.f 0)
    (hg : ι₂.f 0 ≫ P.g.f 0 = S.g ≫ ι₃.f 0) :
    ∃ a : P ⟶ H.diagram,
      ι₁ ≫ a.τ₁ = H.res₁.ι ∧
      ι₂ ≫ a.τ₂ = H.res₂.ι ∧
      ι₃ ≫ a.τ₃ = H.res₃.ι := by
  let α := ShortComplex.cochainFlipCoaugmentation (S := S) (P := P) ι₁ ι₂ ι₃ hf hg
  let κ := ShortComplex.cochainFlipCoaugmentation (S := S) (P := H.diagram)
    H.res₁.ι H.res₂.ι H.res₃.ι H.lift_f H.lift_g
  let : Mono (α.f 0) :=
    ShortComplex.cochainFlipCoaugmentation_mono ι₁ ι₂ ι₃ hf hg
  have h₀ := ShortComplex.cochainFlipCoaugmentation_exact ι₁ ι₂ ι₃ hf hg
  have hP := ShortComplex.cochainFlip_exact_succ ι₁ ι₂ ι₃
  have hQ : ∀ n : ℕ, Injective (H.diagram.cochainFlip.X n) := by
    intro n
    exact @ShortComplex.Splitting.injective C _ _
      ((HomologicalComplex.eval C (ComplexShape.up ℕ) n).mapShortComplex.obj H.diagram)
      (H.split n) (H.res₁.injective n) (H.res₃.injective n)
  obtain ⟨a, ha⟩ := exists_augmentedExactComparison α κ h₀ hP hQ (𝟙 S)
  have ha' : α ≫ a = κ := ha.trans (by simp only [Functor.map_id, Category.id_comp])
  have hα₀ : α.f 0 = ShortComplex.cochainFlipCoaugmentationZero ι₁ ι₂ ι₃ hf hg :=
    ShortComplex.cochainFlipCoaugmentation_f_zero ι₁ ι₂ ι₃ hf hg
  have hκ₀ : κ.f 0 = ShortComplex.cochainFlipCoaugmentationZero
      (S := S) (P := H.diagram) H.res₁.ι H.res₂.ι H.res₃.ι H.lift_f H.lift_g :=
    ShortComplex.cochainFlipCoaugmentation_f_zero
      (S := S) (P := H.diagram) H.res₁.ι H.res₂.ι H.res₃.ι H.lift_f H.lift_g
  let b := ShortComplex.cochainUnflipHom a
  refine ⟨b, ?_, ?_, ?_⟩
  · apply CochainComplex.coaugmentation_comp_eq_of_f_zero
      ι₁ H.res₁.ι b.τ₁
    have h := congrArg (fun m => (m.f 0).τ₁) ha'
    change (α.f 0).τ₁ ≫ (a.f 0).τ₁ = (κ.f 0).τ₁ at h
    rw [hα₀, hκ₀] at h
    dsimp only [ShortComplex.cochainFlipCoaugmentationZero, ShortComplex.homMk] at h
    exact h
  · apply CochainComplex.coaugmentation_comp_eq_of_f_zero
      ι₂ H.res₂.ι b.τ₂
    have h := congrArg (fun m => (m.f 0).τ₂) ha'
    change (α.f 0).τ₂ ≫ (a.f 0).τ₂ = (κ.f 0).τ₂ at h
    rw [hα₀, hκ₀] at h
    dsimp only [ShortComplex.cochainFlipCoaugmentationZero, ShortComplex.homMk] at h
    exact h
  · apply CochainComplex.coaugmentation_comp_eq_of_f_zero
      ι₃ H.res₃.ι b.τ₃
    have h := congrArg (fun m => (m.f 0).τ₃) ha'
    change (α.f 0).τ₃ ≫ (a.f 0).τ₃ = (κ.f 0).τ₃ at h
    rw [hα₀, hκ₀] at h
    dsimp only [ShortComplex.cochainFlipCoaugmentationZero, ShortComplex.homMk] at h
    exact h

end CategoryTheory.Functor.RightDerived
end


/-!
## Connecting square for a mapped short exact diagram

The connecting map is taken from the short exact sequence of complexes
after applying the additive coefficient functor. The exact coaugmented
source complexes need not have injective terms.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For short exact `S : X₁ → X₂ → X₃`, let
`P₁ → P₂ → P₃` have coaugmentation quasi-isomorphisms `X_k[0] → P_k`
commuting with the two sequence maps in degree zero. If `F(P)` is
short exact, then its boundary `Hⁿ(F(P₃)) → H^(n+1)(F(P₁))`
commutes with the comparisons to the right-derived boundary of `S`. -/
theorem augmentedResolutionToRightDerivedHom_connecting
    (F : C ⥤ D) [F.Additive]
    (S : ShortComplex C) (hS : S.ShortExact)
    (P : ShortComplex (CochainComplex C ℕ))
    (ι₁ : (CochainComplex.single₀ C).obj S.X₁ ⟶ P.X₁)
    (ι₂ : (CochainComplex.single₀ C).obj S.X₂ ⟶ P.X₂)
    (ι₃ : (CochainComplex.single₀ C).obj S.X₃ ⟶ P.X₃)
    [QuasiIso ι₁] [QuasiIso ι₂] [QuasiIso ι₃]
    (hf : ι₁.f 0 ≫ P.f.f 0 = S.f ≫ ι₂.f 0)
    (hg : ι₂.f 0 ≫ P.g.f 0 = S.g ≫ ι₃.f 0)
    (hP : (P.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (n : ℕ) :
    hP.δ n (n + 1) rfl ≫ F.augmentedResolutionToRightDerivedHom P.X₁ ι₁ (n + 1) =
      F.augmentedResolutionToRightDerivedHom P.X₃ ι₃ n ≫
        (F.rightDerivedConnecting n).app ⟨S, hS⟩ := by
  let H := RightDerived.HorseshoeData.ofEndpoints S hS
    (injectiveResolution S.X₁) (injectiveResolution S.X₃)
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := RightDerived.exists_strictAugmentedHorseshoeComparison
    S hS H P ι₁ ι₂ ι₃ hf hg
  let Q := F.mapHomologicalComplex (ComplexShape.up ℕ)
  have hδ := HomologicalComplex.HomologySequence.δ_naturality
    (Q.mapShortComplex.map a) hP (H.mapped_shortExact F) n (n + 1) rfl
  have e₁ := F.augmentedResolutionToRightDerivedHom_eq_of_injectiveTarget
    P.X₁ ι₁ H.res₁ a.τ₁ ha₁ (n + 1)
  have e₃ := F.augmentedResolutionToRightDerivedHom_eq_of_injectiveTarget
    P.X₃ ι₃ H.res₃ a.τ₃ ha₃ n
  have hn := RightDerived.rightDerivedConnecting_eq_endpoints F n S hS H.res₁ H.res₃
  rw [e₁, e₃, hn]
  change hP.δ n (n + 1) rfl ≫
      (HomologicalComplex.homologyMap (Q.map a.τ₁) (n + 1) ≫
        (H.res₁.isoRightDerivedObj F (n + 1)).inv) =
    (HomologicalComplex.homologyMap (Q.map a.τ₃) n ≫ (H.res₃.isoRightDerivedObj F n).inv) ≫
      ((H.res₃.isoRightDerivedObj F n).hom ≫
        (H.mapped_shortExact F).δ n (n + 1) rfl ≫ (H.res₁.isoRightDerivedObj F (n + 1)).inv)
  have hδ' : hP.δ n (n + 1) rfl ≫ HomologicalComplex.homologyMap (Q.map a.τ₁) (n + 1) =
      HomologicalComplex.homologyMap (Q.map a.τ₃) n ≫
        (H.mapped_shortExact F).δ n (n + 1) rfl := hδ
  let H₀ := HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n
  let H₁ := HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) (n + 1)
  change hP.δ n (n + 1) rfl ≫ (H₁.map (Q.map a.τ₁) ≫
      (H.res₁.isoRightDerivedObj F (n + 1)).inv) =
    (H₀.map (Q.map a.τ₃) ≫ (H.res₃.isoRightDerivedObj F n).inv) ≫
      ((H.res₃.isoRightDerivedObj F n).hom ≫
        (H.mapped_shortExact F).δ n (n + 1) rfl ≫ (H.res₁.isoRightDerivedObj F (n + 1)).inv)
  change hP.δ n (n + 1) rfl ≫ H₁.map (Q.map a.τ₁) =
    H₀.map (Q.map a.τ₃) ≫ (H.mapped_shortExact F).δ n (n + 1) rfl at hδ'
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (H.res₁.isoRightDerivedObj F (n + 1)).inv) hδ').trans
      (Category.assoc _ _ _))

end CategoryTheory.Functor
end


/-!
## Connecting square for a functorial coaugmented family

Naturality of the coaugmentations identifies the preceding diagram
comparison with the components of the cohomology-to-derived natural
transformation for the family.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. Let `R : C → CochainComplex C ℕ` preserve
zero morphisms and have natural coaugmentation quasi-isomorphisms
`X[0] → R(X)`. If `S` is short exact and `F(R(S))` is short exact,
its connecting map commutes with the degree-`n` and degree-`n+1`
components of the augmented cohomology-to-derived natural transformation. -/
theorem augmentedResolutionToRightDerivedNatTrans_connecting
    (F : C ⥤ D) [F.Additive] (R : C ⥤ CochainComplex C ℕ) [R.PreservesZeroMorphisms]
    (ι : ∀ X : C, (CochainComplex.single₀ C).obj X ⟶ R.obj X)
    (hι : ∀ X : C, QuasiIso (ι X))
    (hmap : ∀ {X Y : C} (f : X ⟶ Y), ι X ≫ R.map f = (CochainComplex.single₀ C).map f ≫ ι Y)
    (S : ShortComplex C) (hS : S.ShortExact)
    (hR : ((S.map R).map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (n : ℕ) :
    hR.δ n (n + 1) rfl ≫ (F.augmentedResolutionToRightDerivedNatTrans R ι hι hmap (n + 1)).app S.X₁ =
      (F.augmentedResolutionToRightDerivedNatTrans R ι hι hmap n).app S.X₃ ≫
        (F.rightDerivedConnecting n).app ⟨S, hS⟩ := by
  let := hι S.X₁
  let := hι S.X₂
  let := hι S.X₃
  apply F.augmentedResolutionToRightDerivedHom_connecting S hS (S.map R)
    (ι S.X₁) (ι S.X₂) (ι S.X₃) _ _ hR n
  · change (ι S.X₁).f 0 ≫ (R.map S.f).f 0 = S.f ≫ (ι S.X₂).f 0
    have h := HomologicalComplex.congr_hom (hmap S.f) 0
    simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] using h
  · change (ι S.X₂).f 0 ≫ (R.map S.g).f 0 = S.g ≫ (ι S.X₃).f 0
    have h := HomologicalComplex.congr_hom (hmap S.g) 0
    simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] using h

end CategoryTheory.Functor
end
