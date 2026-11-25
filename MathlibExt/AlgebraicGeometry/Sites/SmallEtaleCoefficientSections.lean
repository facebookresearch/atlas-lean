/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleTerminal

/-!
# Coefficients and sections on small étale sites
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (X : Scheme.{u})

private instance commonAffineSmall :
    EssentiallySmall.{max u w} X.AffineEtale := by
  let e₀ := equivSmallModel.{u} X.AffineEtale
  exact EssentiallySmall.mk'
    (e₀.trans
      (AsSmall.equiv :
        SmallModel.{u} X.AffineEtale ≌
          AsSmall.{w} (SmallModel.{u} X.AffineEtale)))

private instance commonAffineSheafify :
    HasSheafify (Scheme.AffineEtale.topology X) AddCommGrpCat.{max u w} :=
  hasSheafifyEssentiallySmallSite.{u, max u w, u + 1, (max u w) + 1, max u w} _ _

private instance commonRestrictionEquivalence :
    ((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous
      AddCommGrpCat.{max u w} (Scheme.AffineEtale.topology X)
      X.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense.{u}
    (Scheme.AffineEtale.Spec X) (Scheme.AffineEtale.topology X)
    X.smallEtaleTopology AddCommGrpCat.{max u w}

/-- The actual small étale site admits sheafification with common-universe coefficients. -/
instance smallEtaleHasSheafify :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology (Scheme.AffineEtale.Spec X)

private instance commonAffineGrothendieck :
    IsGrothendieckAbelian.{max u w}
      (Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{max u w}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (Scheme.AffineEtale.topology X) AddCommGrpCat.{max u w}

/-- Abelian sheaves on the actual small étale site form a Grothendieck category. -/
instance smallEtaleGrothendieck :
    IsGrothendieckAbelian.{max u w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  IsGrothendieckAbelian.of_equivalence
    (((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous
      AddCommGrpCat.{max u w} (Scheme.AffineEtale.topology X)
      X.smallEtaleTopology).asEquivalence.symm)

/-- Actual étale Ext groups are small in the common coefficient universe. -/
instance smallEtaleHasExt :
    HasExt.{max u w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  hasExt_of_enoughInjectives _

/-- The original coefficient sheaf lifted on the same small étale site. -/
def liftCoefficients :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u, w}

/-- The actual global-sections right adjoint is additive. -/
instance smallEtaleGammaAdditive :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).Additive :=
  (constantSheafΓAdj X.smallEtaleTopology
    AddCommGrpCat.{max u w}).right_adjoint_additive

/-- The original constant integral sheaf in the common coefficient universe. -/
abbrev integralSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (AddCommGrpCat.of (ULift.{max u w} ℤ))

/-- The actual integral generator identifies Hom with original terminal sections. -/
def integralHomTerminal (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (integralSheaf.{u, w} X ⟶ Q) ≃+ Q.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)).homAddEquiv (AddCommGrpCat.of (ULift.{max u w} ℤ)) Q).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- The single natural integral-Hom family on every common-universe sheaf. -/
def integralHomSections (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (integralSheaf.{u, w} X ⟶ Q) ≃+
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj Q :=
  (integralHomTerminal.{u, w} X Q).trans
    ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).app Q).addCommGroupIsoToAddEquiv.symm

private theorem integralHomTerminal_naturality
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : integralSheaf.{u, w} X ⟶ Q) (g : Q ⟶ Q') :
    integralHomTerminal.{u, w} X Q' (f ≫ g) =
      g.hom.app (op (Scheme.Etale.mk (𝟙 X))) (integralHomTerminal.{u, w} X Q f) := by
  dsimp only [integralHomTerminal, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [(constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)).homEquiv_naturality_right]
  rfl

/-- Every actual sheaf morphism commutes with the same computed Hom/section family. -/
theorem integralHomSections_naturality
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : integralSheaf.{u, w} X ⟶ Q) (g : Q ⟶ Q') :
    integralHomSections.{u, w} X Q' (f ≫ g) =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map g
        (integralHomSections.{u, w} X Q f) := by
  let S := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)
  change S.inv.app Q' (integralHomTerminal.{u, w} X Q' (f ≫ g)) =
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map g
      (S.inv.app Q (integralHomTerminal.{u, w} X Q f))
  rw [integralHomTerminal_naturality]
  exact ConcreteCategory.congr_hom (S.inv.naturality g) (integralHomTerminal.{u, w} X Q f)

/-- Global sections of the actual coefficient lift retain the original section group. -/
def originalSections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj ((liftCoefficients X).obj F) ≅
      AddCommGrpCat.of (ULift.{u} (F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))) :=
  (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)).app ((liftCoefficients X).obj F)

/-- Complete original-site, integral-generator and original coefficient-map construction. -/
theorem original_site_coefficient_sections :
    let J := X.smallEtaleTopology
    let Γ := Sheaf.Γ J AddCommGrpCat.{max u w}
    let T := Scheme.Etale.mk (𝟙 X)
    let S := Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{max u w} (identityEtaleIsTerminal X)
    let L := liftCoefficients.{u, w} X
    ∃ a : ∀ Q : Sheaf J AddCommGrpCat.{max u w}, (integralSheaf.{u, w} X ⟶ Q) ≃+ Γ.obj Q,
      (∀ (Q Q' : Sheaf J AddCommGrpCat.{max u w}) (f : integralSheaf.{u, w} X ⟶ Q) (g : Q ⟶ Q'),
        a Q' (f ≫ g) = Γ.map g (a Q f)) ∧
      (∀ (Q : Sheaf J AddCommGrpCat.{max u w}) (f : integralSheaf.{u, w} X ⟶ Q),
        S.hom.app Q (a Q f) = f.hom.app (op T)
          ((constantSheafAdj J AddCommGrpCat.{max u w} (identityEtaleIsTerminal X)).unit.app
            (AddCommGrpCat.of (ULift.{max u w} ℤ)) (ULift.up (1 : ℤ)))) ∧
      (∀ (F F' : Sheaf J AddCommGrpCat.{w}) (f : F ⟶ F'),
        Γ.map (L.map f) ≫ (originalSections.{u, w} X F').hom =
          (originalSections.{u, w} X F).hom ≫
            AddCommGrpCat.uliftFunctor.{u, w}.map (f.hom.app (op T))) ∧
      (∀ (F : Sheaf J AddCommGrpCat.{w}) (U V : X.Etaleᵒᵖ) (θ : U ⟶ V) (x : F.obj.obj U),
        (L.obj F).obj.map θ (ULift.up x) = ULift.up (F.obj.map θ x)) ∧
      ∀ (F F' : Sheaf J AddCommGrpCat.{w}) (f : F ⟶ F') (U : X.Etaleᵒᵖ) (x : F.obj.obj U),
        (L.map f).hom.app U (ULift.up x) = ULift.up (f.hom.app U x) := by
  intro J Γ T S L
  refine ⟨integralHomSections.{u, w} X, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q Q' f g
    exact integralHomSections_naturality.{u, w} X f g
  · intro Q f
    change S.hom.app Q (S.inv.app Q (integralHomTerminal.{u, w} X Q f)) = _
    rw [← ConcreteCategory.comp_apply, S.inv_hom_id_app, ConcreteCategory.id_apply]
    rfl
  · intro F F' f
    exact S.hom.naturality (L.map f)
  · intros
    rfl
  · intros
    rfl

end AlgebraicGeometry.Scheme.DerivedSections
