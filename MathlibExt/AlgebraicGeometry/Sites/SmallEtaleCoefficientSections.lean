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
# Coefficients and global sections on a small étale site

Let X be a scheme in universe u and w an independent coefficient universe.
Put c = max(u, w). Abelian sheaves on the small étale site of X with
coefficients in AddCommGrpCat c admit sheafification and form a Grothendieck
abelian category; their Ext groups can be represented in universe c.

Write ℤ_X for the constant sheaf associated to the lifted additive group ℤ,
and Γ_X for global sections. The identity étale object T = (X → X) is
terminal. Evaluation of a sheaf morphism ℤ_X → Q on the canonical section 1
gives natural additive equivalences
Hom(ℤ_X, Q) ≃ Q(T) ≃ Γ_X(Q).

Lifting the coefficients of a sheaf F from universe w to c preserves its
restriction maps and sheaf morphisms by applying ULift to their values.
The global sections of the lifted sheaf are canonically the lift of F(T).
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

/-- For a scheme X in universe u and an independent universe w,
the small étale topology of X admits sheafification of abelian-group
presheaves with coefficients in AddCommGrpCat c, where c = max(u, w). -/
instance smallEtaleHasSheafify :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology (Scheme.AffineEtale.Spec X)

private instance commonAffineGrothendieck :
    IsGrothendieckAbelian.{max u w}
      (Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{max u w}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (Scheme.AffineEtale.topology X) AddCommGrpCat.{max u w}

/-- For a scheme X in universe u and c = max(u, w), the category
of sheaves on the small étale site of X with coefficients in AddCommGrpCat c
is Grothendieck abelian. In particular, this coefficient category of sheaves
has enough injectives for computing its right derived functors. -/
instance smallEtaleGrothendieck :
    IsGrothendieckAbelian.{max u w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  IsGrothendieckAbelian.of_equivalence
    (((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous
      AddCommGrpCat.{max u w} (Scheme.AffineEtale.topology X)
      X.smallEtaleTopology).asEquivalence.symm)

/-- For a scheme X in universe u and c = max(u, w), Extⁿ(F, G)
in the category of AddCommGrpCat c-valued sheaves on the small étale site
of X has a carrier in universe c, for all coefficient sheaves F, G
and all n ∈ ℕ. -/
instance smallEtaleHasExt :
    HasExt.{max u w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  hasExt_of_enoughInjectives _

/-- For a scheme X in universe u, this functor lifts the coefficients
of an abelian sheaf F on its small étale site from universe w to
c = max(u, w). At each étale object U, its value is ULift F(U);
restriction maps and morphisms of sheaves send ULift.up(x) to the lift
of their original value at x. -/
def liftCoefficients :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u, w}

/-- For a scheme X in universe u and c = max(u, w), the global-section
functor Γ_X from AddCommGrpCat c-valued sheaves on the small étale site
of X to AddCommGrpCat c is additive: it preserves sums and zero morphisms. -/
instance smallEtaleGammaAdditive :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).Additive :=
  (constantSheafΓAdj X.smallEtaleTopology
    AddCommGrpCat.{max u w}).right_adjoint_additive

/-- For a scheme X in universe u and c = max(u, w), this is the
constant integral sheaf ℤ_X on the small étale site of X, obtained by
sheafifying the constant presheaf with coefficient group ULift ℤ in universe c. -/
abbrev integralSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (AddCommGrpCat.of (ULift.{max u w} ℤ))

/-- For a scheme X in universe u, c = max(u, w), and an abelian
sheaf Q with coefficients in AddCommGrpCat c on its small étale site,
evaluation on 1 gives the additive equivalence
Hom(ℤ_X, Q) ≃ Q(T), where T = (X → X) is the terminal étale object.
Here 1 is the section induced by the constant-sheaf unit from ULift ℤ. -/
def integralHomTerminal (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (integralSheaf.{u, w} X ⟶ Q) ≃+ Q.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)).homAddEquiv (AddCommGrpCat.of (ULift.{max u w} ℤ)) Q).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- For a scheme X in universe u, c = max(u, w), and an abelian
sheaf Q on its small étale site with coefficients in AddCommGrpCat c,
this is the additive equivalence Hom(ℤ_X, Q) ≃ Γ_X(Q).
A morphism from the constant integral sheaf is sent to its global section
given by the image of 1 at the terminal étale object X → X. -/
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

/-- Let X be a scheme in universe u, c = max(u, w), Q, Q′ abelian
sheaves with coefficients in AddCommGrpCat c on its small étale site,
f : ℤ_X → Q, and g : Q → Q′. The Hom-to-sections equivalence satisfies
α_Q′(g ∘ f) = Γ_X(g)(α_Q(f)). Thus evaluation on the integral generator
is natural in the coefficient sheaf. -/
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

/-- For a scheme X in universe u and an abelian sheaf F on its
small étale site with coefficients in universe w, the global-section
group of its coefficient lift to c = max(u, w) is isomorphic to
ULift F(T), with lift height u, where T = (X → X) is the terminal
étale object. -/
def originalSections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj ((liftCoefficients X).obj F) ≅
      AddCommGrpCat.of (ULift.{u} (F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))) :=
  (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)).app ((liftCoefficients X).obj F)

/-- For a scheme X in universe u and c = max(u, w), there is a
natural additive family α_Q : Hom(ℤ_X, Q) ≃ Γ_X(Q) for abelian sheaves
on the small étale site. Its terminal section is the image of 1 under Q's
integral-sheaf morphism. For the coefficient lift L from universe w to c,
the isomorphisms Γ_X(LF) ≅ ULift F(X → X) commute with sheaf morphisms.
Moreover, L sends every restriction θ and every sheaf morphism g to the
maps ULift.up(x) ↦ ULift.up(F(θ)(x)) and
ULift.up(x) ↦ ULift.up(g_U(x)), respectively. -/
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
