/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedLongExactSequence
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ConnectingNaturality
public import MathlibExt.CategoryTheory.Abelian.Ext.DerivedCoyonedaConnecting
public import MathlibExt.CategoryTheory.Abelian.Ext.SizeEquiv

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge
variable (X : Scheme.{u})

/-- For a scheme X in universe u and c = max(u, w), Ext groups
in the category C of AddCommGrpCat c-valued sheaves on its small étale site
also admit carriers in e = max(u + 1, w). This is the larger Ext
universe used to compare Hom from the integral sheaf with global sections. -/
theorem largeExt : HasExt.{max (u + 1) w}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  hasExt_of_enoughInjectives _

/-- Let X be a scheme in universe u, c = max(u, w), e = max(u + 1, w),
and Q an AddCommGrpCat c-valued sheaf on its small étale site. For q ∈ ℕ,
this is the additive equivalence
Hᑫ(X, Q) = Extᑫ_c(ℤ_X, Q) ≃ Extᑫ_e(ℤ_X, Q).
It changes the Ext carrier universe while preserving the sheaves and
the derived-category morphism representing each extension class. -/
def extSizeEquiv (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    Sheaf.H.{max u w, max u w, u, u + 1} Q q ≃+
      Abelian.Ext.{max (u + 1) w} (integralSheaf.{u, w} X) Q q := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max (u + 1) w} C := largeExt.{u, w} X
  let : HasDerivedCategory.{(max u w) + 1} C := HasDerivedCategory.standard C
  exact Abelian.Ext.sizeEquiv.{(max u w) + 1, max u w, max (u + 1) w,
    max (u + 1) w, (max u w) + 1} (integralSheaf.{u, w} X) Q q

/-- For a scheme X in universe u, c = max(u, w), e = max(u + 1, w),
a coefficient sheaf Q on its small étale site, and x ∈ Hᑫ(X, Q),
the Ext size equivalence from universe c to e leaves the representing
morphism in the derived category of AddCommGrpCat c-valued sheaves unchanged.
The derived-category universe is c + 1 on both sides. -/
theorem extSizeEquiv_hom (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    letI : HasDerivedCategory.{(max u w) + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
        HasDerivedCategory.standard _
    Abelian.Ext.homAddEquiv.{(max u w) + 1, max (u + 1) w, max (u + 1) w, (max u w) + 1}
      (extSizeEquiv.{u, w} X Q q x) =
    Abelian.Ext.homAddEquiv.{(max u w) + 1, max u w, max (u + 1) w, (max u w) + 1} x := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max (u + 1) w} C := largeExt.{u, w} X
  let : HasDerivedCategory.{(max u w) + 1} C := HasDerivedCategory.standard C
  exact Abelian.Ext.sizeEquiv_hom.{(max u w) + 1, max u w, max (u + 1) w,
    max (u + 1) w, (max u w) + 1} x

/-- Let X be a scheme in universe u, c = max(u, w), e = max(u + 1, w),
S : 0 → F₁ → F₂ → F₃ → 0 a short exact sequence of abelian sheaves
on its small étale site with coefficients in c, and x ∈ Hᑫ(X, F₃).
The Ext size equivalence satisfies
size(δ_S(x)) = [S] ∘ size(x) in Extᑫ⁺¹_e(ℤ_X, F₁).
Thus it preserves the connecting map and the order of Yoneda composition. -/
theorem extSizeEquiv_connecting
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} S.X₃ q) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    extSizeEquiv.{u, w} X S.X₁ (q + 1) (smallEtaleConnectingMap.{u, w} hS q x) =
      (extSizeEquiv.{u, w} X S.X₃ q x).comp hS.extClass (by omega) := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max (u + 1) w} C := largeExt.{u, w} X
  let : HasDerivedCategory.{(max u w) + 1} C := HasDerivedCategory.standard C
  exact Abelian.Ext.sizeEquiv_comp_extClass.{(max u w) + 1, max u w,
    max (u + 1) w, max (u + 1) w, (max u w) + 1} hS x

end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge
variable (X : Scheme.{u})

/-- For a scheme X in universe u and c = max(u, w), Γ_X is the
global-section functor from AddCommGrpCat c-valued sheaves on its small
étale site to AddCommGrpCat c. It is the right adjoint of the
constant-sheaf functor. -/
abbrev Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
/-- For a scheme X in universe u, c = max(u, w), and e = max(u + 1, w),
P_X is the additive covariant Hom functor Q ↦ Hom(ℤ_X, Q) from
AddCommGrpCat c-valued sheaves on the small étale site to AddCommGrpCat e.
The source ℤ_X is the constant integral sheaf. -/
abbrev P := preadditiveCoyoneda.obj (op (integralSheaf.{u, w} X))

/-- Let X be a scheme in universe u, c = max(u, w), and e = max(u + 1, w).
The additive functor P_X(Q) = Hom(ℤ_X, Q) is naturally isomorphic to the
global-section functor Γ_X followed by the coefficient lift of height u + 1.
On f : ℤ_X → Q, the isomorphism gives ULift.up of the global section
whose value at the terminal étale object is f(1). -/
def homLiftIso : P.{u, w} X ≅ Γ.{u, w} X ⋙ AddCommGrpCat.uliftFunctor.{u + 1, max u w} :=
  NatIso.ofComponents
    (fun Q => ((integralHomSections.{u, w} X Q).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {Q Q'} f => by
      apply ConcreteCategory.ext_apply
      intro g
      change ULift.up (integralHomSections.{u, w} X Q' (g ≫ f)) =
        ULift.up ((Γ.{u, w} X).map f (integralHomSections.{u, w} X Q g))
      exact congrArg ULift.up (integralHomSections_naturality.{u, w} X g f))

/-- For a scheme X in universe u, c = max(u, w), e = max(u + 1, w),
and q ∈ ℕ, the natural isomorphism
P_X ≅ Lift_(u+1) ∘ Γ_X induces an isomorphism of right derived functors
RᑫP_X ≅ Rᑫ(Lift_(u+1) ∘ Γ_X), with values in AddCommGrpCat e.
Here P_X(Q) = Hom(ℤ_X, Q) on AddCommGrpCat c-valued étale sheaves. -/
def derivedHomLiftIso (q : ℕ) :
    (P.{u, w} X).rightDerived q ≅
      (Γ.{u, w} X ⋙ AddCommGrpCat.uliftFunctor.{u + 1, max u w}).rightDerived q where
  hom := NatTrans.rightDerived (homLiftIso.{u, w} X).hom q
  inv := NatTrans.rightDerived (homLiftIso.{u, w} X).inv q
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

/-- For a scheme X in universe u, c = max(u, w), e = max(u + 1, w),
and q ∈ ℕ, this is the natural isomorphism of functors on abelian sheaves
with coefficients in c,
Extᑫ_e(ℤ_X, -) ≅ Lift_(u+1) ∘ RᑫΓ_X.
It uses the integral Hom–section equivalence and the exactness of the
coefficient lift, retaining Γ_X's cohomology groups in universe c. -/
def largeComparisonIso (q : ℕ) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    Abelian.extFunctorObj (integralSheaf.{u, w} X) q ≅
      (Γ.{u, w} X).rightDerived q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, max u w} := by
  letI : HasExt.{max (u + 1) w}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
  exact (Abelian.rightDerivedCoyonedaIsoExtFunctorObj (integralSheaf.{u, w} X) q).symm ≪≫
    derivedHomLiftIso.{u, w} X q ≪≫
      ((Γ.{u, w} X).rightDerivedCompIsoOfPreservesHomology
        (AddCommGrpCat.uliftFunctor.{u + 1, max u w}) q).symm

/-- Let X be a scheme in universe u, c = max(u, w), Q an
AddCommGrpCat c-valued sheaf on its small étale site, and q ∈ ℕ.
This is the additive equivalence Hᑫ(X, Q) ≃ (RᑫΓ_X)(Q).
The left side is Extᑫ(ℤ_X, Q) with carrier in c; the intermediate Ext
carrier is e = max(u + 1, w), and the final coefficient lift is removed,
so the right side is again an abelian group in universe c. -/
def originalComparison
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    Sheaf.H.{max u w, max u w, u, u + 1} Q q ≃+ ((Γ.{u, w} X).rightDerived q).obj Q :=
  (extSizeEquiv.{u, w} X Q q).trans
    (((largeComparisonIso.{u, w} X q).app Q).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

theorem largeComparison_apply
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    ∀ ξ : Abelian.Ext.{max (u + 1) w} (integralSheaf.{u, w} X) Q q,
      ((largeComparisonIso.{u, w} X q).app Q).hom ξ =
        (((Γ.{u, w} X).rightDerivedCompIsoOfPreservesHomology
          AddCommGrpCat.uliftFunctor.{u + 1, max u w} q).app Q).inv
          ((NatTrans.rightDerived (homLiftIso.{u, w} X).hom q).app Q
            (((Abelian.rightDerivedCoyonedaIsoExtFunctorObj
              (integralSheaf.{u, w} X) q).app Q).inv ξ)) := by
  let : HasExt.{max (u + 1) w}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
  intro ξ
  rfl

theorem extSizeEquiv_extMk
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X q)
    (hf : f ≫ (injectiveResolution Q).cocomplex.d q (q + 1) = 0) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    extSizeEquiv.{u, w} X Q q
      ((injectiveResolution Q).extMk.{max u w, max (u + 1) w, (max u w) + 1} f (q + 1) rfl hf :
        Sheaf.H.{max u w, max u w, u, u + 1} Q q) =
      ((injectiveResolution Q).extMk.{max (u + 1) w, max (u + 1) w, (max u w) + 1}
        f (q + 1) rfl hf :
        Abelian.Ext.{max (u + 1) w} (integralSheaf.{u, w} X) Q q) := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max (u + 1) w} C := largeExt.{u, w} X
  let : HasDerivedCategory.{(max u w) + 1} C := HasDerivedCategory.standard C
  exact (injectiveResolution Q).extMk_sizeEquiv.{(max u w) + 1, max u w,
    max (u + 1) w, max (u + 1) w, (max u w) + 1} f (q + 1) rfl hf


end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge
variable (X : Scheme.{u})

/-- Let X be a scheme in universe u, c = max(u, w), e = max(u + 1, w),
Q an AddCommGrpCat c-valued étale sheaf, R an injective resolution of Q,
and f : ℤ_X → Rᑫ a cocycle with d_R ∘ f = 0. The Ext size equivalence
from carrier c to carrier e sends the extension class represented by f
to the extension class represented by the same f in the same resolution.
This holds for every q ∈ ℕ and every chosen injective resolution. -/
theorem extSizeEquiv_extMk_resolution
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (R : InjectiveResolution Q) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ R.cocomplex.X q)
    (hf : f ≫ R.cocomplex.d q (q + 1) = 0) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    extSizeEquiv.{u, w} X Q q
      (R.extMk.{max u w, max (u + 1) w, (max u w) + 1} f (q + 1) rfl hf) =
      R.extMk.{max (u + 1) w, max (u + 1) w, (max u w) + 1} f (q + 1) rfl hf := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max (u + 1) w} C := largeExt.{u, w} X
  let : HasDerivedCategory.{(max u w) + 1} C := HasDerivedCategory.standard C
  exact R.extMk_sizeEquiv.{(max u w) + 1, max u w, max (u + 1) w,
    max (u + 1) w, (max u w) + 1} f (q + 1) rfl hf

set_option backward.isDefEq.respectTransparency false in
/-- Let X be a scheme in universe u, c = max(u, w), and
S : 0 → F₁ → F₂ → F₃ → 0 a short exact sequence of abelian sheaves
with coefficients in c on its small étale site. Choose injective horseshoe
resolutions I₁, I₂, I₃ with degreewise section s_q : I₃,q → I₂,q and
retraction r_(q+1) : I₂,q+1 → I₁,q+1. For a cocycle f : ℤ_X → I₃,q,
the connecting map sends its extension class to the class represented by
r_(q+1) ∘ d_I₂ ∘ s_q ∘ f : ℤ_X → I₁,q+1.
The representative has the indicated order and no additional sign;
it is the same connecting map defined by Yoneda composition with [S]. -/
theorem original_extMk_connecting
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (H : Functor.RightDerived.HorseshoeData S hS) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ H.res₃.cocomplex.X q)
    (hf : f ≫ H.res₃.cocomplex.d q (q + 1) = 0) :
    smallEtaleConnectingMap.{u, w} hS q
      (H.res₃.extMk.{max u w, max (u + 1) w, (max u w) + 1} f (q + 1) rfl hf) =
      H.res₁.extMk.{max u w, max (u + 1) w, (max u w) + 1}
        (H.originalConnectingRepresentative q f) (q + 2) (by omega)
        (H.originalConnectingRepresentative_cycle q f hf) := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max (u + 1) w} C := largeExt.{u, w} X
  let : HasDerivedCategory.{(max u w) + 1} C := HasDerivedCategory.standard C
  apply (extSizeEquiv.{u, w} X S.X₁ (q + 1)).injective
  rw [extSizeEquiv_connecting]
  rw [extSizeEquiv_extMk_resolution, extSizeEquiv_extMk_resolution]
  exact H.extMk_original_boundary q f hf

end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end
