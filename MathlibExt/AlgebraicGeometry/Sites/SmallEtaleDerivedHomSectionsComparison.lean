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

/-- The genuine large Ext instance for the common sheaf category. -/
theorem largeExt : HasExt.{max (u + 1) w}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  hasExt_of_enoughInjectives _

/-- Change only the Ext carrier universe through the same derived-category morphism. -/
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

/-- The size comparison leaves the actual original derived morphism unchanged. -/
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

/-- The original covariant extension-class boundary is preserved by size transport. -/
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

/-- Global sections of abelian sheaves on the small étale site of X in the common universe. -/
abbrev Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
/-- The additive functor of morphisms from the integral sheaf on the small étale site of X. -/
abbrev P := preadditiveCoyoneda.obj (op (integralSheaf.{u, w} X))

/-- Identify morphisms from the integral sheaf with global sections after lifting the universe. -/
def homLiftIso : P.{u, w} X ≅ Γ.{u, w} X ⋙ AddCommGrpCat.uliftFunctor.{u + 1, max u w} :=
  NatIso.ofComponents
    (fun Q => ((integralHomSections.{u, w} X Q).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {Q Q'} f => by
      apply ConcreteCategory.ext_apply
      intro g
      change ULift.up (integralHomSections.{u, w} X Q' (g ≫ f)) =
        ULift.up ((Γ.{u, w} X).map f (integralHomSections.{u, w} X Q g))
      exact congrArg ULift.up (integralHomSections_naturality.{u, w} X g f))

/-- The isomorphism on right derived functors in degree q induced by the
Hom–sections identification. -/
def derivedHomLiftIso (q : ℕ) :
    (P.{u, w} X).rightDerived q ≅
      (Γ.{u, w} X ⋙ AddCommGrpCat.uliftFunctor.{u + 1, max u w}).rightDerived q where
  hom := NatTrans.rightDerived (homLiftIso.{u, w} X).hom q
  inv := NatTrans.rightDerived (homLiftIso.{u, w} X).inv q
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

/-- Compare Ext from the integral sheaf in degree q with derived global sections
after a universe lift. -/
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

/-- Compare the original small étale cohomology with derived global sections by changing
the Ext carrier universe and removing the lift in the large comparison. -/
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

/-- Every actual resolution representative is unchanged under the Ext size comparison. -/
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
/-- The SAME original étale connecting map is computed by the actual chosen
horseshoe section, differential and retraction on every original representative. -/
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
