/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleCoefficientSections
public import MathlibExt.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import MathlibExt.CategoryTheory.Abelian.Ext.DerivedCoyoneda
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison
public import MathlibExt.Algebra.Homology.Functor

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (X : Scheme.{u})
/-- The literal three-term sections complex in each positive degree. -/
abbrev positiveShort (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :=
  (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (injectiveResolution Q).cocomplex).sc' n (n + 1) (n + 2)

/-- The literal sections-homology class followed by the canonical derived-object comparison. -/
def positiveCycleClass (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ)
    (z : (positiveShort.{u, w} X Q n).g.hom.ker) :=
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let R := injectiveResolution Q
  let K := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  (R.isoRightDerivedObj Γ (n + 1)).inv
    ((ShortComplex.homologyMapIso (K.isoSc' n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1)))).inv
        ((positiveShort.{u, w} X Q n).homologyπ ((positiveShort.{u, w} X Q n).abCyclesIso.inv z)))

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections.Reuse
variable (X : Scheme.{u})

private theorem largeExt :
    HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  hasExt_of_enoughInjectives _

private abbrev Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
private abbrev P := preadditiveCoyoneda.obj (op (integralSheaf.{u, w} X))

private def homLiftIso : P.{u, w} X ≅ Γ.{u, w} X ⋙ AddCommGrpCat.uliftFunctor.{u + 1, max u w} :=
  NatIso.ofComponents
    (fun Q => ((integralHomSections.{u, w} X Q).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {Q Q'} f => by
      apply ConcreteCategory.ext_apply
      intro g
      change ULift.up (integralHomSections.{u, w} X Q' (g ≫ f)) =
        ULift.up ((Γ.{u, w} X).map f (integralHomSections.{u, w} X Q g))
      exact congrArg ULift.up (integralHomSections_naturality.{u, w} X g f))

private def derivedHomLiftIso (q : ℕ) :
    (P.{u, w} X).rightDerived q ≅
      (Γ.{u, w} X ⋙ AddCommGrpCat.uliftFunctor.{u + 1, max u w}).rightDerived q where
  hom := NatTrans.rightDerived (homLiftIso.{u, w} X).hom q
  inv := NatTrans.rightDerived (homLiftIso.{u, w} X).inv q
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

private def largeComparisonIso (q : ℕ) :
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

private def extSizeEquiv
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    Sheaf.H.{max u w, max u w, u, u + 1} Q q ≃+
      Abelian.Ext.{max (u + 1) w} (integralSheaf.{u, w} X) Q q := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max (u + 1) w} C := largeExt.{u, w} X
  let : HasDerivedCategory.{(max u w) + 1} C := HasDerivedCategory.standard C
  let e₁ := Abelian.Ext.homAddEquiv.{(max u w) + 1, max u w, max (u + 1) w, (max u w) + 1}
    (X := integralSheaf.{u, w} X) (Y := Q) (n := q)
  let e₂ := Abelian.Ext.homAddEquiv.{(max u w) + 1, max (u + 1) w, max (u + 1) w, (max u w) + 1}
    (X := integralSheaf.{u, w} X) (Y := Q) (n := q)
  exact e₁.trans e₂.symm

private def originalComparison
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    Sheaf.H.{max u w, max u w, u, u + 1} Q q ≃+ ((Γ.{u, w} X).rightDerived q).obj Q :=
  (extSizeEquiv.{u, w} X Q q).trans
    (((largeComparisonIso.{u, w} X q).app Q).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

private theorem largeComparison_apply
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

private theorem extSizeEquiv_extMk
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
  let e₁ := Abelian.Ext.homAddEquiv.{(max u w) + 1, max u w, max (u + 1) w, (max u w) + 1}
    (X := integralSheaf.{u, w} X) (Y := Q) (n := q)
  let e₂ := Abelian.Ext.homAddEquiv.{(max u w) + 1, max (u + 1) w, max (u + 1) w, (max u w) + 1}
    (X := integralSheaf.{u, w} X) (Y := Q) (n := q)
  have hmap : e₁ ((injectiveResolution Q).extMk.{max u w, max (u + 1) w, (max u w) + 1}
      f (q + 1) rfl hf) =
      e₂ ((injectiveResolution Q).extMk.{max (u + 1) w, max (u + 1) w, (max u w) + 1}
        f (q + 1) rfl hf) := by
    simp only [e₁, e₂, Abelian.Ext.homAddEquiv_apply, InjectiveResolution.extMk_hom]
  change e₂.symm (e₁ ((injectiveResolution Q).extMk.{max u w, max (u + 1) w, (max u w) + 1}
    f (q + 1) rfl hf)) = _
  apply e₂.injective
  exact (e₂.apply_symm_apply _).trans hmap

end AlgebraicGeometry.Scheme.DerivedSections.Reuse

namespace AlgebraicGeometry.Scheme.DerivedSections.Reuse
variable (X : Scheme.{u})

-- The original sheaf, Ext-universe, and resolution comparisons need a larger budget.
private theorem originalComparison_extMk
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X (n + 1))
    (hf : f ≫ (injectiveResolution Q).cocomplex.d (n + 1) (n + 2) = 0)
    (z : (positiveShort.{u, w} X Q n).g.hom.ker)
    (hz : z.val = integralHomSections.{u, w} X _ f) :
    originalComparison.{u, w} X Q (n + 1)
        ((injectiveResolution Q).extMk.{max u w, max (u + 1) w, (max u w) + 1}
          f (n + 2) rfl hf) =
      positiveCycleClass.{u, w} X Q n z := by
  let : HasExt.{max (u + 1) w}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
  let R := injectiveResolution Q
  let G := Γ.{u, w} X
  let U := AddCommGrpCat.uliftFunctor.{u + 1, max u w}
  let Z := integralSheaf.{u, w} X
  let hE := DerivedCoyoneda.homologyDataExt Z R (n + 1)
  let c : hE.K := ⟨f, hf⟩
  let a := ((DerivedCoyoneda.mappedCocomplex Z R).sc (n + 1)).homologyπ
    (hE.cyclesIso.inv c)
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let E := K.isoSc' n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))
  obtain ⟨z₀, hvalue, hclass⟩ := ShortComplex.ab_cycle_transport_inv E z
  change z₀.val = z.val at hvalue
  let α := (homLiftIso.{u, w} X).hom
  let β := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex
  let φ : (DerivedCoyoneda.mappedCocomplex Z R).sc (n + 1) ⟶
      (K.sc (n + 1)).map U :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{max (u + 1) w}
      (ComplexShape.up ℕ) (n + 1)).map β
  have hmiddle : φ.τ₂ (hE.i c) = ULift.up z₀.val := by
    change ULift.up (integralHomSections.{u, w} X _ f) = ULift.up z₀.val
    exact congrArg ULift.up (hz.symm.trans hvalue.symm)
  have hcycles := ShortComplex.ulift_cyclesMap_eq_of_middle_eq
    (K.sc (n + 1)) ((DerivedCoyoneda.mappedCocomplex Z R).sc (n + 1)) hE φ c z₀ hmiddle
  have hπ : HomologicalComplex.homologyMap β (n + 1) a =
      ((K.sc (n + 1)).map U).homologyπ (ShortComplex.cyclesMap φ (hE.cyclesIso.inv c)) :=
    ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) (hE.cyclesIso.inv c)
  let M := (K.sc (n + 1)).mapHomologyIso U
  have hUπ := ConcreteCategory.congr_hom
    (ShortComplex.homologyπ_comp_mapHomologyIso_hom (K.sc (n + 1)) U)
    (ShortComplex.cyclesMap φ (hE.cyclesIso.inv c))
  have hUvalue : U.map (K.sc (n + 1)).homologyπ
        (ULift.up ((K.sc (n + 1)).abCyclesIso.inv z₀)) =
      (ULift.up ((ShortComplex.homologyMapIso E).inv
        ((positiveShort.{u, w} X Q n).homologyπ
          ((positiveShort.{u, w} X Q n).abCyclesIso.inv z))) : U.obj (K.sc (n + 1)).homology) :=
    congrArg (fun x : (K.sc (n + 1)).homology =>
      (ULift.up x : U.obj (K.sc (n + 1)).homology)) hclass
  have hH : M.hom (HomologicalComplex.homologyMap β (n + 1) a) =
      (ULift.up ((ShortComplex.homologyMapIso E).inv
        ((positiveShort.{u, w} X Q n).homologyπ
          ((positiveShort.{u, w} X Q n).abCyclesIso.inv z))) : U.obj (K.sc (n + 1)).homology) :=
    (congrArg M.hom hπ).trans
      (hUπ.trans ((congrArg (U.map (K.sc (n + 1)).homologyπ) hcycles).trans hUvalue))
  have hDC := Abelian.rightDerivedCoyonedaIsoExtFunctorObj_inv_extMk Z Q (n + 1) f hf
  have hComp : ((G.rightDerivedCompIsoOfPreservesHomology U (n + 1)).app Q).inv
        ((NatTrans.rightDerived α (n + 1)).app Q
          ((R.isoRightDerivedObj (P.{u, w} X) (n + 1)).inv a)) =
      U.map (R.isoRightDerivedObj G (n + 1)).inv
        (M.hom (HomologicalComplex.homologyMap β (n + 1) a)) :=
    ConcreteCategory.congr_hom
      (CategoryTheory.Functor.rightDerivedCompIsoOfPreservesHomology_inv_naturality_functor
        G U (P.{u, w} X) α Q (n + 1)) a
  have hLarge : ((largeComparisonIso.{u, w} X (n + 1)).app Q).hom
        (R.extMk.{max (u + 1) w, max (u + 1) w, (max u w) + 1} f (n + 2) rfl hf) =
      U.map (R.isoRightDerivedObj G (n + 1)).inv
        (M.hom (HomologicalComplex.homologyMap β (n + 1) a)) := by
    exact (largeComparison_apply.{u, w} X Q (n + 1)
      (R.extMk.{max (u + 1) w, max (u + 1) w, (max u w) + 1} f (n + 2) rfl hf)).trans
        ((congrArg (fun x : ((P.{u, w} X).rightDerived (n + 1)).obj Q =>
          ((G.rightDerivedCompIsoOfPreservesHomology U (n + 1)).app Q).inv
            ((NatTrans.rightDerived α (n + 1)).app Q x)) hDC).trans hComp)
  have hFinal : U.map (R.isoRightDerivedObj G (n + 1)).inv
        (ULift.up ((ShortComplex.homologyMapIso E).inv
          ((positiveShort.{u, w} X Q n).homologyπ
            ((positiveShort.{u, w} X Q n).abCyclesIso.inv z)))) =
      (ULift.up (positiveCycleClass.{u, w} X Q n z) : U.obj ((G.rightDerived (n + 1)).obj Q)) := rfl
  have hSize := extSizeEquiv_extMk.{u, w} X Q (n + 1) f hf
  have hResult : ((largeComparisonIso.{u, w} X (n + 1)).app Q).hom
        (extSizeEquiv.{u, w} X Q (n + 1)
          (R.extMk.{max u w, max (u + 1) w, (max u w) + 1} f (n + 2) rfl hf)) =
      (ULift.up (positiveCycleClass.{u, w} X Q n z) : U.obj ((G.rightDerived (n + 1)).obj Q)) :=
    (congrArg (fun ξ : Abelian.Ext.{max (u + 1) w} Z Q (n + 1) =>
      ((largeComparisonIso.{u, w} X (n + 1)).app Q).hom ξ) hSize).trans
      (hLarge.trans ((congrArg (U.map (R.isoRightDerivedObj G (n + 1)).inv) hH).trans hFinal))
  change (((largeComparisonIso.{u, w} X (n + 1)).app Q).hom
    (extSizeEquiv.{u, w} X Q (n + 1)
      (R.extMk.{max u w, max (u + 1) w, (max u w) + 1} f (n + 2) rfl hf))).down = _
  exact congrArg ULift.down hResult

end AlgebraicGeometry.Scheme.DerivedSections.Reuse

namespace AlgebraicGeometry.Scheme.DerivedSections.Reuse
variable (X : Scheme.{u})

private def positiveQuotientDerivedIso
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    AddCommGrpCat.of ((positiveShort.{u, w} X Q n).g.hom.ker ⧸
        (positiveShort.{u, w} X Q n).abToCycles.range) ≅
      ((Γ.{u, w} X).rightDerived (n + 1)).obj Q :=
  let G := Γ.{u, w} X
  let R := injectiveResolution Q
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  (positiveShort.{u, w} X Q n).abHomologyIso.symm ≪≫
    (ShortComplex.homologyMapIso (K.isoSc' n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1)))).symm ≪≫
        (R.isoRightDerivedObj G (n + 1)).symm

private theorem positiveQuotientDerivedIso_class
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ)
    (z : (positiveShort.{u, w} X Q n).g.hom.ker) :
    (positiveQuotientDerivedIso.{u, w} X Q n).hom
      (QuotientAddGroup.mk' (positiveShort.{u, w} X Q n).abToCycles.range z) =
        positiveCycleClass.{u, w} X Q n z := by
  let S := positiveShort.{u, w} X Q n
  let G := Γ.{u, w} X
  let R := injectiveResolution Q
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let E := ShortComplex.homologyMapIso (K.isoSc' n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1)))
  have hπ : S.abHomologyIso.inv (QuotientAddGroup.mk' S.abToCycles.range z) =
      S.homologyπ (S.abCyclesIso.inv z) :=
    ConcreteCategory.congr_hom S.abLeftHomologyData.π_comp_homologyIso_inv z
  change (R.isoRightDerivedObj G (n + 1)).inv (E.inv (S.abHomologyIso.inv _)) =
    (R.isoRightDerivedObj G (n + 1)).inv (E.inv (S.homologyπ (S.abCyclesIso.inv z)))
  exact congrArg (fun x => (R.isoRightDerivedObj G (n + 1)).inv (E.inv x)) hπ

private def canonicalPositiveCycleMap
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    (positiveShort.{u, w} X Q n).g.hom.ker →+
      Sheaf.H.{max u w, max u w, u, u + 1} Q (n + 1) :=
  (((positiveQuotientDerivedIso.{u, w} X Q n).addCommGroupIsoToAddEquiv.trans
    (originalComparison.{u, w} X Q (n + 1)).symm).toAddMonoidHom).comp
      (QuotientAddGroup.mk' (positiveShort.{u, w} X Q n).abToCycles.range)

-- Normalizing the original sheaf/Ext equivalences exceeds the default recursion depth.
private theorem canonicalPositivePacket
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    let R := injectiveResolution Q
    Function.Surjective (canonicalPositiveCycleMap.{u, w} X Q n) ∧
    (positiveShort.{u, w} X Q n).abToCycles.range = (canonicalPositiveCycleMap.{u, w} X Q n).ker ∧
    (∀ z, originalComparison.{u, w} X Q (n + 1)
      (canonicalPositiveCycleMap.{u, w} X Q n z) = positiveCycleClass.{u, w} X Q n z) ∧
    ∀ (f : integralSheaf.{u, w} X ⟶ R.cocomplex.X (n + 1))
      (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0),
      ∃ z : (positiveShort.{u, w} X Q n).g.hom.ker,
        z.val = integralHomSections.{u, w} X _ f ∧
          canonicalPositiveCycleMap.{u, w} X Q n z = R.extMk f (n + 2) rfl hf := by
  let S := positiveShort.{u, w} X Q n
  let e := originalComparison.{u, w} X Q (n + 1)
  let g := (positiveQuotientDerivedIso.{u, w} X Q n).addCommGroupIsoToAddEquiv.trans e.symm
  let π := QuotientAddGroup.mk' S.abToCycles.range
  have hSurj : Function.Surjective (canonicalPositiveCycleMap.{u, w} X Q n) :=
    g.surjective.comp (QuotientAddGroup.mk'_surjective S.abToCycles.range)
  have hKer : (canonicalPositiveCycleMap.{u, w} X Q n).ker = S.abToCycles.range :=
    (AddMonoidHom.ker_comp_of_injective π g.toAddMonoidHom g.injective).trans
      (QuotientAddGroup.ker_mk' S.abToCycles.range)
  have hClass (z : S.g.hom.ker) :
      e (canonicalPositiveCycleMap.{u, w} X Q n z) = positiveCycleClass.{u, w} X Q n z := by
    change e (e.symm ((positiveQuotientDerivedIso.{u, w} X Q n).hom (π z))) = _
    exact (e.apply_symm_apply _).trans (positiveQuotientDerivedIso_class.{u, w} X Q n z)
  refine ⟨hSurj, hKer.symm, hClass, ?_⟩
  intro f hf
  let R := injectiveResolution Q
  let G := Γ.{u, w} X
  have hcycle : G.map (R.cocomplex.d (n + 1) (n + 2))
      (integralHomSections.{u, w} X _ f) = 0 :=
    (integralHomSections_naturality.{u, w} X f (R.cocomplex.d (n + 1) (n + 2))).symm.trans
      ((congrArg (integralHomSections.{u, w} X _) hf).trans
        (integralHomSections.{u, w} X _).map_zero)
  let z : S.g.hom.ker := ⟨integralHomSections.{u, w} X _ f, hcycle⟩
  refine ⟨z, rfl, ?_⟩
  apply e.injective
  exact (hClass z).trans (originalComparison_extMk.{u, w} X Q n f hf z rfl).symm

end AlgebraicGeometry.Scheme.DerivedSections.Reuse

namespace AlgebraicGeometry.Scheme.DerivedSections
variable (X : Scheme.{u})

/-- The complete cycle-map and comparison families, with every representative identified. -/
theorem positive_ext_cycle_comparison :
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
    ∃ p : ∀ (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ),
        (positiveShort.{u, w} X Q n).g.hom.ker →+
          Sheaf.H.{max u w, max u w, u, u + 1} Q (n + 1),
      ∃ e : ∀ (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ),
        Sheaf.H.{max u w, max u w, u, u + 1} Q (n + 1) ≃+ (Γ.rightDerived (n + 1)).obj Q,
      ∀ (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ),
        let R := injectiveResolution Q
        Function.Surjective (p Q n) ∧
        (positiveShort.{u, w} X Q n).abToCycles.range = (p Q n).ker ∧
        (∀ z, e Q n (p Q n z) = positiveCycleClass.{u, w} X Q n z) ∧
        ∀ (f : integralSheaf.{u, w} X ⟶ R.cocomplex.X (n + 1))
          (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0),
          ∃ z : (positiveShort.{u, w} X Q n).g.hom.ker,
            z.val = integralHomSections.{u, w} X _ f ∧ p Q n z = R.extMk f (n + 2) rfl hf := by
  intro G
  refine ⟨Reuse.canonicalPositiveCycleMap.{u, w} X,
    (fun Q n => Reuse.originalComparison.{u, w} X Q (n + 1)), ?_⟩
  intro Q n
  exact Reuse.canonicalPositivePacket.{u, w} X Q n

end AlgebraicGeometry.Scheme.DerivedSections
