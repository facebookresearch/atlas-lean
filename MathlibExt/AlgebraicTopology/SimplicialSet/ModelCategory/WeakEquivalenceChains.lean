/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.ChangeOfCategory
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakEquivalenceChains
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationUnitChains
import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedFunctor

/-!
# Chain invariance under realization weak equivalences

A realization weak equivalence of arbitrary simplicial sets induces a
quasi-isomorphism on unnormalized and normalized chains with coefficients in
an arbitrary module over an arbitrary ring. The ring universe and the
simplicial/module-carrier universe are independent.

The proof compares the map with its image under realization followed by the
singular functor.  The latter is a weak equivalence between Kan complexes,
while the two vertical realization--singular units induce chain
quasi-isomorphisms.  Naturality of the unit and quasi-isomorphism cancellation
then give the result without choosing a quotient representative or assuming
the original simplicial sets are Kan.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace SSet.realizationWeakEquivalences

/-- A realization weak equivalence induces a quasi-isomorphism on
unnormalized simplicial chains with arbitrary module coefficients over an
arbitrary ring. -/
private theorem quasiIso_chainComplexMap_homogeneous
    {R : Type u} [Ring R]
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) (A : ModuleCat.{u} R) :
    QuasiIso (SSet.chainComplexMap f A) := by
  let G : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet
  let F : SSet.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
    (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj A
  have hW : SSet.KanComplex.W (G.map f) :=
    (SSet.mem_realizationWeakEquivalences_iff f).mp hf
  let _ : QuasiIso (F.map (G.map f)) :=
    SSet.KanComplex.W.quasiIso_chainComplexMap hW A
  let _ : QuasiIso (F.map (sSetTopAdj.unit.app X)) :=
    SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A X
  let _ : QuasiIso (F.map (sSetTopAdj.unit.app Y)) :=
    SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A Y
  have hUnitNat :
      f ≫ sSetTopAdj.unit.app Y =
        sSetTopAdj.unit.app X ≫ G.map f := by
    simpa only [G, Functor.id_obj, Functor.id_map] using
      sSetTopAdj.unit.naturality f
  have hChainNat :
      F.map f ≫ F.map (sSetTopAdj.unit.app Y) =
        F.map (sSetTopAdj.unit.app X) ≫ F.map (G.map f) := by
    rw [← F.map_comp, ← F.map_comp, hUnitNat]
  have hComposite : QuasiIso
      (F.map f ≫ F.map (sSetTopAdj.unit.app Y)) := by
    rw [hChainNat]
    infer_instance
  let _ : QuasiIso
      (F.map f ≫ F.map (sSetTopAdj.unit.app Y)) := hComposite
  change QuasiIso (F.map f)
  exact quasiIso_of_comp_right
    (F.map f) (F.map (sSetTopAdj.unit.app Y))

/-- A realization weak equivalence induces a quasi-isomorphism on
unnormalized simplicial chains with coefficients in any abelian group. -/
theorem quasiIso_chainComplexMap_addCommGrp
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) (A : AddCommGrpCat.{u}) :
    QuasiIso (SSet.chainComplexMap f A) := by
  let R : Type u := ULift.{u} ℤ
  let _ : Module R A :=
    Module.compHom A (ULift.ringEquiv.toRingHom : R →+* ℤ)
  let U : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let A' : ModuleCat.{u} R := ModuleCat.of R A
  let e := SSet.mapChainComplexFunctorIso U A'
  let _ : QuasiIso (SSet.chainComplexMap f A') :=
    quasiIso_chainComplexMap_homogeneous (R := R) hf A'
  let _ : QuasiIso
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (SSet.chainComplexMap f A')) :=
    inferInstance
  have hComposite : QuasiIso
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (SSet.chainComplexMap f A') ≫ e.hom.app Y) := by
    infer_instance
  have hNaturality :
      (U.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (SSet.chainComplexMap f A') ≫ e.hom.app Y =
        e.hom.app X ≫ SSet.chainComplexMap f (U.obj A') :=
    e.hom.naturality f
  have hTransported : QuasiIso
      (e.hom.app X ≫ SSet.chainComplexMap f (U.obj A')) := by
    rw [← hNaturality]
    exact hComposite
  let _ : QuasiIso
      (e.hom.app X ≫ SSet.chainComplexMap f (U.obj A')) :=
    hTransported
  change QuasiIso (SSet.chainComplexMap f (U.obj A'))
  exact quasiIso_of_comp_left
    (e.hom.app X) (SSet.chainComplexMap f (U.obj A'))

/-- A realization weak equivalence induces a quasi-isomorphism on chains
with arbitrary module coefficients. The ring universe and the simplicial/
module-carrier universe are independent; the proof uses the original
forgetful chain square and homology reflection. -/
theorem quasiIso_chainComplexMap
    {R : Type v} [Ring R]
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) (A : ModuleCat.{u} R) :
    QuasiIso (SSet.chainComplexMap f A) := by
  let U : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let : CategoryTheory.Limits.HasColimitsOfSize.{u, u} AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfSize.{u, u, u}
  let : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} U := by
    change CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    exact ModuleCat.forget₂PreservesColimitsOfSize (R := R)
  let K : ChainComplex (ModuleCat.{u} R) ℕ := X.chainComplex A
  let L : ChainComplex (ModuleCat.{u} R) ℕ := Y.chainComplex A
  let c : K ⟶ L := SSet.chainComplexMap f A
  let cU := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map c
  let b := SSet.chainComplexMap f (U.obj A)
  let eX : (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅
      X.chainComplex (U.obj A) :=
    (SSet.mapChainComplexFunctorIso.{u} U A).app X
  let eY : (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj L ≅
      Y.chainComplex (U.obj A) :=
    (SSet.mapChainComplexFunctorIso.{u} U A).app Y
  have hb : QuasiIso b :=
    SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp hf (U.obj A)
  have hs : cU ≫ eY.hom = eX.hom ≫ b :=
    (SSet.mapChainComplexFunctorIso.{u} U A).hom.naturality f
  let e : Arrow.mk cU ≅ Arrow.mk b := Arrow.isoMk eX eY hs.symm
  have hcU : QuasiIso cU := (quasiIso_iff_of_arrow_mk_iso cU b e).mpr hb
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology c U).mp hcU

/-- A realization weak equivalence induces a quasi-isomorphism on normalized
simplicial chains with arbitrary module coefficients over an arbitrary ring. -/
theorem quasiIso_normalizedChainComplexMap
    {R : Type v} [Ring R]
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) (A : ModuleCat.{u} R) :
    QuasiIso (SSet.normalizedChainComplexMap f A) := by
  let _ : QuasiIso (SSet.chainComplexMap f A) :=
    quasiIso_chainComplexMap hf A
  have hNat :=
    (SSet.fromNormalizedChainComplexNatTrans
      (C := ModuleCat.{u} R) A).naturality f
  change SSet.normalizedChainComplexMap f A ≫
        Y.fromNormalizedChainComplex A =
      X.fromNormalizedChainComplex A ≫
        SSet.chainComplexMap f A at hNat
  have hComposite : QuasiIso
      (SSet.normalizedChainComplexMap f A ≫
        Y.fromNormalizedChainComplex A) := by
    rw [hNat]
    infer_instance
  let _ : QuasiIso
      (SSet.normalizedChainComplexMap f A ≫
        Y.fromNormalizedChainComplex A) := hComposite
  exact quasiIso_of_comp_right
    (SSet.normalizedChainComplexMap f A)
    (Y.fromNormalizedChainComplex A)

end SSet.realizationWeakEquivalences
