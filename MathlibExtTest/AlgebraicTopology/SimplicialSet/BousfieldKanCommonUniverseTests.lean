/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotalNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import Mathlib.Algebra.Category.Grp.Ulift
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.AlgebraicTopology.SingularHomology.Integral

/-! # Ordinary public clients of common-universe Bousfield--Kan chains -/

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe uJ vJ uA vA w z

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanCommonUniverseTests

/-- The existing simplex computation simplifies with a strictly positive Hom universe. -/
public theorem bkHocolimMap_higherHom_simp
    {J : Type uJ} [Category.{vJ + 1} J]
    {D E : J ⥤ SSet.{max uJ (vJ + 1)}} (α : D ⟶ E) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) :
    (SSet.bkHocolimMap α).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p).app (op ⦋n⦌)
          ((α.app p.1.left).app (op ⦋n⦌) x) := by
  simp

private def integralCoefficientIso :
    (AddCommGrpCat.uliftFunctor.{z, w}).obj
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{w}) ≅
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{max w z}) :=
  (((AddEquiv.ulift : ULift.{z, w} (ULift.{w, 0} ℤ) ≃+ ULift.{w, 0} ℤ).trans
      (AddEquiv.ulift : ULift.{w, 0} ℤ ≃+ ℤ)).trans
        (AddEquiv.ulift : ULift.{max w z, 0} ℤ ≃+ ℤ).symm).toAddCommGrpIso

private def integralChainIso :
    ((SSet.chainComplexFunctor.{w} AddCommGrpCat.{w}).obj
        AlgebraicTopology.singularIntegralCoefficients) ⋙
        (AddCommGrpCat.uliftFunctor.{z, w}).mapHomologicalComplex (.down ℕ) ≅
      (SSet.chainComplexFunctor.{w} AddCommGrpCat.{max w z}).obj
        AlgebraicTopology.singularIntegralCoefficients :=
  SSet.chainComplexFunctorObjCompMapIso.{w} AddCommGrpCat.uliftFunctor
      AlgebraicTopology.singularIntegralCoefficients ≪≫
    (SSet.chainComplexFunctor.{w} AddCommGrpCat.{max w z}).mapIso
      integralCoefficientIso

private def integralHomologyIso (X : SSet.{w}) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{z, w}.obj
        (X.homology AlgebraicTopology.singularIntegralCoefficients n) ≅
      X.homology (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{max w z}) n :=
  ((HomologicalComplex.mapHomologyFunctorIso (c := .down ℕ) n
      AddCommGrpCat.uliftFunctor.{z, w}).app
        (X.chainComplex AlgebraicTopology.singularIntegralCoefficients)).symm ≪≫
    HomologicalComplex.homologyMapIso (integralChainIso.{w, z}.app X) n

private theorem coefficientChainIso_ι
    {B : Type uA} [Category.{vA} B] [Preadditive B] [HasCoproducts.{w} B]
    {R S : B} (e : R ≅ S) (X : SSet.{w}) {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex (R := R) x ≫
        (((SSet.chainComplexFunctor B).mapIso e).hom.app X).f n =
      e.hom ≫ X.ιChainComplex (R := S) x := by
  dsimp [SSet.chainComplexFunctor, SSet.ιChainComplex]
  simp

private theorem integralChainIso_ι (X : SSet.{w}) {n : ℕ} (x : X _⦋n⦌) :
    AddCommGrpCat.uliftFunctor.{z, w}.map (X.ιChainComplex
        (R := AlgebraicTopology.singularIntegralCoefficients) x) ≫
        (integralChainIso.{w, z}.app X).hom.f n =
      integralCoefficientIso.{w, z}.hom ≫ X.ιChainComplex
        (R := (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{max w z})) x := by
  change _ ≫
      (((SSet.chainComplexFunctorObjCompMapIso.{w} AddCommGrpCat.uliftFunctor.{z, w}
          AlgebraicTopology.singularIntegralCoefficients).hom.app X).f n ≫
        (((SSet.chainComplexFunctor.{w} AddCommGrpCat.{max w z}).mapIso
          integralCoefficientIso.{w, z}).hom.app X).f n) = _
  rw [← Category.assoc,
    SSet.map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f,
    coefficientChainIso_ι]

private theorem integralHomologyIso_naturality {X Y : SSet.{w}} (f : X ⟶ Y) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{z, w}.map
        (SSet.homologyMap f AlgebraicTopology.singularIntegralCoefficients n) ≫
        (integralHomologyIso.{w, z} Y n).hom =
      (integralHomologyIso.{w, z} X n).hom ≫
        SSet.homologyMap f (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{max w z}) n := by
  let H := HomologicalComplex.mapHomologyFunctorIso (c := .down ℕ) n
    AddCommGrpCat.uliftFunctor.{z, w}
  let phi := SSet.chainComplexMap f
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{w})
  have hU := H.inv.naturality phi
  have hC := congrArg (fun g => HomologicalComplex.homologyMap g n)
    ((integralChainIso.{w, z}).hom.naturality f)
  simp only [HomologicalComplex.homologyMap_comp] at hC
  exact ((congrArg (fun g => g ≫ HomologicalComplex.homologyMap
      (integralChainIso.{w, z}.app Y).hom n) hU).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun g => H.inv.app
        (X.chainComplex AlgebraicTopology.singularIntegralCoefficients) ≫ g) hC).trans
          (Category.assoc _ _ _).symm)))

/-- A client fixes the independent indexing universes and uses the actual public maps. -/
public theorem commonUniverseBK_public_characteristics
    {J : Type uJ} [Category.{vJ} J]
    (A : Type uA) [Category.{vA} A] [Preadditive A]
    [HasCoproducts.{max uJ vJ} A] [HasCountableCoproducts A] (R : A)
    {D E F : J ⥤ SSet.{max uJ vJ}} (α : D ⟶ E) (β : E ⟶ F) (S : AddCommGrpCat.{max uJ vJ}) :
    let B := fun D : J ⥤ SSet.{max uJ vJ} =>
      (SSet.bisimplicialLinearizationFunctor A R).obj (SSet.bkBarBisimplicial D)
    let K := fun D : J ⥤ SSet.{max uJ vJ} => SSet.bkAlternatingBicomplex A R D
    let c := fun D : J ⥤ SSet.{max uJ vJ} => SSet.bkCarrierChainIso A R D
    let e := fun D : J ⥤ SSet.{max uJ vJ} => SSet.bkDiagonalTotalHomotopyEquiv A R D
    let a := (AlgebraicTopology.alternatingFaceMapComplex A).map
      ((SSet.coproductLinearizationFunctor A R).map (SSet.bkHocolimMap α))
    let t := SSet.chainComplexMap (SSet.bkHocolimMap α) R
    let T := (SSet.bkAlternatingTotalComplexFunctor A R).map α
    let cZ : (AddCommGrpCat.uliftFunctor.{z, max uJ vJ}).obj
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{max uJ vJ}) ≅
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{max uJ vJ z}) :=
      (((AddEquiv.ulift : ULift.{z, max uJ vJ} (ULift.{max uJ vJ, 0} ℤ) ≃+
          ULift.{max uJ vJ, 0} ℤ).trans
        (AddEquiv.ulift : ULift.{max uJ vJ, 0} ℤ ≃+ ℤ)).trans
        (AddEquiv.ulift : ULift.{max uJ vJ z, 0} ℤ ≃+ ℤ).symm).toAddCommGrpIso
    let Xi := SSet.chainComplexFunctorObjCompMapIso.{max uJ vJ}
        AddCommGrpCat.uliftFunctor.{z, max uJ vJ}
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{max uJ vJ}) ≪≫
      (SSet.chainComplexFunctor.{max uJ vJ} AddCommGrpCat.{max uJ vJ z}).mapIso cZ
    let H := fun (X : SSet.{max uJ vJ}) (n : ℕ) =>
      ((HomologicalComplex.mapHomologyFunctorIso (c := .down ℕ) n
          AddCommGrpCat.uliftFunctor.{z, max uJ vJ}).app
          (X.chainComplex AlgebraicTopology.singularIntegralCoefficients)).symm ≪≫
        HomologicalComplex.homologyMapIso (Xi.app X) n
    (∀ n, (SSet.bkHocolim D).obj (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D n).obj (op ⦋n⦌)) ∧
    SSet.bkHocolimMap (𝟙 D) = 𝟙 (SSet.bkHocolim D) ∧
    SSet.bkHocolimMap (α ≫ β) = SSet.bkHocolimMap α ≫ SSet.bkHocolimMap β ∧
    (∀ (n : ℕ) (s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
      (x : (D.obj s.1.left).obj (op ⦋n⦌)),
      (SSet.bkHocolim D).ιChainComplex (R := R)
          ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n s).app
            (op ⦋n⦌) x) ≫ t.f n =
        (SSet.bkHocolim E).ιChainComplex (R := R)
          ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E n s).app
            (op ⦋n⦌) ((α.app s.1.left).app (op ⦋n⦌) x))) ∧
    (∀ p q, (((SSet.bkAlternatingBicomplexFunctor A R).map α).f p).f q =
      (sigmaConst.obj R).map
        ((((SSet.bkBarBisimplicialFunctor (J := J)).map α).app (op ⦋p⦌)).app
          (op ⦋q⦌))) ∧
    (∀ (p q : ℕ) (x : ((SSet.bkBarBisimplicial D).obj (op ⦋p⦌)).obj (op ⦋q⦌)),
      Sigma.ι (fun _ : ((SSet.bkBarBisimplicial D).obj (op ⦋p⦌)).obj
          (op ⦋q⦌) => R) x ≫
        (((SSet.bkAlternatingBicomplexFunctor A R).map α).f p).f q =
      Sigma.ι (fun _ : ((SSet.bkBarBisimplicial E).obj (op ⦋p⦌)).obj
          (op ⦋q⦌) => R)
        ((((SSet.bkBarBisimplicialFunctor (J := J)).map α).app (op ⦋p⦌)).app
          (op ⦋q⦌) x)) ∧
    (∀ p q, ((K D).X p).d (q + 1) q =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((B D).obj (op ⦋p⦌)).δ i) ∧
    (∀ p q, ((K D).d (p + 1) p).f q =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((B D).δ i).app (op ⦋q⦌)) ∧
    (∀ p q, SSet.bkAlternatingTotalι A R D p q ≫ T.f (p + q) =
      (((SSet.bkAlternatingBicomplexFunctor A R).map α).f p).f q ≫
        SSet.bkAlternatingTotalι A R E p q) ∧
    t ≫ (c E).hom = (c D).hom ≫ a ∧
    a ≫ (e E).hom = (e D).hom ≫ T ∧
    T ≫ (e E).inv = (e D).inv ≫ a ∧
    t ≫ (c E).hom ≫ (e E).hom = (c D).hom ≫ (e D).hom ≫ T ∧
    T ≫ (e E).inv ≫ (c E).inv = (e D).inv ≫ (c D).inv ≫ t ∧
    (∀ n, HomologicalComplex.homologyMap
      ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{max uJ vJ}).map
        ((SSet.coproductLinearizationFunctor AddCommGrpCat.{max uJ vJ} S).map
          (SSet.bkHocolimMap α))) n ≫ (SSet.bkDiagonalTotalHomologyIso S E n).hom =
      (SSet.bkDiagonalTotalHomologyIso S D n).hom ≫ HomologicalComplex.homologyMap
        ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{max uJ vJ} S).map α) n) ∧
    (∀ k : ℤ, cZ.hom (ULift.up (ULift.up k)) =
      ULift.up k) ∧
    (∀ (X : SSet.{max uJ vJ}) (n : ℕ) (x : X _⦋n⦌),
      AddCommGrpCat.uliftFunctor.{z, max uJ vJ}.map (X.ιChainComplex
        (R := AlgebraicTopology.singularIntegralCoefficients) x) ≫
          (Xi.app X).hom.f n =
        cZ.hom ≫ X.ιChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{max uJ vJ z})) x) ∧
    (∀ (X Y : SSet.{max uJ vJ}) (f : X ⟶ Y),
      ((AddCommGrpCat.uliftFunctor.{z, max uJ vJ}).mapHomologicalComplex (.down ℕ)).map
        (SSet.chainComplexMap f AlgebraicTopology.singularIntegralCoefficients) ≫
          (Xi.app Y).hom =
        (Xi.app X).hom ≫ SSet.chainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{max uJ vJ z})) ∧
    (∀ (X Y : SSet.{max uJ vJ}) (f : X ⟶ Y) (n : ℕ),
      AddCommGrpCat.uliftFunctor.{z, max uJ vJ}.map
        (SSet.homologyMap f AlgebraicTopology.singularIntegralCoefficients n) ≫
          (H Y n).hom =
        (H X n).hom ≫ SSet.homologyMap f
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{max uJ vJ z}) n) := by
  dsimp only
  refine ⟨SSet.bkHocolim_obj_mk D, SSet.bkHocolimMap_id D,
    SSet.bkHocolimMap_comp α β, ?_, ?_, ?_, ?_, ?_, ?_,
    SSet.bkCarrierChainIso_naturality A R α,
    SSet.bkDiagonalTotalHomotopyEquiv_hom_naturality A R α,
    SSet.bkDiagonalTotalHomotopyEquiv_inv_naturality A R α, ?_, ?_,
    SSet.bkDiagonalTotalHomologyIso_naturality S α, ?_, ?_, ?_, ?_⟩
  · intro n s x
    exact (SSet.ι_chainComplexMap_f (SSet.bkHocolim D) (SSet.bkHocolim E)
      (SSet.bkHocolimMap α) R _).trans
        (congrArg (fun y => (SSet.bkHocolim E).ιChainComplex (R := R) y)
          (SSet.bkHocolimMap_app_mk_ι_apply α n s x))
  · intro p q
    rfl
  · intro p q x
    change Sigma.ι (fun _ : ((SSet.bkBarBisimplicial D).obj
        (op ⦋p⦌)).obj (op ⦋q⦌) => R) x ≫ (sigmaConst.obj R).map _ = _
    simp [sigmaConst]
  · intro p q
    exact AlgebraicTopology.bisimplicialAlternatingBicomplex_vertical_d_eq_sum A _ p q
  · intro p q
    exact AlgebraicTopology.bisimplicialAlternatingBicomplex_horizontal_d_f_eq_sum A _ p q
  · intro p q
    exact HomologicalComplex₂.ιTotal_map
      (SSet.bkAlternatingBicomplex A R D) (SSet.bkAlternatingBicomplex A R E)
      ((SSet.bkAlternatingBicomplexFunctor A R).map α) (.down ℕ) p q (p + q) rfl
  · rw [← Category.assoc, SSet.bkCarrierChainIso_naturality,
      Category.assoc, SSet.bkDiagonalTotalHomotopyEquiv_hom_naturality,
      ← Category.assoc]
  · have hc := SSet.bkCarrierChainIso_naturality A R α
    have hinv :
        (AlgebraicTopology.alternatingFaceMapComplex A).map
            ((SSet.coproductLinearizationFunctor A R).map (SSet.bkHocolimMap α)) ≫
          (SSet.bkCarrierChainIso A R E).inv =
        (SSet.bkCarrierChainIso A R D).inv ≫
          SSet.chainComplexMap (SSet.bkHocolimMap α) R := by
      have h := congrArg (fun f =>
        (SSet.bkCarrierChainIso A R D).inv ≫ f ≫
          (SSet.bkCarrierChainIso A R E).inv) hc
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using h.symm
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ (SSet.bkCarrierChainIso A R E).inv)
        (SSet.bkDiagonalTotalHomotopyEquiv_inv_naturality A R α)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun f => (SSet.bkDiagonalTotalHomotopyEquiv A R D).inv ≫ f)
            hinv)))
  · intro k
    rfl
  · intro X n x
    exact integralChainIso_ι X x
  · intro X Y f
    exact (integralChainIso.{max uJ vJ, z}).hom.naturality f
  · intro X Y f n
    exact integralHomologyIso_naturality f n


end MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanCommonUniverseTests
