/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowCoreComponent
public import MathlibExt.CategoryTheory.ConnectedComponents.NerveDecomposition
public import MathlibExt.CategoryTheory.NerveCommonHom
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.Coproducts
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-!
# Injectivity of the actual original finite-row core homology map

The original projective core is the disjoint union of its actual categorical
components. The established nerve decomposition and homology coproduct
comparison therefore split each component inclusion on homology. The
derived finite-GL/component equivalence identifies the SAME original row
map with such an inclusion. Its homology map is consequently monic in
every degree and for every fixed coefficient group.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private abbrev rowCore := Core (FGProjectiveCat.IdempotentModel R)

private abbrev rowCoreComponent (c : CategoryTheory.ConnectedComponents (rowCore R)) := c.Component

private def rowCoreComponentSumNerveIso :
    (∐ fun c : CategoryTheory.ConnectedComponents (rowCore R) => nerve (rowCoreComponent R c)) ≅
      nerve (rowCore R) :=
  NerveDecomposition.nerveSigmaIso (C := fun c : CategoryTheory.ConnectedComponents (rowCore R) =>
    rowCoreComponent R c) ≪≫ decomposedNerveIso (rowCore R)

private theorem rowCoreComponentSumNerveIso_ι (c : CategoryTheory.ConnectedComponents (rowCore R)) :
    Sigma.ι (fun d : CategoryTheory.ConnectedComponents (rowCore R) => nerve (rowCoreComponent R d)) c ≫
        (rowCoreComponentSumNerveIso R).hom =
      nerveMap (CategoryTheory.ConnectedComponents.ι c) := by
  let E := NerveDecomposition.nerveSigmaIso
    (C := fun d : CategoryTheory.ConnectedComponents (rowCore R) => rowCoreComponent R d)
  let D := decomposedNerveIso (rowCore R)
  change Sigma.ι (fun d : CategoryTheory.ConnectedComponents (rowCore R) => nerve (rowCoreComponent R d)) c ≫
      (E.hom ≫ D.hom) = _
  rw [← Category.assoc, NerveDecomposition.nerveSigmaIso_ι,
    decomposedNerveIso_hom, nerveMap_comp, inclusion_comp_decomposedTo]

private def rowCoreComponentHomologyIso (A : AddCommGrpCat.{u}) (q : ℕ) :
    (nerve (rowCore R)).homology (C := AddCommGrpCat.{u}) A q ≅
      ∐ fun c : CategoryTheory.ConnectedComponents (rowCore R) =>
        (nerve (rowCoreComponent R c)).homology (C := AddCommGrpCat.{u}) A q :=
  (SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).mapIso (rowCoreComponentSumNerveIso R).symm ≪≫
    SSet.homologySigmaIso
      (fun c : CategoryTheory.ConnectedComponents (rowCore R) => nerve (rowCoreComponent R c)) A q

private theorem rowCoreComponentHomologyIso_ι
    (A : AddCommGrpCat.{u}) (q : ℕ) (c : CategoryTheory.ConnectedComponents (rowCore R)) :
    SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (CategoryTheory.ConnectedComponents.ι c)) A q ≫
        (rowCoreComponentHomologyIso R A q).hom =
      Sigma.ι (fun d : CategoryTheory.ConnectedComponents (rowCore R) =>
        (nerve (rowCoreComponent R d)).homology (C := AddCommGrpCat.{u}) A q) c := by
  let E := rowCoreComponentSumNerveIso R
  let F := fun d : CategoryTheory.ConnectedComponents (rowCore R) => nerve (rowCoreComponent R d)
  have hBack : nerveMap (CategoryTheory.ConnectedComponents.ι c) ≫ E.inv = Sigma.ι F c := by
    calc
      _ = (Sigma.ι F c ≫ E.hom) ≫ E.inv :=
        congrArg (fun f => f ≫ E.inv) (rowCoreComponentSumNerveIso_ι R c).symm
      _ = Sigma.ι F c := by
        rw [Category.assoc, E.hom_inv_id, Category.comp_id]
  change SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (CategoryTheory.ConnectedComponents.ι c)) A q ≫
      SSet.homologyMap (C := AddCommGrpCat.{u}) E.inv A q ≫ (SSet.homologySigmaIso F A q).hom = _
  rw [← Category.assoc, ← SSet.homologyMap_comp, hBack]
  exact SSet.homologyMap_ι_comp_homologySigmaIso_hom F A q c

private def rowCoreComponentHomologySplitMono
    (A : AddCommGrpCat.{u}) (q : ℕ) (c : CategoryTheory.ConnectedComponents (rowCore R)) :
    SplitMono (SSet.homologyMap (C := AddCommGrpCat.{u})
      (nerveMap (CategoryTheory.ConnectedComponents.ι c)) A q) where
  retraction := (rowCoreComponentHomologyIso R A q).hom ≫
    retraction (Sigma.ι (fun d : CategoryTheory.ConnectedComponents (rowCore R) =>
      (nerve (rowCoreComponent R d)).homology (C := AddCommGrpCat.{u}) A q) c)
  id := by
    rw [← Category.assoc, rowCoreComponentHomologyIso_ι]
    simp

/-- The SAME original row functor mapped to the nerve of its computed
categorical component, through the established common-Hom-universe map. -/
public def finiteFreeRowCoreComponentNerveMap (n : ℕ) :
    nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⟶
      nerve ((CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).Component) :=
  nerveMapCommonHomUp.{0, u, 0} (finiteFreeRowCoreComponentFunctor R n)

/-- The original component nerve map followed by the actual component
inclusion is precisely the ORIGINAL finite-stage core nerve map. -/
public theorem finiteFreeRowCoreComponentNerveMap_comp_inclusion (n : ℕ) :
    finiteFreeRowCoreComponentNerveMap R n ≫
        nerveMap (CategoryTheory.ConnectedComponents.ι
          (CategoryTheory.ConnectedComponents.mk
            (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))) =
      finiteFreeRowStageCoreNerveMap R n := by
  ext Δ X
  have h := congrArg
    (fun F : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤ rowCore R =>
      (F.mapComposableArrows Δ.unop.len).obj X)
    (finiteFreeRowCoreComponentFunctor_comp_inclusion R n)
  let L : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤ rowCore R :=
    finiteFreeRowCoreComponentFunctor R n ⋙ CategoryTheory.ConnectedComponents.ι
      (CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))
  change (L.mapComposableArrows Δ.unop.len).obj X = _
  exact h.trans (finiteFreeRowStageCoreNerveMap_app R n Δ X).symm

/-- The actual finite-row/component homology Iso induced by the derived
category equivalence and its original unit/counit nerve homotopies. -/
public def finiteFreeRowCoreComponentHomologyIso
    (A : AddCommGrpCat.{u}) (q n : ℕ) :
    (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology (C := AddCommGrpCat.{u})
      A q ≅
      (nerve ((CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).Component)).homology
          (C := AddCommGrpCat.{u}) A q := by
  let e := finiteFreeRowCoreComponentEquivalence R n
  let f := nerveMapCommonHomUp.{0, u, 0} e.functor
  let g := nerveMapCommonHom.{0, u, 0} e.inverse
  have hUnit : SSet.homologyMap (C := AddCommGrpCat.{u})
    (nerveMap (e.functor ⋙ e.inverse)) A q = 𝟙 _ := by
    have h := (NatTrans.nerveHomotopy e.unitIso.hom).congr_homologyMap A q
    calc
      _ = SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (𝟭 _)) A q := h.symm
      _ = 𝟙 _ := by
        rw [nerveMap_id]
        exact (SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).map_id _
  have hCounit : SSet.homologyMap (C := AddCommGrpCat.{u})
    (nerveMap (e.inverse ⋙ e.functor)) A q = 𝟙 _ := by
    have h := (NatTrans.nerveHomotopy e.counitIso.hom).congr_homologyMap A q
    calc
      _ = SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (𝟭 _)) A q := h
      _ = 𝟙 _ := by
        rw [nerveMap_id]
        exact (SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).map_id _
  refine
    { hom := SSet.homologyMap (C := AddCommGrpCat.{u}) f A q
      inv := SSet.homologyMap (C := AddCommGrpCat.{u}) g A q
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · have hfg : f ≫ g = nerveMap (e.functor ⋙ e.inverse) :=
      nerveMapCommonHomUp_comp.{0, u, 0} e.functor e.inverse
    have hComp :
        SSet.homologyMap (C := AddCommGrpCat.{u}) f A q ≫
          SSet.homologyMap (C := AddCommGrpCat.{u}) g A q =
        SSet.homologyMap (C := AddCommGrpCat.{u}) (f ≫ g) A q :=
      ((SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).map_comp f g).symm
    have hMap : SSet.homologyMap (C := AddCommGrpCat.{u}) (f ≫ g) A q =
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (e.functor ⋙ e.inverse)) A q :=
      congrArg
        (fun h : nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⟶
            nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =>
          SSet.homologyMap (C := AddCommGrpCat.{u}) h A q) hfg
    exact hComp.trans (hMap.trans hUnit)
  · have hgf : g ≫ f = nerveMap (e.inverse ⋙ e.functor) :=
      nerveMapCommonHom_comp_up.{0, u, 0} e.inverse e.functor
    have hComp :
        SSet.homologyMap (C := AddCommGrpCat.{u}) g A q ≫
          SSet.homologyMap (C := AddCommGrpCat.{u}) f A q =
        SSet.homologyMap (C := AddCommGrpCat.{u}) (g ≫ f) A q :=
      ((SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).map_comp g f).symm
    let Y : SSet.{u} := nerve
      ((CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).Component)
    have hMap : SSet.homologyMap (C := AddCommGrpCat.{u}) (g ≫ f) A q =
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (e.inverse ⋙ e.functor)) A q :=
      congrArg (fun h : Y ⟶ Y => SSet.homologyMap (C := AddCommGrpCat.{u}) h A q) hgf
    exact hComp.trans (hMap.trans hCounit)

/-- The forward homology Iso is the SAME original component nerve map. -/
private theorem finiteFreeRowCoreComponentHomologyIso_hom_computation07 (A : AddCommGrpCat.{u}) (q n : ℕ) :
    (finiteFreeRowCoreComponentHomologyIso R A q n).hom =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowCoreComponentNerveMap R n) A q := by
  unfold finiteFreeRowCoreComponentHomologyIso
  change SSet.homologyMap (C := AddCommGrpCat.{u})
      (nerveMapCommonHomUp.{0, u, 0} (finiteFreeRowCoreComponentEquivalence R n).functor) A q = _
  rw [finiteFreeRowCoreComponentEquivalence_functor]
  rfl

public theorem finiteFreeRowCoreComponentHomologyIso_hom (A : AddCommGrpCat.{u}) (q n : ℕ) :
    (finiteFreeRowCoreComponentHomologyIso R A q n).hom =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowCoreComponentNerveMap R n) A q :=
  finiteFreeRowCoreComponentHomologyIso_hom_computation07 R A q n

/-- In EVERY degree the ORIGINAL finite-row core homology map is monic.
This is derived from its actual component equivalence and the original
component coproduct splitting, with no homology or connectedness input. -/
public theorem finiteFreeRowStageCoreHomology_mono
    (A : AddCommGrpCat.{u}) (q n : ℕ) :
    Mono (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q) := by
  let c := CategoryTheory.ConnectedComponents.mk
    (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))
  let j := nerveMap (CategoryTheory.ConnectedComponents.ι c)
  let m := SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowCoreComponentNerveMap R n) A q
  letI : IsIso m := by
    let e := finiteFreeRowCoreComponentHomologyIso R A q n
    have hMap : e.hom = m := finiteFreeRowCoreComponentHomologyIso_hom R A q n
    exact hMap ▸ e.isIso_hom
  letI : IsSplitMono (SSet.homologyMap (C := AddCommGrpCat.{u}) j A q) :=
    IsSplitMono.mk' (rowCoreComponentHomologySplitMono R A q c)
  have h : SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q =
      m ≫ SSet.homologyMap (C := AddCommGrpCat.{u}) j A q := by
    exact (congrArg (fun f => SSet.homologyMap (C := AddCommGrpCat.{u}) f A q)
      (finiteFreeRowCoreComponentNerveMap_comp_inclusion R n)).symm.trans
        ((SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).map_comp _ _)
  rw [h]
  infer_instance

end AlgebraicKTheory.StableGL
