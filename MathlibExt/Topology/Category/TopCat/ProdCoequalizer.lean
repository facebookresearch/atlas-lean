/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import MathlibExt.Topology.Convenient.QuotientProduct
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat Topology

universe u

namespace TopCat

/-!
# Fixed-left product preserves TopCat coequalizers

For locally compact `K`, the functor `K ⨯ -` sends every coequalizer
cofork to a colimit cofork. The quotient half uses
`isQuotientMap_of_isColimit_cofork` with `IsQuotientMap.prodMap_right`;
the bijection half uses underlying-Type product preservation via the
cartesian-closed left-adjoint instance; the assembly uses the minimal
`Cofork.IsColimit.mk` universal property with quotient lift.
-/

/-- Fixed-left product of a coequalizer projection is a quotient map. -/
theorem isQuotientMap_prodMap_cofork_π_of_isColimit
    {K X Y : TopCat.{u}} [LocallyCompactSpace (↑K : Type u)]
    {f g : X ⟶ Y} (c : Cofork f g) (hc : IsColimit c) :
    IsQuotientMap ⇑(Limits.prod.map (𝟙 K) c.π : K ⨯ Y ⟶ K ⨯ c.pt) := by
  have hq : IsQuotientMap ⇑c.π := isQuotientMap_of_isColimit_cofork c hc
  have hqm : IsQuotientMap
      (Prod.map (id : ↑K → ↑K) ⇑c.π : ↑K × ↑Y → ↑K × ↑c.pt) :=
    hq.prodMap_right
  have hEq : ⇑(Limits.prod.map (𝟙 K) c.π : K ⨯ Y ⟶ K ⨯ c.pt) =
      ⇑(prodIsoProd K c.pt).inv ∘
        (Prod.map (id : ↑K → ↑K) ⇑c.π ∘ ⇑(prodIsoProd K Y).hom) := by
    funext p
    apply TopCat.prod_point_ext
    · have eLhs : (Limits.prod.fst : K ⨯ c.pt ⟶ K)
          ((Limits.prod.map (𝟙 K) c.π) p) =
          (𝟙 K : K ⟶ K) ((Limits.prod.fst : K ⨯ Y ⟶ K) p) :=
        CategoryTheory.ConcreteCategory.congr_hom
          (Limits.prod.map_fst (𝟙 K) c.π) p
      have eHom : (prodIsoProd K Y).hom p =
          ((Limits.prod.fst : K ⨯ Y ⟶ K) p,
            (Limits.prod.snd : K ⨯ Y ⟶ Y) p) :=
        prodIsoProd_hom_apply p
      have eInv : (Limits.prod.fst : K ⨯ c.pt ⟶ K)
          ((prodIsoProd K c.pt).inv
            (Prod.map (id : ↑K → ↑K) ⇑c.π ((prodIsoProd K Y).hom p))) =
          Prod.fst (Prod.map (id : ↑K → ↑K) ⇑c.π ((prodIsoProd K Y).hom p)) := by
        have h1 := CategoryTheory.ConcreteCategory.congr_hom
          (TopCat.prodIsoProd_inv_fst K c.pt)
          (Prod.map (id : ↑K → ↑K) ⇑c.π ((prodIsoProd K Y).hom p))
        simp only [CategoryTheory.ConcreteCategory.comp_apply] at h1
        rw [h1]
        rfl
      simp only [Function.comp_apply] at eInv ⊢
      rw [eInv, eHom]
      simp only [Prod.map_fst]
      have eId : (𝟙 K : K ⟶ K) ((Limits.prod.fst : K ⨯ Y ⟶ K) p) =
          (Limits.prod.fst : K ⨯ Y ⟶ K) p := rfl
      rw [eLhs, eId]
      rfl
    · have eLhs : (Limits.prod.snd : K ⨯ c.pt ⟶ c.pt)
          ((Limits.prod.map (𝟙 K) c.π) p) =
          c.π ((Limits.prod.snd : K ⨯ Y ⟶ Y) p) :=
        CategoryTheory.ConcreteCategory.congr_hom
          (Limits.prod.map_snd (𝟙 K) c.π) p
      have eHom : (prodIsoProd K Y).hom p =
          ((Limits.prod.fst : K ⨯ Y ⟶ K) p,
            (Limits.prod.snd : K ⨯ Y ⟶ Y) p) :=
        prodIsoProd_hom_apply p
      have eInv : (Limits.prod.snd : K ⨯ c.pt ⟶ c.pt)
          ((prodIsoProd K c.pt).inv
            (Prod.map (id : ↑K → ↑K) ⇑c.π ((prodIsoProd K Y).hom p))) =
          ⇑c.π (Prod.snd ((prodIsoProd K Y).hom p)) := by
        have h1 := CategoryTheory.ConcreteCategory.congr_hom
          (TopCat.prodIsoProd_inv_snd K c.pt)
          (Prod.map (id : ↑K → ↑K) ⇑c.π ((prodIsoProd K Y).hom p))
        simp only [CategoryTheory.ConcreteCategory.comp_apply] at h1
        rw [h1]
        rfl
      simp only [Function.comp_apply] at eInv ⊢
      rw [eInv, eHom]
      rw [eLhs]
  rw [hEq]
  have hSymmQ : IsQuotientMap ⇑(prodIsoProd K c.pt).inv :=
    (homeoOfIso (prodIsoProd K c.pt)).symm.isQuotientMap
  have hHomQ : IsQuotientMap ⇑(prodIsoProd K Y).hom :=
    (homeoOfIso (prodIsoProd K Y)).isQuotientMap
  exact hSymmQ.comp (hqm.comp hHomQ)

/-- Fixed-left product sends a coequalizer cofork to a colimit cofork. -/
@[nolint defsWithUnderscore] -- MathlibExtTest ProdCoequalizerTests uses this name.
noncomputable def isColimit_prodMap_cofork_of_isColimit
    {K X Y : TopCat.{u}} [LocallyCompactSpace (↑K : Type u)]
    {f g : X ⟶ Y} (c : Cofork f g) (hc : IsColimit c) :
    IsColimit
      (Cofork.ofπ (f := Limits.prod.map (𝟙 K) f) (g := Limits.prod.map (𝟙 K) g)
        (Limits.prod.map (𝟙 K) c.π : K ⨯ Y ⟶ K ⨯ c.pt)
        (by
          show Limits.prod.map (𝟙 K) f ≫ Limits.prod.map (𝟙 K) c.π =
            Limits.prod.map (𝟙 K) g ≫ Limits.prod.map (𝟙 K) c.π
          have e1 : Limits.prod.map (𝟙 K) f ≫ Limits.prod.map (𝟙 K) c.π =
              Limits.prod.map (𝟙 K ≫ 𝟙 K) (f ≫ c.π) := by
            rw [Limits.prod.map_map]
          have e2 : Limits.prod.map (𝟙 K) g ≫ Limits.prod.map (𝟙 K) c.π =
              Limits.prod.map (𝟙 K ≫ 𝟙 K) (g ≫ c.π) := by
            rw [Limits.prod.map_map]
          rw [e1, e2, Category.id_comp, c.condition])) := by
  classical
  let Pf := Limits.prod.map (𝟙 K) f
  let Pg := Limits.prod.map (𝟙 K) g
  let Pq := Limits.prod.map (𝟙 K) c.π
  have hPq : IsQuotientMap (Pq.hom : C(↑(K ⨯ Y), ↑(K ⨯ c.pt))) :=
    isQuotientMap_prodMap_cofork_π_of_isColimit c hc
  haveI hEpi : Epi (Pq : K ⨯ Y ⟶ K ⨯ c.pt) :=
    (epi_iff_surjective _).mpr hPq.surjective
  -- Underlying-Type product colimit via cartesian-closed preservation.
  let Fforget := forget TopCat
  let S := Fforget.obj K
  let PType := Limits.prod.functor.obj S
  have hcT : IsColimit (Fforget.mapCocone c) :=
    isColimitOfPreserves Fforget hc
  have hPT : IsColimit (PType.mapCocone (Fforget.mapCocone c)) :=
    isColimitOfPreserves PType hcT
  -- Transport the Type colimit to the underlying product cofork.
  have hUnder : IsColimit
      (Cofork.ofπ (f := Fforget.map Pf) (g := Fforget.map Pg)
        (Fforget.map Pq : Fforget.obj (K ⨯ Y) ⟶ Fforget.obj (K ⨯ c.pt))
        (by
          change Fforget.map (Limits.prod.map (𝟙 K) f) ≫
              Fforget.map (Limits.prod.map (𝟙 K) c.π) =
            Fforget.map (Limits.prod.map (𝟙 K) g) ≫
              Fforget.map (Limits.prod.map (𝟙 K) c.π)
          simp only [← Functor.map_comp]
          have e1 : Limits.prod.map (𝟙 K) f ≫ Limits.prod.map (𝟙 K) c.π =
              Limits.prod.map (𝟙 K ≫ 𝟙 K) (f ≫ c.π) := by
            rw [Limits.prod.map_map]
          have e2 : Limits.prod.map (𝟙 K) g ≫ Limits.prod.map (𝟙 K) c.π =
              Limits.prod.map (𝟙 K ≫ 𝟙 K) (g ≫ c.π) := by
            rw [Limits.prod.map_map]
          rw [e1, e2, Category.id_comp, Cofork.condition c])) := by
    have hFc : IsColimit
        (Cofork.ofπ (f := Fforget.map f) (g := Fforget.map g)
          (Fforget.map c.π : Fforget.obj Y ⟶ Fforget.obj c.pt)
          (by simp only [← Functor.map_comp]; rw [Cofork.condition c])) :=
      (isColimitMapCoconeCoforkEquiv Fforget (Cofork.condition c))
        (isColimitOfPreserves Fforget (hc.ofIsoColimit (Cofork.isoCoforkOfπ c)))
    have hF : Fforget.map f ≫ Fforget.map c.π =
        Fforget.map g ≫ Fforget.map c.π := by
      simp only [← Functor.map_comp]; rw [Cofork.condition c]
    have hPTπ : IsColimit
        (Cofork.ofπ (f := PType.map (Fforget.map f)) (g := PType.map (Fforget.map g))
          (PType.map (Fforget.map c.π) :
            PType.obj (Fforget.obj Y) ⟶ PType.obj (Fforget.obj c.pt))
          (by simp only [← Functor.map_comp, hF])) :=
      isColimitCoforkMapOfIsColimit PType hF hFc
    -- Transport along naturality of the product-comparison iso.
    -- Keep everything in functorial form so domains match syntactically.
    let eX := (Limits.prodComparisonNatIso Fforget K).app X
    let eY := (Limits.prodComparisonNatIso Fforget K).app Y
    let eQ := (Limits.prodComparisonNatIso Fforget K).app c.pt
    have hnat_f := (Limits.prodComparisonNatIso Fforget K).hom.naturality f
    have hnat_g := (Limits.prodComparisonNatIso Fforget K).hom.naturality g
    have hnat_q := (Limits.prodComparisonNatIso Fforget K).hom.naturality c.π
    have comm1 : eX.symm.hom ≫ Fforget.map Pf = PType.map (Fforget.map f) ≫ eY.symm.hom := by
      have h := hnat_f
      change (Limits.prod.functor.obj K ⋙ Fforget).map f ≫ eY.hom =
        eX.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map f at h
      change eX.inv ≫ (Limits.prod.functor.obj K ⋙ Fforget).map f =
        (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map f ≫ eY.inv
      rw [Iso.inv_comp_eq]
      have h2 : ((Limits.prod.functor.obj K ⋙ Fforget).map f ≫ eY.hom) ≫ eY.inv =
          (eX.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map f) ≫ eY.inv := by
        rw [h]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
      exact h2
    have comm2 : eX.symm.hom ≫ Fforget.map Pg = PType.map (Fforget.map g) ≫ eY.symm.hom := by
      have h := hnat_g
      change (Limits.prod.functor.obj K ⋙ Fforget).map g ≫ eY.hom =
        eX.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map g at h
      change eX.inv ≫ (Limits.prod.functor.obj K ⋙ Fforget).map g =
        (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map g ≫ eY.inv
      rw [Iso.inv_comp_eq]
      have h2 : ((Limits.prod.functor.obj K ⋙ Fforget).map g ≫ eY.hom) ≫ eY.inv =
          (eX.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map g) ≫ eY.inv := by
        rw [h]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
      exact h2
    have comm3 : eY.symm.inv ≫ PType.map (Fforget.map c.π) ≫ eQ.symm.hom =
        Fforget.map Pq := by
      have h := hnat_q
      change (Limits.prod.functor.obj K ⋙ Fforget).map c.π ≫ eQ.hom =
        eY.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map c.π at h
      change eY.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map c.π ≫ eQ.inv =
        (Limits.prod.functor.obj K ⋙ Fforget).map c.π
      have hsym : eY.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map c.π =
          (Limits.prod.functor.obj K ⋙ Fforget).map c.π ≫ eQ.hom := h.symm
      calc eY.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map c.π ≫ eQ.inv
          = (eY.hom ≫ (Fforget ⋙ Limits.prod.functor.obj (Fforget.obj K)).map c.π) ≫ eQ.inv := by
            rw [Category.assoc]
        _ = ((Limits.prod.functor.obj K ⋙ Fforget).map c.π ≫ eQ.hom) ≫ eQ.inv := by
            rw [hsym]
        _ = (Limits.prod.functor.obj K ⋙ Fforget).map c.π ≫ (eQ.hom ≫ eQ.inv) := by
            rw [← Category.assoc]
        _ = (Limits.prod.functor.obj K ⋙ Fforget).map c.π ≫ 𝟙 _ := by
            rw [Iso.hom_inv_id]
        _ = (Limits.prod.functor.obj K ⋙ Fforget).map c.π := by
            rw [Category.comp_id]
    exact Cofork.isColimitOfIsos _ hPTπ _ eX.symm eY.symm eQ.symm comm1 comm2 comm3
  -- Every test leg factors through the quotient projection on underlying types.
  have key : ∀ s : Cofork Pf Pg, Function.FactorsThrough ⇑s.π ⇑Pq := by
    intro s
    let sT : Cofork (Fforget.map Pf) (Fforget.map Pg) :=
      Cofork.ofπ (f := Fforget.map Pf) (g := Fforget.map Pg)
        (Fforget.map s.π : Fforget.obj (K ⨯ Y) ⟶ Fforget.obj s.pt)
        (by
          have hcond := Cofork.condition s
          simp only [← Functor.map_comp]
          exact congrArg Fforget.map hcond)
    obtain ⟨dT, hdT⟩ := Cofork.IsColimit.desc' hUnder sT.π sT.condition
    intro a b hab
    have ha : ⇑s.π a = dT (⇑Pq a) := by
      have h := ConcreteCategory.congr_hom hdT a
      rw [ConcreteCategory.comp_apply] at h
      exact h.symm
    have hb : ⇑s.π b = dT (⇑Pq b) := by
      have h := ConcreteCategory.congr_hom hdT b
      rw [ConcreteCategory.comp_apply] at h
      exact h.symm
    rw [ha, hb, hab]
  apply Cofork.IsColimit.mk'
  intro s
  have hFac : Function.FactorsThrough s.π.hom Pq.hom := key s
  have hPqC : IsQuotientMap Pq.hom := hPq
  let lC : C(↑(K ⨯ c.pt), ↑s.pt) := hPqC.lift s.π.hom hFac
  have hfac : Pq ≫ ConcreteCategory.ofHom lC = s.π := by
    apply TopCat.hom_ext
    exact hPqC.lift_comp s.π.hom hFac
  refine ⟨ConcreteCategory.ofHom lC, hfac, fun {m'} hm' => ?_⟩
  apply (cancel_epi (Pq : K ⨯ Y ⟶ K ⨯ c.pt)).mp
  have hmP : Pq ≫ m' = s.π := hm'
  rw [hmP, ← hfac]

/-- Fixed-left product preserves `WalkingParallelPair` colimits. -/
instance preservesColimitsOfShape_walkingParallelPair_prodLeft
    (K : TopCat.{u}) [LocallyCompactSpace (↑K : Type u)] :
    PreservesColimitsOfShape WalkingParallelPair (Limits.prod.functor.obj K) := by
  constructor
  intro F
  suffices h : PreservesColimit
      (parallelPair (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right))
      (Limits.prod.functor.obj K) from
    preservesColimit_of_iso_diagram _ (diagramIsoParallelPair F).symm
  apply preservesColimit_of_preserves_colimit_cocone (coequalizerIsCoequalizer _ _)
  apply (isColimitMapCoconeCoforkEquiv _ _).symm _
  exact isColimit_prodMap_cofork_of_isColimit
    (Cofork.ofπ (coequalizer.π _ _) (coequalizer.condition _ _))
    (coequalizerIsCoequalizer _ _)

end TopCat
