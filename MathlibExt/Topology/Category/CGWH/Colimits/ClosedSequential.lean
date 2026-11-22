/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellTransfinite
public import MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedSequentialColimit
public import Mathlib.Order.Lattice
public import Mathlib.Order.WellFounded

/-!
# Closed sequential colimits of compactly generated weak Hausdorff spaces

For a sequence with closed transition embeddings, the chosen native CGWH
colimit cocone remains colimiting in compactly generated spaces and in
`TopCat`. Its actual legs are closed embeddings. Every continuous map from
an independently sized compact space factors through a stage, and the stage
can be chosen after any prescribed index.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits Topology

namespace CGWH.ClosedSequentialColimit

/-- The actual included Nat cocone is colimiting, with independent native universes. -/
def isColimitCompactlyGenerated {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f))) :
    IsColimit (CGWH.cgwhToCompactlyGenerated.mapCocone c) := by
  let e : ULift.{v} ℕ ≃o ℕ := ULift.orderIso
  let _ : SuccOrder (ULift.{v} ℕ) := SuccOrder.ofOrderIso e.symm
  let D := e.equivalence.functor ⋙ F
  let d := c.whisker e.equivalence.functor
  have hd : IsColimit d := hc.whiskerEquivalence e.equivalence
  have hD : ∀ (a : ULift.{v} ℕ) (_ha : ¬ IsMax a), Function.Injective
      (CGWH.cgwhToCompactlyGenerated.map
        (D.map (homOfLE (Order.le_succ a)))).hom := by
    intro a ha
    exact (hF (e.equivalence.functor.map (homOfLE (Order.le_succ a)))).injective
  have hMapped := CGWH.isColimitMapCoconeOfInjectiveSucc D hD d hd
  exact IsColimit.ofWhiskerEquivalence e.equivalence
    (IsColimit.ofIsoColimit hMapped (Functor.mapCoconeWhisker _))

/-- The same complete native Nat cocone is colimiting after the actual TopCat inclusion. -/
def isColimitTop {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f))) :
    IsColimit (CGWH.cgwhToTop.mapCocone c) := by
  have h := isColimitOfPreserves CompactlyGenerated.compactlyGeneratedToTop
    (isColimitCompactlyGenerated c hc hF)
  exact IsColimit.ofIsoColimit h (Cocone.ext (Iso.refl _))

/-- Genuine native T1 makes every closed transition a closed-T1 embedding. -/
theorem map_closedT1 {F : ℕ ⥤ CGWH.{u, v}}
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    {i j : ℕ} (f : i ⟶ j) : TopCat.closedT1Embeddings ((F ⋙ cgwhToTop).map f) := by
  exact { toIsClosedEmbedding := hF f
          isClosed_singleton_of_notMem_range := fun y _hy => by
            change IsClosed ({y} : Set (F.obj j))
            exact isClosed_singleton }

/-- Every actual colimit leg is a closed embedding. -/
theorem leg_isClosedEmbedding {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f))) (n : ℕ) :
    IsClosedEmbedding (cgwhToTop.map (c.ι.app n)).hom :=
  TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding
    (cgwhToTop.mapCocone c) (isColimitTop c hc hF) hF n

/-- Actual compact maps factor through the same chosen leg. -/
theorem exists_stage_of_compact {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    {K : Type w} [TopologicalSpace K] (hK : IsCompact (Set.univ : Set K))
    (f : C(K, cgwhToTop.obj c.pt)) :
    ∃ (n : ℕ) (g : C(K, cgwhToTop.obj (F.obj n))),
      (cgwhToTop.map (c.ι.app n)).hom.comp g = f :=
  TopCat.exists_stage_of_compact (cgwhToTop.mapCocone c) (isColimitTop c hc hF)
    (fun _ _ φ => map_closedT1 hF φ) hK f

/-- The actual factor can be chosen beyond any prescribed stage. -/
theorem exists_later_stage_of_compact {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    {K : Type w} [TopologicalSpace K] (hK : IsCompact (Set.univ : Set K))
    (f : C(K, cgwhToTop.obj c.pt)) (n₀ : ℕ) :
    ∃ (n : ℕ), n₀ ≤ n ∧ ∃ (g : C(K, cgwhToTop.obj (F.obj n))),
      (cgwhToTop.map (c.ι.app n)).hom.comp g = f := by
  obtain ⟨j, g, hg⟩ := exists_stage_of_compact c hc hF hK f
  let φ : j ⟶ max n₀ j := homOfLE (le_max_right n₀ j)
  refine ⟨max n₀ j, le_max_left _ _, (cgwhToTop.map (F.map φ)).hom.comp g, ?_⟩
  calc
    _ = (cgwhToTop.map (F.map φ ≫ c.ι.app (max n₀ j))).hom.comp g := by
      rw [Functor.map_comp]
      rfl
    _ = (cgwhToTop.map (c.ι.app j)).hom.comp g := by rw [c.w φ]
    _ = f := hg


/-- Compare the chosen topological colimit with the included native cocone point. -/
def topComparisonIso {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f))) :
    Limits.colimit (F ⋙ cgwhToTop) ≅ cgwhToTop.obj c.pt :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitTop c hc hF)

/-- The forward comparison sends every stage leg to the chosen native leg. -/
@[reassoc]
theorem topComparisonIso_hom_ι {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (j : ℕ) : colimit.ι (F ⋙ cgwhToTop) j ≫ (topComparisonIso c hc hF).hom =
      cgwhToTop.map (c.ι.app j) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) (isColimitTop c hc hF) j

/-- The inverse comparison sends every native leg back to the chosen colimit leg. -/
@[reassoc]
theorem topComparisonIso_inv_ι {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (j : ℕ) : cgwhToTop.map (c.ι.app j) ≫ (topComparisonIso c hc hF).inv =
      colimit.ι (F ⋙ cgwhToTop) j :=
  IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _) (isColimitTop c hc hF) j

/-- The whole comparison is natural for maps of the same native cocones. -/
theorem topComparisonIso_naturality {F G : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (G.map f)))
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    colim.map (Functor.whiskerRight a cgwhToTop) ≫ (topComparisonIso d hd hG).hom =
      (topComparisonIso c hc hF).hom ≫ cgwhToTop.map g := by
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_map_assoc, topComparisonIso_hom_ι, ← Category.assoc,
    topComparisonIso_hom_ι]
  exact ((cgwhToTop.map_comp _ _).symm.trans
    ((cgwhToTop.congr_map (hg j)).trans (cgwhToTop.map_comp _ _))).symm

/-- The complete inverse comparison has the same cocone-map naturality. -/
theorem topComparisonIso_inv_naturality {F G : ℕ ⥤ CGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (G.map f)))
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    cgwhToTop.map g ≫ (topComparisonIso d hd hG).inv =
      (topComparisonIso c hc hF).inv ≫ colim.map (Functor.whiskerRight a cgwhToTop) := by
  apply (cancel_mono (topComparisonIso d hd hG).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    topComparisonIso_naturality c d hc hd hF hG a g hg, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end CGWH.ClosedSequentialColimit
