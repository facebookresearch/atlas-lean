/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.Colimits.ClosedSequential
import MathlibExt.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Homotopy groups of pointed closed sequential colimits

Compact cube representatives and compact relative homotopies prove that
literal-degree homotopy types preserve closed sequential colimit cocones.
The Type comparison includes degree zero. Positive groups use the actual
filtered group quotient at degree `n + 1`. The comparison isomorphisms
retain every stage representative, both inverse maps, and naturality for
arbitrary maps of the chosen native cocones.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC uJ vJ
open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval Topology.Homotopy

namespace CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C] {J : Type uJ} [Category.{vJ} J]
  [HasColimitsOfShape J C]

private theorem closedSequential_colimitPointIso_naturality {F G : J ⥤ C}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : J, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    colim.map a ≫ ((colimit.isColimit G).coconePointUniqueUpToIso hd).hom =
      ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom ≫ g := by
  apply colimit.hom_ext
  intro j
  have hec : colimit.ι F j ≫ ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom =
      c.ι.app j := IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) hc j
  have hed : colimit.ι G j ≫ ((colimit.isColimit G).coconePointUniqueUpToIso hd).hom =
      d.ι.app j := IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit G) hd j
  rw [colimit.ι_map_assoc, hed, ← Category.assoc, hec]
  exact (hg j).symm

end CategoryTheory.Limits

namespace CategoryTheory

private theorem closedSequential_inverse_naturality {C : Type uC} [Category.{vC} C]
    {A B D E : C} (s : A ≅ B) (t : D ≅ E) (f : A ⟶ D) (g : B ⟶ E)
    (h : f ≫ t.hom = s.hom ≫ g) : g ≫ t.inv = s.inv ≫ f := by
  apply (Iso.comp_inv_eq t).2
  have h' : s.inv ≫ (f ≫ t.hom) = g := (Iso.inv_comp_eq s).2 h
  exact h'.symm.trans (Category.assoc s.inv f t.hom).symm

end CategoryTheory

namespace GrpCat.FilteredColimits

private theorem closedSequential_desc_map_naturality {F G : ℕ ⥤ GrpCat.{v}}
    (c : Cocone F) (d : Cocone G) (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    colimitMap a ≫ (colimitCoconeIsColimit G).desc d =
      (colimitCoconeIsColimit F).desc c ≫ g := by
  apply (colimitCoconeIsColimit F).hom_ext
  intro j
  have hF := (colimitCoconeIsColimit F).fac c j
  have hG := (colimitCoconeIsColimit G).fac d j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun r => r ≫ (colimitCoconeIsColimit G).desc d)
      (colimitMap_ι a j)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun r => a.app j ≫ r) hG).trans
            ((hg j).symm.trans
              ((congrArg (fun r => r ≫ g) hF.symm).trans (Category.assoc _ _ _))))))

end GrpCat.FilteredColimits

namespace PointedCGWH.SequentialHomotopyColimit
open PointedCGWH.ClosedSequentialColimit PointedCGWH.CubeColimitGeometry

/-- Every piN class has an actual stage representative. -/
theorem piN_stage_exists (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (a : piN n c.pt) :
    ∃ (j : ℕ) (b : piN n (F.obj j)), piNMap n (c.ι.app j) b = a := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨j, _hj, q, hq⟩ := cube_stage_factor n c hc hF p 0
  exact ⟨j, HomotopyGroup.mk q, (piNMap_mk n (c.ι.app j) q).trans
    (congrArg HomotopyGroup.mk hq)⟩

/-- Original piN equality is witnessed at an actual common later stage. -/
theorem piN_eventual_eq (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (i j : ℕ) (a : piN n (F.obj i)) (b : piN n (F.obj j))
    (hab : piNMap n (c.ι.app i) a = piNMap n (c.ι.app j) b) :
    ∃ (k : ℕ) (f : i ⟶ k) (g : j ⟶ k), piNMap n (F.map f) a = piNMap n (F.map g) b := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective b
  have h : GenLoop.Homotopic (cubeMap n (c.ι.app i) p) (cubeMap n (c.ι.app j) q) :=
    Quotient.exact ((piNMap_mk n (c.ι.app i) p).symm.trans
      (hab.trans (piNMap_mk n (c.ι.app j) q)))
  obtain ⟨H⟩ := h
  obtain ⟨k, hik, hjk, Hk, _hmap⟩ := relative_homotopy_stage_factor n c hc hF i j p q H
  have heq : HomotopyGroup.mk (cubeMap n (F.map (homOfLE hik)) p) =
      HomotopyGroup.mk (cubeMap n (F.map (homOfLE hjk)) q) := Quotient.sound ⟨Hk⟩
  exact ⟨k, homOfLE hik, homOfLE hjk, (piNMap_mk n (F.map (homOfLE hik)) p).trans
    (heq.trans (piNMap_mk n (F.map (homOfLE hjk)) q).symm)⟩

/--
The all-degree homotopy functor carries the actual closed Nat cocone to a colimit.
-/
def piNIsColimit (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    IsColimit ((piNFunctor n).mapCocone c) := by
  apply Types.FilteredColimit.isColimitOf
  · intro a
    obtain ⟨j, b, hb⟩ := piN_stage_exists n c hc hF a
    exact ⟨j, b, hb.symm⟩
  · intro i j a b hab
    exact piN_eventual_eq n c hc hF i j a b hab

/-- Both actual Type colimit points are retained by the whole comparison Iso. -/
def piNComparisonIso (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    colimit (F ⋙ piNFunctor n) ≅ piN n c.pt :=
  (colimit.isColimit _).coconePointUniqueUpToIso (piNIsColimit n c hc hF)

/-- Every actual piN stage map is the full forward comparison leg. -/
theorem piNComparisonIso_hom_ι (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (j : ℕ) :
    colimit.ι (F ⋙ piNFunctor n) j ≫ (piNComparisonIso n c hc hF).hom =
      (piNFunctor n).map (c.ι.app j) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (piNIsColimit n c hc hF) j

/-- Every piN stage map is retained by the full inverse comparison leg. -/
theorem piNComparisonIso_inv_ι (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (j : ℕ) :
    (piNFunctor n).map (c.ι.app j) ≫ (piNComparisonIso n c hc hF).inv =
      colimit.ι (F ⋙ piNFunctor n) j :=
  IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _)
    (piNIsColimit n c hc hF) j

/-- The complete Type comparison preserves every actual pointed cocone-map square. -/
theorem piNComparisonIso_naturality (n : ℕ) {F G : ℕ ⥤ PointedCGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (G.map f).right))
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    colim.map (Functor.whiskerRight a (piNFunctor n)) ≫ (piNComparisonIso n d hd hG).hom =
      (piNComparisonIso n c hc hF).hom ≫ (piNFunctor n).map g := by
  apply CategoryTheory.Limits.closedSequential_colimitPointIso_naturality
    ((piNFunctor n).mapCocone c) ((piNFunctor n).mapCocone d)
    (piNIsColimit n c hc hF) (piNIsColimit n d hd hG)
  intro j
  exact ((piNFunctor n).map_comp _ _).symm.trans
    (((piNFunctor n).congr_map (hg j)).trans ((piNFunctor n).map_comp _ _))

/--
The actual filtered group universal property constructs the positive comparison.
-/
def piNPositiveComparison (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F) :
    GrpCat.FilteredColimits.colimit (F ⋙ piNPositiveFunctor n) ⟶
      (piNPositiveFunctor n).obj c.pt :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ piNPositiveFunctor n)).desc
    ((piNPositiveFunctor n).mapCocone c)

/-- Every actual positive group stage map is the full comparison leg. -/
theorem piNPositiveComparison_ι (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F) (j : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (F ⋙ piNPositiveFunctor n)).ι.app j ≫
      piNPositiveComparison n c = (piNPositiveFunctor n).map (c.ι.app j) :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ piNPositiveFunctor n)).fac
    ((piNPositiveFunctor n).mapCocone c) j

/--
The entire group-comparison function at each genuine quotient representative is piNMap.
-/
theorem piNPositiveComparison_apply (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (j : ℕ) (a : piN (n + 1) (F.obj j)) :
    (piNPositiveComparison n c).hom
      (GrpCat.FilteredColimits.G.mk (F ⋙ piNPositiveFunctor n) ⟨j, a⟩) =
        piNMap (n + 1) (c.ι.app j) a :=
  (ConcreteCategory.congr_hom (piNPositiveComparison_ι n c j) a).trans
    (piNPositiveMap_apply n (c.ι.app j) a)

/--
Original actual compact representatives make the genuine group-comparison function surjective.
-/
theorem piNPositiveComparison_surjective (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    Function.Surjective (piNPositiveComparison n c).hom := by
  intro a
  obtain ⟨j, b, hb⟩ := piN_stage_exists (n + 1) c hc hF a
  exact ⟨GrpCat.FilteredColimits.G.mk (F ⋙ piNPositiveFunctor n) ⟨j, b⟩,
    (piNPositiveComparison_apply n c j b).trans hb⟩

/-- Whole compact relative homotopies make the group comparison injective. -/
theorem piNPositiveComparison_injective (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    Function.Injective (piNPositiveComparison n c).hom := by
  intro x y hxy
  obtain ⟨i, a, rfl⟩ :=
    ((F ⋙ piNPositiveFunctor n) ⋙ forget GrpCat).ιColimitType_jointly_surjective x
  obtain ⟨j, b, rfl⟩ :=
    ((F ⋙ piNPositiveFunctor n) ⋙ forget GrpCat).ιColimitType_jointly_surjective y
  have hab : piNMap (n + 1) (c.ι.app i) a = piNMap (n + 1) (c.ι.app j) b :=
    (piNPositiveComparison_apply n c i a).symm.trans
      (hxy.trans (piNPositiveComparison_apply n c j b))
  obtain ⟨k, f, g, hfg⟩ := piN_eventual_eq (n + 1) c hc hF i j a b hab
  have hGroup : ((F ⋙ piNPositiveFunctor n).map f).hom a =
      ((F ⋙ piNPositiveFunctor n).map g).hom b :=
    (piNPositiveMap_apply n (F.map f) a).trans
      (hfg.trans (piNPositiveMap_apply n (F.map g) b).symm)
  exact GrpCat.FilteredColimits.G.mk_eq (F ⋙ piNPositiveFunctor n) ⟨i, a⟩ ⟨j, b⟩
    ⟨k, f, g, hGroup⟩

/-- Both genuine multiplicative comparison maps use the same actual group quotient. -/
def piNPositiveComparisonIso (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    GrpCat.FilteredColimits.colimit (F ⋙ piNPositiveFunctor n) ≅
      (piNPositiveFunctor n).obj c.pt :=
  (MulEquiv.ofBijective (piNPositiveComparison n c).hom
    ⟨piNPositiveComparison_injective n c hc hF,
      piNPositiveComparison_surjective n c hc hF⟩).toGrpIso

/-- The full positive-Iso hom function is the group-comparison map. -/
theorem piNPositiveComparisonIso_hom (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    (piNPositiveComparisonIso n c hc hF).hom = piNPositiveComparison n c := by
  apply GrpCat.hom_ext
  ext a
  rfl

/-- Every whole positive stage map is preserved by the inverse group comparison. -/
theorem piNPositiveComparisonIso_inv_ι (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (j : ℕ) :
    (piNPositiveFunctor n).map (c.ι.app j) ≫ (piNPositiveComparisonIso n c hc hF).inv =
      (GrpCat.FilteredColimits.colimitCocone (F ⋙ piNPositiveFunctor n)).ι.app j := by
  apply (cancel_mono (piNPositiveComparisonIso n c hc hF).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, piNPositiveComparisonIso_hom]
  exact (piNPositiveComparison_ι n c j).symm

/-- The complete actual positive-group cocone is colimiting for the closed Nat diagram. -/
def piNPositiveIsColimit (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    IsColimit ((piNPositiveFunctor n).mapCocone c) := by
  apply IsColimit.ofIsoColimit
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ piNPositiveFunctor n))
  refine Cocone.ext (piNPositiveComparisonIso n c hc hF) (fun j => ?_)
  rw [piNPositiveComparisonIso_hom]
  exact piNPositiveComparison_ι n c j

/-- The actual whole group comparison preserves every pointed cocone-map square. -/
theorem piNPositiveComparison_naturality (n : ℕ) {F G : ℕ ⥤ PointedCGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    GrpCat.FilteredColimits.colimitMap (Functor.whiskerRight a (piNPositiveFunctor n)) ≫
      piNPositiveComparison n d = piNPositiveComparison n c ≫ (piNPositiveFunctor n).map g := by
  apply GrpCat.FilteredColimits.closedSequential_desc_map_naturality
  intro j
  exact ((piNPositiveFunctor n).map_comp _ _).symm.trans
    (((piNPositiveFunctor n).congr_map (hg j)).trans ((piNPositiveFunctor n).map_comp _ _))

/-- The complete positive comparison Iso is natural in every whole pointed cocone map. -/
theorem piNPositiveComparisonIso_naturality (n : ℕ) {F G : ℕ ⥤ PointedCGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (G.map f).right))
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    GrpCat.FilteredColimits.colimitMap (Functor.whiskerRight a (piNPositiveFunctor n)) ≫
      (piNPositiveComparisonIso n d hd hG).hom =
        (piNPositiveComparisonIso n c hc hF).hom ≫ (piNPositiveFunctor n).map g := by
  rw [piNPositiveComparisonIso_hom, piNPositiveComparisonIso_hom]
  exact piNPositiveComparison_naturality n c d a g hg


/-- A homotopy class has a representative after any prescribed stage. -/
theorem piN_later_stage_exists (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (a : piN n c.pt) (j₀ : ℕ) :
    ∃ (j : ℕ), j₀ ≤ j ∧ ∃ (b : piN n (F.obj j)), piNMap n (c.ι.app j) b = a := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨j, hj, q, hq⟩ := cube_stage_factor n c hc hF p j₀
  exact ⟨j, hj, HomotopyGroup.mk q, (piNMap_mk n (c.ι.app j) q).trans
    (congrArg HomotopyGroup.mk hq)⟩

/-- The forward Type comparison is the actual homotopy map at every stage element. -/
theorem piNComparisonIso_hom_apply (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (j : ℕ)
    (a : piN n (F.obj j)) :
    (piNComparisonIso n c hc hF).hom (colimit.ι (F ⋙ piNFunctor n) j a) =
      piNMap n (c.ι.app j) a :=
  ConcreteCategory.congr_hom (piNComparisonIso_hom_ι n c hc hF j) a

/-- The inverse Type comparison returns the actual chosen colimit stage element. -/
theorem piNComparisonIso_inv_apply (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (j : ℕ)
    (a : piN n (F.obj j)) :
    (piNComparisonIso n c hc hF).inv (piNMap n (c.ι.app j) a) =
      colimit.ι (F ⋙ piNFunctor n) j a :=
  ConcreteCategory.congr_hom (piNComparisonIso_inv_ι n c hc hF j) a

/-- The inverse Type comparison is natural for every map of native cocones. -/
theorem piNComparisonIso_inv_naturality (n : ℕ) {F G : ℕ ⥤ PointedCGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (G.map f).right))
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    (piNFunctor n).map g ≫ (piNComparisonIso n d hd hG).inv =
      (piNComparisonIso n c hc hF).inv ≫ colim.map (Functor.whiskerRight a (piNFunctor n)) := by
  exact CategoryTheory.closedSequential_inverse_naturality
    (piNComparisonIso n c hc hF) (piNComparisonIso n d hd hG)
    (colim.map (Functor.whiskerRight a (piNFunctor n))) ((piNFunctor n).map g)
    (piNComparisonIso_naturality n c d hc hd hF hG a g hg)

/-- The inverse positive comparison returns every actual filtered group representative. -/
theorem piNPositiveComparisonIso_inv_apply (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}}
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (j : ℕ)
    (a : piN (n + 1) (F.obj j)) :
    (piNPositiveComparisonIso n c hc hF).inv.hom (piNMap (n + 1) (c.ι.app j) a) =
      GrpCat.FilteredColimits.G.mk (F ⋙ piNPositiveFunctor n) ⟨j, a⟩ := by
  have h := ConcreteCategory.congr_hom (piNPositiveComparisonIso_inv_ι n c hc hF j) a
  change (piNPositiveComparisonIso n c hc hF).inv.hom
    ((piNPositiveMap n (c.ι.app j)).hom a) = _ at h
  rw [piNPositiveMap_apply] at h
  exact h

/-- The complete inverse positive comparison retains arbitrary cocone-map naturality. -/
theorem piNPositiveComparisonIso_inv_naturality (n : ℕ) {F G : ℕ ⥤ PointedCGWH.{u, v}}
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (G.map f).right))
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    (piNPositiveFunctor n).map g ≫ (piNPositiveComparisonIso n d hd hG).inv =
      (piNPositiveComparisonIso n c hc hF).inv ≫
        GrpCat.FilteredColimits.colimitMap (Functor.whiskerRight a (piNPositiveFunctor n)) := by
  exact CategoryTheory.closedSequential_inverse_naturality
    (piNPositiveComparisonIso n c hc hF) (piNPositiveComparisonIso n d hd hG)
    (GrpCat.FilteredColimits.colimitMap (Functor.whiskerRight a (piNPositiveFunctor n)))
    ((piNPositiveFunctor n).map g)
    (piNPositiveComparisonIso_naturality n c d hc hd hF hG a g hg)

end PointedCGWH.SequentialHomotopyColimit
