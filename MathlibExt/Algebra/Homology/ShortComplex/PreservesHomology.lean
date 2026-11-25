/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology comparisons for composite functors

For functors preserving the specified homology, the homology
comparison of their composite is the composite of their comparisons.
Only the relevant homology objects and preservation of left homology
are required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
  {E : Type u₃} [Category.{v₃} E] [HasZeroMorphisms E]

namespace ShortComplex.LeftHomologyData

/-- Preservation of the kernel and cokernel in a left homology data
is stable under composition. -/
theorem isPreservedBy_comp {S : ShortComplex C} (h : S.LeftHomologyData)
    (F : C ⥤ D) (G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [h.IsPreservedBy F] [(h.map F).IsPreservedBy G] :
    h.IsPreservedBy (F ⋙ G) where
  g := by
    let : PreservesLimit (parallelPair S.g 0) F := IsPreservedBy.hg h F
    let : PreservesLimit (parallelPair (F.map S.g) 0) G :=
      IsPreservedBy.hg (h.map F) G
    let c : KernelFork S.g := KernelFork.ofι h.i h.wi
    have hcF : IsLimit (c.map F) := KernelFork.mapIsLimit c h.hi F
    have hcG : IsLimit ((c.map F).map G) := KernelFork.mapIsLimit (c.map F) hcF G
    exact preservesLimit_of_preserves_limit_cone h.hi
      ((KernelFork.isLimitMapConeEquiv c (F ⋙ G)).symm hcG)
  f' := by
    let : PreservesColimit (parallelPair h.f' 0) F := IsPreservedBy.hf' h F
    have hG : PreservesColimit (parallelPair (h.map F).f' 0) G :=
      IsPreservedBy.hf' (h.map F) G
    rw [map_f'] at hG
    let : PreservesColimit (parallelPair (F.map h.f') 0) G := hG
    let c : CokernelCofork h.f' := CokernelCofork.ofπ h.π h.f'_π
    have hcF : IsColimit (c.map F) := CokernelCofork.mapIsColimit c h.hπ' F
    have hcG : IsColimit ((c.map F).map G) :=
      CokernelCofork.mapIsColimit (c.map F) hcF G
    exact preservesColimit_of_preserves_colimit_cocone h.hπ'
      ((CokernelCofork.isColimitMapCoconeEquiv c (F ⋙ G)).symm hcG)

end ShortComplex.LeftHomologyData

/-- Composite preservation follows from preservation of the short complex and its image,
without a global exactness assumption. -/
instance (priority := 100) Functor.preservesLeftHomologyOf_comp
    (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)] :
    (F ⋙ G).PreservesLeftHomologyOf S where
  isPreservedBy h := h.isPreservedBy_comp F G

namespace ShortComplex

section Composition

private theorem map_comp_hasHomology (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [h : ((S.map F).map G).HasHomology] : (S.map (F ⋙ G)).HasHomology := by
  rw [ShortComplex.map_comp]
  exact h

-- The two mapped data have the same actual objects G(F(K)) and G(F(H)).

/-- The native comparison for a composite functor equals the two native
comparisons in their actual order. The homology assumptions are individual. -/
theorem mapHomologyIso_comp (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [S.HasHomology] [(S.map F).HasHomology] [((S.map F).map G).HasHomology]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)] :
    letI : (S.map (F ⋙ G)).HasHomology := by
      rw [ShortComplex.map_comp]
      infer_instance
    S.mapHomologyIso (F ⋙ G) =
      ((S.map F).mapHomologyIso G) ≪≫ G.mapIso (S.mapHomologyIso F) := by
  let : (S.map (F ⋙ G)).HasHomology := map_comp_hasHomology S F G
  let h := S.homologyData.left
  let hFG : ((S.map F).map G).LeftHomologyData := h.map (F ⋙ G)
  let hGF : ((S.map F).map G).LeftHomologyData := (h.map F).map G
  let γ : LeftHomologyMapData (𝟙 ((S.map F).map G)) hFG hGF :=
    { φK := 𝟙 (G.obj (F.obj h.K))
      φH := 𝟙 (G.obj (F.obj h.H))
      commi := by
        change (𝟙 _) ≫ G.map (F.map h.i) = G.map (F.map h.i) ≫ (𝟙 _)
        rw [Category.id_comp, Category.comp_id]
      commf' := by
        have hfFG : (h.map (F ⋙ G)).f' = G.map (F.map h.f') :=
          h.map_f' (F ⋙ G)
        have hfGF : ((h.map F).map G).f' = G.map (F.map h.f') :=
          ((h.map F).map_f' G).trans
            (congrArg (fun f : F.obj S.X₁ ⟶ F.obj h.K => G.map f) (h.map_f' F))
        exact (Category.comp_id _).trans
          (hfFG.trans (hfGF.symm.trans (Category.id_comp _).symm))
      commπ := by
        change G.map (F.map h.π) ≫ (𝟙 _) = (𝟙 _) ≫ G.map (F.map h.π)
        rw [Category.comp_id, Category.id_comp] }
  have hdata : hFG.homologyIso.hom = hGF.homologyIso.hom := by
    have hh := γ.homologyMap_comm
    have hcomm : hFG.homologyIso.hom ≫ 𝟙 (G.obj (F.obj h.H)) =
        hGF.homologyIso.hom := by
      simpa only [γ, homologyMap_id, Category.id_comp] using hh.symm
    exact (Category.comp_id hFG.homologyIso.hom).symm.trans hcomm
  have hFG' : (S.mapHomologyIso (F ⋙ G)).hom =
      hFG.homologyIso.hom ≫ G.map (F.map h.homologyIso.inv) := by
    have hh := congrArg Iso.hom (h.mapHomologyIso_eq (F ⋙ G))
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.comp_map] using hh
  have hF' : (S.mapHomologyIso F).hom =
      (h.map F).homologyIso.hom ≫ F.map h.homologyIso.inv :=
    congrArg Iso.hom (h.mapHomologyIso_eq F)
  have hG : ((S.map F).mapHomologyIso G).hom =
      hGF.homologyIso.hom ≫ G.map (h.map F).homologyIso.inv := by
    have hh := congrArg
      (fun e : ((S.map F).map G).homology ≅ G.obj (S.map F).homology => e.hom)
      ((h.map F).mapHomologyIso_eq G)
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] using hh
  have hunit : G.map (h.map F).homologyIso.inv ≫ G.map (h.map F).homologyIso.hom =
      𝟙 (G.obj (F.obj h.H)) :=
    (G.mapIso (h.map F).homologyIso).inv_hom_id
  apply Iso.ext
  calc
    (S.mapHomologyIso (F ⋙ G)).hom =
        hFG.homologyIso.hom ≫ G.map (F.map h.homologyIso.inv) := hFG'
    _ = hGF.homologyIso.hom ≫ G.map (F.map h.homologyIso.inv) :=
      congrArg (fun f => f ≫ G.map (F.map h.homologyIso.inv)) hdata
    _ = ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
      rw [hG, hF', G.map_comp]
      symm
      calc
        (hGF.homologyIso.hom ≫ G.map (h.map F).homologyIso.inv) ≫
            (G.map (h.map F).homologyIso.hom ≫ G.map (F.map h.homologyIso.inv)) =
            hGF.homologyIso.hom ≫ (G.map (h.map F).homologyIso.inv ≫
              (G.map (h.map F).homologyIso.hom ≫ G.map (F.map h.homologyIso.inv))) :=
          Category.assoc _ _ _
        _ = hGF.homologyIso.hom ≫ ((G.map (h.map F).homologyIso.inv ≫
            G.map (h.map F).homologyIso.hom) ≫ G.map (F.map h.homologyIso.inv)) :=
          congrArg (fun f => hGF.homologyIso.hom ≫ f) (Category.assoc _ _ _).symm
        _ = hGF.homologyIso.hom ≫ (𝟙 _ ≫ G.map (F.map h.homologyIso.inv)) :=
          congrArg (fun f => hGF.homologyIso.hom ≫ (f ≫ G.map (F.map h.homologyIso.inv))) hunit
        _ = hGF.homologyIso.hom ≫ G.map (F.map h.homologyIso.inv) :=
          congrArg (fun f => hGF.homologyIso.hom ≫ f) (Category.id_comp _)

/-- The forward composite comparison, with its actual ordered maps exposed. -/
@[reassoc]
theorem mapHomologyIso_comp_hom (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [S.HasHomology] [(S.map F).HasHomology] [((S.map F).map G).HasHomology]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)] :
    letI : (S.map (F ⋙ G)).HasHomology := by
      rw [ShortComplex.map_comp]
      infer_instance
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  let : (S.map (F ⋙ G)).HasHomology := map_comp_hasHomology S F G
  exact congrArg Iso.hom (mapHomologyIso_comp S F G)

/-- The inverse composite comparison reverses the two comparison maps. -/
@[reassoc]
theorem mapHomologyIso_comp_inv (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [S.HasHomology] [(S.map F).HasHomology] [((S.map F).map G).HasHomology]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)] :
    letI : (S.map (F ⋙ G)).HasHomology := by
      rw [ShortComplex.map_comp]
      infer_instance
    (S.mapHomologyIso (F ⋙ G)).inv =
      G.map (S.mapHomologyIso F).inv ≫ ((S.map F).mapHomologyIso G).inv := by
  let : (S.map (F ⋙ G)).HasHomology := map_comp_hasHomology S F G
  exact congrArg Iso.inv (mapHomologyIso_comp S F G)

end Composition

end ShortComplex

end CategoryTheory
