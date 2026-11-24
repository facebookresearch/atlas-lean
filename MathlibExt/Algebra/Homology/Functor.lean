/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology comparison for a functor preserving homology

We provide the homological-complex wrapper around the short-complex
`mapHomologyIso`. For a functor `F` preserving zero morphisms and
homology, the homology in degree `i` after applying `F` to a complex
is naturally isomorphic to `F` applied to the homology in degree `i`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  {ι : Type*} {c : ComplexShape ι}

/-- The natural isomorphism comparing homology before and after applying
a functor which preserves zero morphisms and homology.

Its component at a complex `K` is `ShortComplex.mapHomologyIso` for
`K.sc i`. Naturality follows from the naturality theorem for that
short-complex isomorphism applied to the degree-`i` short-complex map. -/
noncomputable def mapHomologyFunctorIso (i : ι) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesHomology] :
    F.mapHomologicalComplex c ⋙ homologyFunctor D c i ≅
      homologyFunctor C c i ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc i).mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor C c i).map f) F)

end HomologicalComplex

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

/-- The inverse homology comparisons form a commuting square with a natural
transformation. Only preservation of homology of this short complex is needed. -/
@[reassoc]
lemma NatTrans.app_homology_comp_mapHomologyIso_inv
    {F G : C ⥤ D} (τ : F ⟶ G) (S : ShortComplex C) [S.HasHomology]
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [G.PreservesRightHomologyOf S] :
    τ.app S.homology ≫ (S.mapHomologyIso G).inv =
      (S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap (S.mapNatTrans τ) := by
  rw [NatTrans.app_homology]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The forward homology comparisons form the corresponding commuting square. -/
@[reassoc]
lemma NatTrans.mapHomologyIso_hom_comp_app_homology
    {F G : C ⥤ D} (τ : F ⟶ G) (S : ShortComplex C) [S.HasHomology]
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [G.PreservesRightHomologyOf S] :
    (S.mapHomologyIso F).hom ≫ τ.app S.homology =
      ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom := by
  rw [NatTrans.app_homology, Iso.hom_inv_id_assoc]

end CategoryTheory


/-! ## Cycle-class projection compatibility

The compatibility below is new formalization by @toskua and Avocado.
-/

section CycleClassProjection

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ShortComplex

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A functor preserving left homology carries the canonical cycle-class projection
to the original projection through its canonical cycle and homology comparisons. -/
theorem homologyπ_comp_mapHomologyIso_hom
    (S : ShortComplex C) [S.HasHomology] (U : C ⥤ D) [U.PreservesZeroMorphisms]
    [(S.map U).HasHomology] [U.PreservesLeftHomologyOf S] :
    (S.map U).homologyπ ≫ (S.mapHomologyIso U).hom =
      (S.mapCyclesIso U).hom ≫ U.map S.homologyπ := by
  let h := S.homologyData.left
  have hHom : (S.mapHomologyIso U).hom =
      (h.map U).homologyIso.hom ≫ U.map h.homologyIso.inv :=
    congrArg (fun e : (S.map U).homology ≅ U.obj S.homology => e.hom)
      (h.mapHomologyIso_eq U)
  have hCycles : (S.mapCyclesIso U).hom =
      (h.map U).cyclesIso.hom ≫ U.map h.cyclesIso.inv :=
    congrArg (fun e : (S.map U).cycles ≅ U.obj S.cycles => e.hom)
      (h.mapCyclesIso_eq U)
  have hProjection : (S.map U).homologyπ ≫ (h.map U).homologyIso.hom =
      (h.map U).cyclesIso.hom ≫ U.map h.π :=
    (h.map U).homologyπ_comp_homologyIso_hom
  calc
    (S.map U).homologyπ ≫ (S.mapHomologyIso U).hom =
        (S.map U).homologyπ ≫ (h.map U).homologyIso.hom ≫
          U.map h.homologyIso.inv :=
      congrArg (fun k : (S.map U).homology ⟶ U.obj S.homology =>
        (S.map U).homologyπ ≫ k) hHom
    _ = ((S.map U).homologyπ ≫ (h.map U).homologyIso.hom) ≫
        U.map h.homologyIso.inv := (Category.assoc _ _ _).symm
    _ = ((h.map U).cyclesIso.hom ≫ U.map h.π) ≫ U.map h.homologyIso.inv :=
      congrArg (fun k : (S.map U).cycles ⟶ U.obj h.H =>
        k ≫ U.map h.homologyIso.inv) hProjection
    _ = (h.map U).cyclesIso.hom ≫ U.map (h.π ≫ h.homologyIso.inv) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k : U.obj h.K ⟶ U.obj S.homology =>
          (h.map U).cyclesIso.hom ≫ k) (U.map_comp _ _).symm)
    _ = (h.map U).cyclesIso.hom ≫ U.map (h.cyclesIso.inv ≫ S.homologyπ) :=
      congrArg (fun k : h.K ⟶ S.homology => (h.map U).cyclesIso.hom ≫ U.map k)
        h.π_comp_homologyIso_inv
    _ = ((h.map U).cyclesIso.hom ≫ U.map h.cyclesIso.inv) ≫ U.map S.homologyπ :=
      (congrArg (fun k : U.obj h.K ⟶ U.obj S.homology =>
        (h.map U).cyclesIso.hom ≫ k) (U.map_comp _ _)).trans
          (Category.assoc _ _ _).symm
    _ = (S.mapCyclesIso U).hom ≫ U.map S.homologyπ :=
      congrArg (fun k : (S.map U).cycles ⟶ U.obj S.cycles => k ≫ U.map S.homologyπ)
        hCycles.symm

end CategoryTheory.ShortComplex

end CycleClassProjection


/-! ## Naturality under canonical boundary comparisons -/

section ConjugatedBoundary
universe uB vB
namespace CategoryTheory

/-- Transport a boundary naturality square through the actual comparison
isomorphisms. This is the original categorical argument previously internal to
`DiscreteCoefficientLongExact`; coefficient and degree models are unchanged. -/
theorem conjugatedBoundary_naturality
    {C : Type uB} [Category.{vB} C]
    {M₁ M₃ N₁ N₃ M₁' M₃' N₁' N₃' : C}
    (eM₁ : M₁ ≅ M₁') (eM₃ : M₃ ≅ M₃')
    (eN₁ : N₁ ≅ N₁') (eN₃ : N₃ ≅ N₃')
    (a : M₁ ⟶ N₁) (b : M₃ ⟶ N₃)
    (a' : M₁' ⟶ N₁') (b' : M₃' ⟶ N₃')
    (δ : M₃' ⟶ M₁') (δ' : N₃' ⟶ N₁')
    (h₁ : eM₁.inv ≫ a = a' ≫ eN₁.inv)
    (h₃ : b ≫ eN₃.hom = eM₃.hom ≫ b')
    (hδ : δ ≫ a' = b' ≫ δ') :
    (eM₃.hom ≫ δ ≫ eM₁.inv) ≫ a = b ≫ (eN₃.hom ≫ δ' ≫ eN₁.inv) := by
  calc
    _ = eM₃.hom ≫ δ ≫ (eM₁.inv ≫ a) := by simp only [Category.assoc]
    _ = eM₃.hom ≫ δ ≫ (a' ≫ eN₁.inv) :=
      congrArg (fun h => eM₃.hom ≫ δ ≫ h) h₁
    _ = eM₃.hom ≫ (δ ≫ a') ≫ eN₁.inv := by simp only [Category.assoc]
    _ = eM₃.hom ≫ (b' ≫ δ') ≫ eN₁.inv :=
      congrArg (fun h => eM₃.hom ≫ h ≫ eN₁.inv) hδ
    _ = (eM₃.hom ≫ b') ≫ δ' ≫ eN₁.inv := by simp only [Category.assoc]
    _ = (b ≫ eN₃.hom) ≫ δ' ≫ eN₁.inv :=
      congrArg (fun h => h ≫ δ' ≫ eN₁.inv) h₃.symm
    _ = _ := by simp only [Category.assoc]

end CategoryTheory
end ConjugatedBoundary

namespace HomologicalComplex

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  {ι : Type*} {c : ComplexShape ι}

/-- The canonical homology comparison is natural in a functor transformation. -/
theorem mapHomologyFunctorIso_naturality_transformation
    (A : HomologicalComplex C c) (i : ι) (F G : C ⥤ D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] (τ : F ⟶ G) :
    let H := homologyFunctor D c i
    H.map ((τ.mapHomologicalComplex c).app A) ≫ (mapHomologyFunctorIso i G).hom.app A =
      (mapHomologyFunctorIso i F).hom.app A ≫ τ.app ((homologyFunctor C c i).obj A) := by
  change ShortComplex.homologyMap ((A.sc i).mapNatTrans τ) ≫ ((A.sc i).mapHomologyIso G).hom =
    ((A.sc i).mapHomologyIso F).hom ≫ τ.app ((A.sc i).homology)
  exact (NatTrans.mapHomologyIso_hom_comp_app_homology τ (A.sc i)).symm

/-- A commuting square of actual complexes induces the composed canonical homology square. -/
theorem mapHomologyIso_composed_naturality
    (A : HomologicalComplex C c) (i : ι) (F G : C ⥤ D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] (τ : F ⟶ G)
    {B B' : HomologicalComplex D c}
    (e : B ≅ (F.mapHomologicalComplex c).obj A)
    (e' : B' ≅ (G.mapHomologicalComplex c).obj A)
    (d : B ⟶ B') {N : C} (E : (homologyFunctor C c i).obj A ≅ N)
    (hd : d ≫ e'.hom = e.hom ≫ (τ.mapHomologicalComplex c).app A) :
    let H := homologyFunctor D c i
    H.map d ≫ (H.mapIso e' ≪≫ (mapHomologyFunctorIso i G).app A ≪≫ G.mapIso E).hom =
      (H.mapIso e ≪≫ (mapHomologyFunctorIso i F).app A ≪≫ F.mapIso E).hom ≫ τ.app N := by
  let H := homologyFunctor D c i
  let T := (τ.mapHomologicalComplex c).app A
  have hrow : H.map d ≫ H.map e'.hom = H.map e.hom ≫ H.map T := by
    simpa only [Functor.map_comp] using congrArg (fun f => H.map f) hd
  have hmap := mapHomologyFunctorIso_naturality_transformation A i F G τ
  change H.map d ≫ (H.map e'.hom ≫ ((mapHomologyFunctorIso i G).app A).hom ≫ G.map E.hom) =
    (H.map e.hom ≫ ((mapHomologyFunctorIso i F).app A).hom ≫ F.map E.hom) ≫ τ.app N
  calc
    _ = (H.map e.hom ≫ H.map T) ≫ ((mapHomologyFunctorIso i G).app A).hom ≫ G.map E.hom := by
      rw [← Category.assoc, hrow]
    _ = (H.map e.hom ≫ (H.map T ≫ ((mapHomologyFunctorIso i G).app A).hom)) ≫ G.map E.hom := by
      simp only [Category.assoc]
    _ = (H.map e.hom ≫ (((mapHomologyFunctorIso i F).app A).hom ≫
        τ.app ((homologyFunctor C c i).obj A))) ≫ G.map E.hom :=
      congrArg (fun z => (H.map e.hom ≫ z) ≫ G.map E.hom) hmap
    _ = H.map e.hom ≫ ((mapHomologyFunctorIso i F).app A).hom ≫ F.map E.hom ≫ τ.app N := by
      simp only [Category.assoc]
      rw [← τ.naturality E.hom]
    _ = _ := by simp only [Category.assoc]

end HomologicalComplex
