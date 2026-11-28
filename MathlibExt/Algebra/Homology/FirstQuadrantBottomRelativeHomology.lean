/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantAbutmentImage

/-!
# Homology relative to the zero bottom filtration stage

Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). At each complete
filtration cut i∈EInt, let G_i be the filtered total chain stage and F_i its cochain extension
with degree n placed at -n. The bottom stage F_⊥ is zero, and F_⊥→F_i→F_i is a split short exact
complex with identity second arrow.

The induced mapping-cone map g_i:Cone(F_⊥→F_i)→F_i is a quasi-isomorphism. It is natural under
every stage inclusion i≤j. Combining its cochain homology map with the homotopy-category
homology factorization and the chain/cochain reindexing identifies H^{-n}(⊥,i) with H_n(G_i) for
all n : ℕ. The comparison is natural in i, and the category's object and morphism universes are
arbitrary.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- For any EInt filtration cut i, horizontalBottomToStageMap i is the unique order morphism ⊥→i. -/
noncomputable abbrev horizontalBottomToStageMap (i : EInt) :
    (⊥ : EInt) ⟶ i := homOfLE bot_le

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For i∈EInt, horizontalBottomStageShortComplex is F_⊥→F_i→F_i, with first arrow
F(⊥→i) and second arrow id_{F_i}. The first arrow is zero because F_⊥=0. -/
noncomputable def horizontalBottomStageShortComplex (i : EInt) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    ((horizontalCompleteFiltrationCochainDiagram K).map
      (horizontalBottomToStageMap i))
    (𝟙 ((horizontalCompleteFiltrationCochainDiagram K).obj i)) (by
      have hbot := horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot K
      simpa using hbot.eq_of_src
        ((horizontalCompleteFiltrationCochainDiagram K).map
          (horizontalBottomToStageMap i)) 0)

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For every i∈EInt, the short complex F_⊥→F_i→F_i has a canonical splitting, using
the zero first object and the identity second arrow. -/
noncomputable def horizontalBottomStageShortComplexSplitting (i : EInt) :
    (horizontalBottomStageShortComplex K i).Splitting := by
  have hg : IsIso (horizontalBottomStageShortComplex K i).g := by
    dsimp [horizontalBottomStageShortComplex]
    infer_instance
  exact ShortComplex.Splitting.ofIsZeroOfIsIso _
    (horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot K)
    hg

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For each i∈EInt, the complex F_⊥→F_i→F_i is short exact in the category of
cochain complexes C^ℤ, by its zero-object splitting. -/
theorem horizontalBottomStageShortComplex_shortExact (i : EInt) :
    (horizontalBottomStageShortComplex K i).ShortExact :=
  (horizontalBottomStageShortComplexSplitting K i).shortExact

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For i∈EInt, the split short complex defines g_i:Cone(F_⊥→F_i)→F_i, the canonical
mapping-cone descent to the stage. -/
noncomputable def horizontalBottomMappingConeToStage (i : EInt) :
    CochainComplex.mappingCone
        ((horizontalCompleteFiltrationCochainDiagram K).map
          (horizontalBottomToStageMap i)) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj i :=
  CochainComplex.mappingCone.descShortComplex
    (horizontalBottomStageShortComplex K i)

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For every i∈EInt, g_i:Cone(F_⊥→F_i)→F_i is a quasi-isomorphism. The corresponding
short complex F_⊥→F_i→F_i is split short exact. -/
theorem horizontalBottomMappingConeToStage_quasiIso (i : EInt) :
    QuasiIso (horizontalBottomMappingConeToStage K i) := by
  exact CochainComplex.mappingCone.quasiIso_descShortComplex
    (horizontalBottomStageShortComplex_shortExact K i)

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For i≤j in EInt, the map between F_⊥→F_i→F_i and F_⊥→F_j→F_j has components
F(id_⊥), F(i→j) and F(i→j), respectively. -/
noncomputable def horizontalBottomStageShortComplexMap
    {i j : EInt} (h : i ≤ j) :
    horizontalBottomStageShortComplex K i ⟶
      horizontalBottomStageShortComplex K j where
  τ₁ := (horizontalCompleteFiltrationCochainDiagram K).map (𝟙 (⊥ : EInt))
  τ₂ := (horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h)
  τ₃ := (horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h)
  comm₁₂ := by
    dsimp [horizontalBottomStageShortComplex]
    rw [← (horizontalCompleteFiltrationCochainDiagram K).map_comp,
      ← (horizontalCompleteFiltrationCochainDiagram K).map_comp]
    apply (horizontalCompleteFiltrationCochainDiagram K).congr_map
    apply Subsingleton.elim
  comm₂₃ := by simp [horizontalBottomStageShortComplex]

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For i≤j, let M_{ij}:Cone(F_⊥→F_i)→Cone(F_⊥→F_j) be the induced cone map. Then
M_{ij}≫g_j=g_i≫F(i→j). -/
theorem horizontalBottomMappingConeToStage_naturality
    {i j : EInt} (h : i ≤ j) :
    (horizontalCompleteFiltrationMappingConeFunctor K).map
        (twoδ₂Toδ₁
          (horizontalBottomToStageMap i)
          (homOfLE h)
          (horizontalBottomToStageMap j)
          (Subsingleton.elim _ _)) ≫
      horizontalBottomMappingConeToStage K j =
    horizontalBottomMappingConeToStage K i ≫
      (horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h) := by
  exact CochainComplex.mappingCone.map_descShortComplex
    (horizontalBottomStageShortComplex K i)
    (horizontalBottomStageShortComplex K j)
    (horizontalBottomStageShortComplexMap K h)

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For i∈EInt and n : ℕ, the spectral-object relative cochain homology H^{-n}(⊥,i)
is canonically isomorphic to H_n(G_i). The map first identifies homotopy-category and cone
homology, then applies H^{-n}(g_i), and finally reindexes cochain degree -n to chain degree n. -/
noncomputable def horizontalBottomRelativeHomologyStageIso
    (i : EInt) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H (-(n : ℤ))).obj
        (mk₁ (horizontalBottomToStageMap i)) ≅
      (horizontalCompleteFilteredTotalComplex K i).homology n := by
  let M : CochainComplex C ℤ := CochainComplex.mappingCone
    ((horizontalCompleteFiltrationCochainDiagram K).map
      (horizontalBottomToStageMap i))
  let g : M ⟶ (horizontalCompleteFiltrationCochainDiagram K).obj i :=
    horizontalBottomMappingConeToStage K i
  letI : QuasiIso g := horizontalBottomMappingConeToStage_quasiIso K i
  simp only [horizontalCompleteFiltrationSpectralObject,
    CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_H]
  change ((HomotopyCategory.homologyFunctor C
      (ComplexShape.up ℤ) (-(n : ℤ))).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) ≅
    (horizontalCompleteFilteredTotalComplex K i).homology n
  let eCone : (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (-(n : ℤ))).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M) ≅ M.homology (-(n : ℤ)) :=
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (-(n : ℤ))).app M
  let eStage : M.homology (-(n : ℤ)) ≅
      ((horizontalCompleteFiltrationCochainDiagram K).obj i).homology (-(n : ℤ)) :=
    isoOfQuasiIsoAt g (-(n : ℤ))
  let eExtend : ((horizontalCompleteFiltrationCochainDiagram K).obj i).homology (-(n : ℤ)) ≅
      (horizontalCompleteFilteredTotalComplex K i).homology n :=
    (horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)
  exact eCone ≪≫ eStage ≪≫ eExtend

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For i∈EInt and n : ℕ, the forward map H^{-n}(⊥,i)→H_n(G_i) is the canonical
homotopy-homology factor isomorphism to H^{-n}(Cone(F_⊥→F_i)), followed by H^{-n}(g_i), then the
extension homology isomorphism H^{-n}(F_i)≅H_n(G_i). -/
theorem horizontalBottomRelativeHomologyStageIso_hom
    (i : EInt) (n : ℕ) :
    (horizontalBottomRelativeHomologyStageIso K i n).hom =
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
          (CochainComplex.mappingCone
            ((horizontalCompleteFiltrationCochainDiagram K).map
              (horizontalBottomToStageMap i))) ≫
        HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage K i) (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom := by
  simp [horizontalBottomRelativeHomologyStageIso, id]

/-- Let C be an abelian category in arbitrary universes and K a bicomplex of shape (down ℕ,down ℕ).
Let G_i be its complete filtered total chain stage and F_i its cochain extension along n↦-n, for
i∈EInt; F_⊥=0. For i≤j and n : ℕ, let H_{ij} be the relative spectral homology map and e_i,e_j
the bottom-relative/stage isomorphisms. Then H_{ij}≫e_j.hom=e_i.hom≫H_n(G_i→G_j), with relative
degree -n and chain degree n. -/
theorem horizontalBottomRelativeHomologyStageIso_naturality
    {i j : EInt} (h : i ≤ j) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H (-(n : ℤ))).map
        (twoδ₂Toδ₁
          (horizontalBottomToStageMap i)
          (homOfLE h)
          (horizontalBottomToStageMap j)
          (Subsingleton.elim _ _)) ≫
      (horizontalBottomRelativeHomologyStageIso K j n).hom =
    (horizontalBottomRelativeHomologyStageIso K i n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalMap K h) n := by
  rw [horizontalBottomRelativeHomologyStageIso_hom,
    horizontalBottomRelativeHomologyStageIso_hom]
  let Dᵢ : ComposableArrows EInt 1 := mk₁ (horizontalBottomToStageMap i)
  let Dⱼ : ComposableArrows EInt 1 := mk₁ (horizontalBottomToStageMap j)
  let α : Dᵢ ⟶ Dⱼ := twoδ₂Toδ₁
    (horizontalBottomToStageMap i) (homOfLE h) (horizontalBottomToStageMap j)
    (Subsingleton.elim _ _)
  let F : EInt ⥤ CochainComplex C ℤ := horizontalCompleteFiltrationCochainDiagram K
  let M : ComposableArrows EInt 1 ⥤ CochainComplex C ℤ :=
    horizontalCompleteFiltrationMappingConeFunctor K
  let Q : CochainComplex C ℤ ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
    HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let Hq : HomotopyCategory C (ComplexShape.up ℤ) ⥤ C :=
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (-(n : ℤ))
  let Hc : CochainComplex C ℤ ⥤ C :=
    HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-(n : ℤ))
  let η : Q ⋙ Hq ≅ Hc :=
    HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (-(n : ℤ))
  let m : M.obj Dᵢ ⟶ M.obj Dⱼ := M.map α
  let gᵢ : M.obj Dᵢ ⟶ F.obj i := horizontalBottomMappingConeToStage K i
  let gⱼ : M.obj Dⱼ ⟶ F.obj j := horizontalBottomMappingConeToStage K j
  let t : F.obj i ⟶ F.obj j := F.map (homOfLE h)
  let s : horizontalCompleteFilteredTotalComplex K i ⟶
      horizontalCompleteFilteredTotalComplex K j := horizontalCompleteFilteredTotalMap K h
  let aᵢ : (Q ⋙ Hq).obj (M.obj Dᵢ) ⟶ (M.obj Dᵢ).homology (-(n : ℤ)) :=
    η.hom.app (M.obj Dᵢ)
  let aⱼ : (Q ⋙ Hq).obj (M.obj Dⱼ) ⟶ (M.obj Dⱼ).homology (-(n : ℤ)) :=
    η.hom.app (M.obj Dⱼ)
  let eᵢ : (F.obj i).homology (-(n : ℤ)) ⟶
      (horizontalCompleteFilteredTotalComplex K i).homology n :=
    ((horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)).hom
  let eⱼ : (F.obj j).homology (-(n : ℤ)) ⟶
      (horizontalCompleteFilteredTotalComplex K j).homology n :=
    ((horizontalCompleteFilteredTotalComplex K j).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)).hom
  have hfac : (Q ⋙ Hq).map m ≫ aⱼ =
      aᵢ ≫ HomologicalComplex.homologyMap m (-(n : ℤ)) := by
    simpa only [aᵢ, aⱼ, Hc, Functor.comp_map,
      HomologicalComplex.homologyFunctor_obj,
      HomologicalComplex.homologyFunctor_map] using η.hom.naturality m
  have hdesc : m ≫ gⱼ = gᵢ ≫ t :=
    horizontalBottomMappingConeToStage_naturality K h
  have hdescH : HomologicalComplex.homologyMap m (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap gⱼ (-(n : ℤ)) =
      HomologicalComplex.homologyMap gᵢ (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap t (-(n : ℤ)) := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun f : M.obj Dᵢ ⟶ F.obj j =>
        HomologicalComplex.homologyMap f (-(n : ℤ))) hdesc
  have ht : t = HomologicalComplex.extendMap s ComplexShape.embeddingDownNat := rfl
  have hext : HomologicalComplex.homologyMap t (-(n : ℤ)) ≫ eⱼ =
      eᵢ ≫ HomologicalComplex.homologyMap s n := by
    rw [ht]
    exact HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := s) (e := ComplexShape.embeddingDownNat)
      (j := n) (j' := -(n : ℤ)) (by simp)
  simp only [horizontalCompleteFiltrationSpectralObject,
    CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_H]
  change (Q ⋙ Hq).map m ≫ aⱼ ≫
      HomologicalComplex.homologyMap gⱼ (-(n : ℤ)) ≫ eⱼ =
    (aᵢ ≫ HomologicalComplex.homologyMap gᵢ (-(n : ℤ)) ≫ eᵢ) ≫
      HomologicalComplex.homologyMap s n
  calc
    _ = aᵢ ≫ HomologicalComplex.homologyMap m (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap gⱼ (-(n : ℤ)) ≫ eⱼ := by
      simpa only [Category.assoc] using hfac =≫
        (HomologicalComplex.homologyMap gⱼ (-(n : ℤ)) ≫ eⱼ)
    _ = aᵢ ≫ HomologicalComplex.homologyMap gᵢ (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap t (-(n : ℤ)) ≫ eⱼ := by
      simpa only [Category.assoc] using (aᵢ ≫= hdescH) =≫ eⱼ
    _ = _ := by
      simpa only [Category.assoc] using
        (aᵢ ≫ HomologicalComplex.homologyMap gᵢ (-(n : ℤ))) ≫= hext

end HomologicalComplex₂
