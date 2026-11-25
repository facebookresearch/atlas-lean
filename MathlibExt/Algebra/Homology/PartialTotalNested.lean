/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalBasic
public import MathlibExt.Algebra.Homology.Embedding.StupidTruncNested

import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Maps between nested partial total complexes

Initial-segment inclusions in the first coordinate induce maps between the
corresponding partial total complexes. This file records the construction and
its action on retained bicomplex summands.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ComplexShape

/-- The support of a natural initial segment through `p` is contained in the
support of every initial segment through `p'` when `p ≤ p'`. -/
theorem embeddingDownNatInitialSegment_rangeLE
    {p p' : ℕ} (h : p ≤ p') :
    (embeddingDownNatInitialSegment p).RangeLE
      (embeddingDownNatInitialSegment p') := by
  rintro _ ⟨i, rfl⟩
  exact ⟨(downNatInitialSegmentEmbedding h).f i,
    downNatInitialSegmentEmbedding_f_embedding_f h i⟩

end ComplexShape

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The canonical map from a first-coordinate stupid truncation into a larger
first-coordinate stupid truncation. -/
noncomputable def firstStupidTruncMap {p p' : ℕ} (h : p ≤ p') :
    B.firstStupidTrunc p ⟶ B.firstStupidTrunc p' :=
  B.stupidTruncMapOfRangeLE
    (ComplexShape.embeddingDownNatInitialSegment p)
    (ComplexShape.embeddingDownNatInitialSegment p')
    (ComplexShape.embeddingDownNatInitialSegment_rangeLE h)

/-- The filtration map between partial total complexes induced by an inclusion
of first-coordinate initial segments. -/
noncomputable def partialTotalMap {p p' : ℕ} (h : p ≤ p') :
    B.partialTotal p ⟶ B.partialTotal p' :=
  HomologicalComplex₂.total.map (B.firstStupidTruncMap h)
    (ComplexShape.down ℕ)

/-- On a retained summand, the partial-total filtration map is the composite
of the two truncation coordinate isomorphisms followed by the target total
inclusion. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalMap {p p' : ℕ} (h : p ≤ p')
    (i : Fin (p + 1)) (j n : ℕ) (hn : i.1 + j = n) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i.1 j n hn ≫
        (B.partialTotalMap h).f n =
      ((B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p) rfl).hom.f j ≫
        (B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p')
          (ComplexShape.downNatInitialSegmentEmbedding_f_embedding_f
            h i)).inv.f j) ≫
        (B.firstStupidTrunc p').ιTotal
          (ComplexShape.down ℕ) i.1 j n hn := by
  change
    HomologicalComplex₂.ιTotal
          (B.stupidTrunc (ComplexShape.embeddingDownNatInitialSegment p))
          (ComplexShape.down ℕ) i.1 j n hn ≫
        (HomologicalComplex₂.total.map
          (B.stupidTruncMapOfRangeLE
            (ComplexShape.embeddingDownNatInitialSegment p)
            (ComplexShape.embeddingDownNatInitialSegment p')
            (ComplexShape.embeddingDownNatInitialSegment_rangeLE h))
          (ComplexShape.down ℕ)).f n =
      ((B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p) rfl).hom.f j ≫
        (B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p')
          (ComplexShape.downNatInitialSegmentEmbedding_f_embedding_f
            h i)).inv.f j) ≫
        HomologicalComplex₂.ιTotal
          (B.stupidTrunc
            (ComplexShape.embeddingDownNatInitialSegment p'))
          (ComplexShape.down ℕ) i.1 j n hn
  rw [HomologicalComplex₂.ιTotal_map]
  have hcomponent :
      (B.stupidTruncMapOfRangeLE
        (ComplexShape.embeddingDownNatInitialSegment p)
        (ComplexShape.embeddingDownNatInitialSegment p')
        (ComplexShape.embeddingDownNatInitialSegment_rangeLE h)).f i.1 =
      (B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p) rfl).hom ≫
        (B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p')
          (ComplexShape.downNatInitialSegmentEmbedding_f_embedding_f
            h i)).inv := by
    exact HomologicalComplex.stupidTruncMapOfRangeLE_f B
      (ComplexShape.embeddingDownNatInitialSegment p)
      (ComplexShape.embeddingDownNatInitialSegment p')
      (ComplexShape.embeddingDownNatInitialSegment_rangeLE h)
      (i₁ := i)
      (i₂ := (ComplexShape.downNatInitialSegmentEmbedding h).f i)
      (k := i.1) rfl
      (ComplexShape.downNatInitialSegmentEmbedding_f_embedding_f h i)
  rw [hcomponent, HomologicalComplex.comp_f]
  rfl

/-- A partial-total filtration map followed by the inclusion of its target
stage is the inclusion of its source stage. -/
@[reassoc (attr := simp)]
theorem partialTotalMap_comp_partialTotalι {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalMap h ≫ B.partialTotalι p' = B.partialTotalι p := by
  let ιp' : B.firstStupidTrunc p' ⟶ B := by
    exact B.ιStupidTrunc
      (ComplexShape.embeddingDownNatInitialSegment p')
  let ιp : B.firstStupidTrunc p ⟶ B := by
    exact B.ιStupidTrunc
      (ComplexShape.embeddingDownNatInitialSegment p)
  change
    HomologicalComplex₂.total.map (B.firstStupidTruncMap h)
          (ComplexShape.down ℕ) ≫
        HomologicalComplex₂.total.map ιp' (ComplexShape.down ℕ) =
      HomologicalComplex₂.total.map ιp
        (ComplexShape.down ℕ)
  have hfactor :
      B.firstStupidTruncMap h ≫ ιp' = ιp := by
    dsimp only [ιp', ιp]
    exact HomologicalComplex.stupidTruncMapOfRangeLE_ιStupidTrunc B
      (ComplexShape.embeddingDownNatInitialSegment p)
      (ComplexShape.embeddingDownNatInitialSegment p')
      (ComplexShape.embeddingDownNatInitialSegment_rangeLE h)
  rw [← HomologicalComplex₂.total.map_comp, hfactor]

/-- The partial-total filtration map from a stage to itself is the identity. -/
@[simp]
theorem partialTotalMap_refl (p : ℕ) :
    B.partialTotalMap (le_refl p) = 𝟙 _ := by
  apply (cancel_mono (B.partialTotalι p)).1
  rw [partialTotalMap_comp_partialTotalι, Category.id_comp]

/-- Partial-total filtration maps compose according to transitivity of the
stage inequalities. -/
@[reassoc]
theorem partialTotalMap_comp {p p' p'' : ℕ}
    (h : p ≤ p') (h' : p' ≤ p'') :
    B.partialTotalMap h ≫ B.partialTotalMap h' =
      B.partialTotalMap (h.trans h') := by
  apply (cancel_mono (B.partialTotalι p'')).1
  calc
    (B.partialTotalMap h ≫ B.partialTotalMap h') ≫
          B.partialTotalι p'' =
        B.partialTotalMap h ≫
          (B.partialTotalMap h' ≫ B.partialTotalι p'') :=
      Category.assoc _ _ _
    _ = B.partialTotalMap h ≫ B.partialTotalι p' := by
      rw [partialTotalMap_comp_partialTotalι]
    _ = B.partialTotalι p := partialTotalMap_comp_partialTotalι B h
    _ = B.partialTotalMap (h.trans h') ≫ B.partialTotalι p'' :=
      (partialTotalMap_comp_partialTotalι B (h.trans h')).symm

/-- The map on a partial-total stage induced by a morphism of bicomplexes. -/
noncomputable def partialTotalHom
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B') (p : ℕ) :
    B.partialTotal p ⟶ B'.partialTotal p :=
  HomologicalComplex₂.total.map
    (HomologicalComplex.stupidTruncMap φ
      (ComplexShape.embeddingDownNatInitialSegment p))
    (ComplexShape.down ℕ)

/-- On a retained summand, the stagewise map is induced by the corresponding
component of the stupid-truncation map. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalHom
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B') (p : ℕ)
    (i : Fin (p + 1)) (j n : ℕ) (hn : i.1 + j = n) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i.1 j n hn ≫
        (B.partialTotalHom φ p).f n =
      (((HomologicalComplex.stupidTruncMap φ
        (ComplexShape.embeddingDownNatInitialSegment p)).f i.1).f j) ≫
        (B'.firstStupidTrunc p).ιTotal
          (ComplexShape.down ℕ) i.1 j n hn := by
  change
    HomologicalComplex₂.ιTotal
          (B.stupidTrunc (ComplexShape.embeddingDownNatInitialSegment p))
          (ComplexShape.down ℕ) i.1 j n hn ≫
        (HomologicalComplex₂.total.map
          (HomologicalComplex.stupidTruncMap φ
            (ComplexShape.embeddingDownNatInitialSegment p))
          (ComplexShape.down ℕ)).f n = _
  exact HomologicalComplex₂.ιTotal_map
    (K := B.stupidTrunc
      (ComplexShape.embeddingDownNatInitialSegment p))
    (L := B'.stupidTrunc
      (ComplexShape.embeddingDownNatInitialSegment p))
    (φ := HomologicalComplex.stupidTruncMap φ
      (ComplexShape.embeddingDownNatInitialSegment p))
    (c₁₂ := ComplexShape.down ℕ) i.1 j n hn

/-- The stagewise map commutes with the inclusions into the full total
complexes. -/
@[reassoc (attr := simp)]
theorem partialTotalHom_ι_naturality
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B') (p : ℕ) :
    B.partialTotalHom φ p ≫ B'.partialTotalι p =
      B.partialTotalι p ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) := by
  let e := ComplexShape.embeddingDownNatInitialSegment p
  let φp : B.firstStupidTrunc p ⟶ B'.firstStupidTrunc p := by
    exact HomologicalComplex.stupidTruncMap φ e
  let ιB : B.firstStupidTrunc p ⟶ B := by
    exact B.ιStupidTrunc e
  let ιB' : B'.firstStupidTrunc p ⟶ B' := by
    exact B'.ιStupidTrunc e
  change
    HomologicalComplex₂.total.map φp (ComplexShape.down ℕ) ≫
        HomologicalComplex₂.total.map ιB' (ComplexShape.down ℕ) =
      HomologicalComplex₂.total.map ιB (ComplexShape.down ℕ) ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)
  have hφ : φp ≫ ιB' = ιB ≫ φ := by
    dsimp only [φp, ιB', ιB]
    exact HomologicalComplex.stupidTruncMap_ιStupidTrunc_naturality e φ
  rw [← HomologicalComplex₂.total.map_comp,
    ← HomologicalComplex₂.total.map_comp, hφ]

/-- The filtration maps are natural in morphisms of bicomplexes. -/
@[reassoc]
theorem partialTotalMap_naturality
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B')
    {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalHom φ p ≫ B'.partialTotalMap h =
      B.partialTotalMap h ≫ B.partialTotalHom φ p' := by
  apply (cancel_mono (B'.partialTotalι p')).1
  calc
    (B.partialTotalHom φ p ≫ B'.partialTotalMap h) ≫
          B'.partialTotalι p' =
        B.partialTotalHom φ p ≫
          (B'.partialTotalMap h ≫ B'.partialTotalι p') :=
      Category.assoc _ _ _
    _ = B.partialTotalHom φ p ≫ B'.partialTotalι p := by
      rw [partialTotalMap_comp_partialTotalι]
    _ = B.partialTotalι p ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) :=
      partialTotalHom_ι_naturality B φ p
    _ = (B.partialTotalMap h ≫ B.partialTotalι p') ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) := by
      rw [partialTotalMap_comp_partialTotalι]
    _ = B.partialTotalMap h ≫
        (B.partialTotalι p' ≫
          HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) :=
      Category.assoc _ _ _
    _ = B.partialTotalMap h ≫
        (B.partialTotalHom φ p' ≫ B'.partialTotalι p') := by
      rw [← partialTotalHom_ι_naturality]
    _ = (B.partialTotalMap h ≫ B.partialTotalHom φ p') ≫
        B'.partialTotalι p' := (Category.assoc _ _ _).symm

/-- Every degree of a partial-total filtration map is a monomorphism. -/
instance partialTotalMap_f_mono {p p' : ℕ} (h : p ≤ p') (n : ℕ) :
    Mono ((B.partialTotalMap h).f n) := by
  have hfac := congrArg (fun q => q.f n)
    (B.partialTotalMap_comp_partialTotalι h)
  rw [HomologicalComplex.comp_f] at hfac
  exact mono_of_mono_fac hfac

/-- A partial-total filtration map is a monomorphism of chain complexes. -/
instance partialTotalMap_mono {p p' : ℕ} (h : p ≤ p') :
    Mono (B.partialTotalMap h) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    B.partialTotalMap_f_mono h n

end HomologicalComplex₂

end
